; A tool to evaluate the proof-advice-generating models
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: change to HELP package

(include-book "replay-book-with-advice") ; todo: factour out common stuff
(include-book "replay-books-with-advice") ; todo: factour out common stuff: clear-keys-with-matching-prefixes
(include-book "advice")
(include-book "kestrel/utilities/split-path" :dir :system)
(include-book "kestrel/axe/merge-sort-less-than" :dir :system) ; todo: move
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;; TODO: removing :add-hyp gets us less the requested number of recs sometimes!

;;Returns (mv attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums total-recs-produced).
(defun tabulate-resuls-for-model (model result-alist attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums-acc total-recs-produced)
  (declare (xargs :mode :program)) ;todo
  (if (endp result-alist)
      (mv attempt-count successful-attempt-count top-1-count top-10-count
          (merge-sort-< successful-rec-nums-acc)
          total-recs-produced)
    (b* ((result-entry (first result-alist))
         (model-results (cdr result-entry))
         (this-model-result (assoc-eq model model-results)))
      (if (not this-model-result) ; maybe print a warning?
          (tabulate-resuls-for-model model (rest result-alist) attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums-acc total-recs-produced)
        (let* ((total-recs (second this-model-result))
               (first-working-rec-num-or-nil (third this-model-result)) ; todo: also tabulate the times
               (successp first-working-rec-num-or-nil)
               (top-1 (and successp (<= first-working-rec-num-or-nil 1)))
               (top-10 (and successp (<= first-working-rec-num-or-nil 10))) ; todo: what if we don't even ask for 10, or there are not 10, or :add-hyp gets removed?
               )
          (tabulate-resuls-for-model model (rest result-alist)
                                     (+ 1 attempt-count)
                                     (if successp (+ 1 successful-attempt-count) successful-attempt-count)
                                     (if top-1 (+ 1 top-1-count) top-1-count)
                                     (if top-10 (+ 1 top-10-count) top-10-count)
                                     (if successp
                                         (cons first-working-rec-num-or-nil successful-rec-nums-acc)
                                       successful-rec-nums-acc)
                                     (+ total-recs total-recs-produced)
                                     ))))))

;; todo: support rounding to hundredths
(defun quotient-to-percent-string (numerator denominator)
  (declare (xargs :guard (and (rationalp numerator)
                              (<= 0 numerator) ; todo gen
                              (rationalp denominator))
                  :mode :program ; todo
                  ))
  (if (= 0 denominator)
      (if (= 0 numerator)
          "undefined"
        (if (< numerator 0) "negative-infinity" "infinity"))
    (let* ((quotient (/ numerator denominator))
           (percent (* 100 quotient))
           (percent-int-part (floor percent 1))
           (rounded-percent (if (> percent (+ percent-int-part 1/2))
                                (+ 1 percent-int-part)
                              percent-int-part)))
      (nat-to-string rounded-percent))))

(defun show-model-evaluation (model result-alist)
  (declare (xargs :mode :program)) ;todo
  (b* (((mv attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums total-recs-produced)
        (tabulate-resuls-for-model model result-alist 0 0 0 0 nil 0))
       (- (cw "Results for model ~x0 (~x1 theorem attempts, ~x2 total recs produced):~%" model attempt-count total-recs-produced))
       (- (cw "Success: ~x0 (~s1%)~%" successful-attempt-count (quotient-to-percent-string successful-attempt-count attempt-count)))
       (- (cw "Nums of first successful recs: ~X01~%" successful-rec-nums nil)) ; todo: summarize better
       (- (cw "Top-1: ~x0 (~s1%)~%" top-1-count (quotient-to-percent-string top-1-count attempt-count)))
       (- (cw "Top-10: ~x0 (~s1%)~%~%" top-10-count (quotient-to-percent-string top-10-count attempt-count)))
       )
    nil))

;; RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
(defun show-model-evaluations (models result-alist)
  (declare (xargs :mode :program)) ;todo
  (if (endp models)
      nil
    (prog2$ (show-model-evaluation (first models) result-alist)
            (show-model-evaluations (rest models) result-alist))))

;;Returns (mv erp first-working-rec-or-nil state).
(defun try-recs-in-order (recs rec-num checkpoint-clauses theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit state)
  (declare (xargs :guard (and (help::recommendation-listp recs)
                              (posp rec-num)
                              (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit)))
                  :stobjs state
                  :mode :program))
  (if (endp recs)
      (prog2$ (and (acl2::print-level-at-least-tp print)
                   (cw "No working rec found.~%") ; todo: print the model name.
                   )
              (mv nil ; no error
                  nil ; no working rec found
                  state))
    (b* ((rec (first recs))
         ((mv erp maybe-successful-rec state)
          (help::try-recommendation rec
                                    current-book-absolute-path
                                    t ; avoid-current-bookp (since we are evaluating the rec, don't allow using the book it is in!)
                                    theorem-name ; may be :thm
                                    theorem-body
                                    theorem-hints
                                    theorem-otf-flg
                                    step-limit time-limit
                                    nil ; improve-recsp (just want to know if the rec works)
                                    print
                                    state))
         ((when erp) (mv erp nil state)))
      (if maybe-successful-rec
          (b* ((- (and (acl2::print-level-at-least-tp print)
                       (cw "Rec #~x0 worked.~%" rec-num) ; todo: print the model name.
                       ))
               (state (if (acl2::print-level-at-least-tp print)
                          (b* ((state (acl2::widen-margins state))
                               (- (help::show-successful-recommendation maybe-successful-rec))
                               (state (acl2::unwiden-margins state)))
                            state)
                        state)))
            (mv nil ; no-error
                rec-num
                state))
        ;; keep looking:
        (try-recs-in-order (rest recs) (+ 1 rec-num) checkpoint-clauses theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit state)))))


;; Walks through the RECOMMENDATION-ALIST, evaluating, for each model, how many recs must be tried to find one that works, and how long that takes.
;; Returns (mv erp model-results state), where each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
(defun eval-models-on-checkpoints-aux (recommendation-alist
                                       checkpoint-clauses
                                       theorem-name
                                       theorem-body
                                       theorem-hints
                                       theorem-otf-flg
                                       current-book-absolute-path
                                       print
                                       debug
                                       step-limit time-limit
                                       model-results-acc
                                       state)
  (declare (xargs :guard (and (alistp recommendation-alist) ; todo: strengthen
                              (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (true-listp model-results-acc))
                  :stobjs state
                  :mode :program))
  (if (endp recommendation-alist)
      (mv nil ; no error
          (reverse model-results-acc)
          state)
    (b* ((entry (first recommendation-alist))
         (model (car entry))
         (recs (cdr entry)) ; todo: these are ordered, right?
         ;; Maybe print the recommendations:
         (state (if (acl2::print-level-at-least-tp print)
                    (prog2$ (cw "~%RECOMMENDATIONS FOR ~x0:~%" model)
                            (help::show-recommendations recs state))
                  state))
         ((mv start-time state) (get-cpu-time state)) ; or we could use real time (here and below)
         ((mv erp first-working-rec-num-or-nil state)
          (try-recs-in-order recs 1 checkpoint-clauses theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit state))
         ((mv end-time state) (get-cpu-time state))
         ((when erp) (mv erp nil state)))
      (eval-models-on-checkpoints-aux (rest recommendation-alist)
                                      checkpoint-clauses
                                      theorem-name
                                      theorem-body
                                      theorem-hints
                                      theorem-otf-flg
                                      current-book-absolute-path
                                      print
                                      debug
                                      step-limit time-limit
                                      (cons (list model (len recs) first-working-rec-num-or-nil (help::round-to-hundredths (- end-time start-time)))
                                            model-results-acc)
                                      state))))

;; Returns (mv erp model-results state), where each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
(defun eval-models-on-checkpoints (checkpoint-clauses
                                   theorem-name
                                   theorem-body
                                   theorem-hints
                                   theorem-otf-flg
                                   num-recs-per-model
                                   current-book-absolute-path
                                   print
                                   server-url
                                   debug
                                   step-limit time-limit
                                   disallowed-rec-types ;todo: for this, handle the similar treatment of :use-lemma and :add-enable-hint?
                                   models
                                   state)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              ;; (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (help::rec-type-listp disallowed-rec-types)
                              (help::model-namesp models))
                  :stobjs state
                  :mode :program))
  (b* ( ;; Get the rec-lists for all the models:
       ((mv erp recommendation-alist state)
        (help::get-recs-from-models models num-recs-per-model disallowed-rec-types checkpoint-clauses theorem-body server-url debug print nil state))
       ((when erp) (mv erp nil state)))
    (eval-models-on-checkpoints-aux recommendation-alist
                                    checkpoint-clauses
                                    theorem-name
                                    theorem-body
                                    theorem-hints
                                    theorem-otf-flg
                                    current-book-absolute-path
                                    print
                                    debug
                                    step-limit time-limit
                                    nil
                                    state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Determines whether the Proof Advice tool can find advice for the given DEFTHM.  Either way, this also submits DEFTHM.
;; Returns (mv erp trivialp model-results state), where each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
(defun eval-models-and-submit-defthm-event (defthm num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models state)
  (declare (xargs :guard (and (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or (null server-url)
                                  (stringp server-url))
                              (help::model-namesp models))
                  :mode :program
                  :stobjs state))
  (b* (;; (defthm-variant (car defthm)) ; defthm or defthmd, etc.
       (theorem-name (cadr defthm))
       (theorem-body (caddr defthm))
       (theorem-otf-flg (cadr (assoc-keyword :otf-flg (cdddr defthm))))
       ;; (rule-classes-result (assoc-keyword :rule-classes (cdddr defthm)))
       ;; (rule-classes (if rule-classes-result
       ;;                   (cadr rule-classes-result)
       ;;                 ;; this really means don't put in any :rule-classes arg at all:
       ;;                 '(:rewrite)))
       ;; (hints-presentp (if (assoc-keyword :hints (cdddr defthm)) t nil))
       (- (cw "(ADVICE: ~x0: " theorem-name))
       ;; Ignores any given hints (for now):
       (theorem-hints nil)
       ((mv erp provedp & checkpoint-clauses state)
        (help::try-proof-and-get-checkpoint-clauses theorem-name
                                                    theorem-body
                                                    (acl2::translate-term theorem-body 'eval-models-and-submit-defthm-event (w state))
                                                    theorem-hints
                                                    theorem-otf-flg ; or use nil ?
                                                    step-limit time-limit
                                                    t ; suppress-trivial-warningp
                                                    state))
       ((when erp) (mv erp nil nil state)))
    (if provedp
        (b* ((- (cw "Trivial (no hints needed)).~%")) ;todo: print more, also tabulate these
             ((mv erp state) ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event-helper-core `(skip-proofs ,defthm) print state))
             ((when erp) (mv erp nil nil state)))
          (mv nil ; no error
              t   ; theorem was trivial (no hints needed)
              nil
              state))
      (b* (((mv erp model-results state)
            (eval-models-on-checkpoints checkpoint-clauses
                                        theorem-name
                                        theorem-body
                                        theorem-hints
                                        theorem-otf-flg
                                        num-recs-per-model
                                        current-book-absolute-path
                                        print
                                        server-url
                                        debug
                                        step-limit time-limit
                                        '(:add-hyp)
                                        models
                                        state))
           ((when erp) (mv erp nil nil state))
           ((mv erp state) ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
            (submit-event-helper-core `(skip-proofs ,defthm) print state))
           ((when erp) (mv erp nil nil state))
           (- (cw ")~%")) ; todo: print which model(s) worked
           )
        (mv nil ; no error
            nil ; not trivial
            model-results
            state)))))

;; Returns (mv erp result-alist state).
;throws an error if any event fails
(defun submit-events-and-eval-models (events theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models result-alist-acc state)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or (null server-url)
                                  (stringp server-url))
                              (help::model-namesp models)
                              (alistp result-alist-acc))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil ; no error
          result-alist-acc
          state)
    (let ((event (first events)))
      (if (advice-eventp event theorems-to-try)
          ;; It's a theorem for which we are to try advice:
          (b* ( ;; Try to prove it using advice:
               ((mv erp trivialp model-results state)
                (eval-models-and-submit-defthm-event event num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models state))
               (- (and erp
                       (cw "ERROR (~x0) with advice attempt for event ~X12 (continuing...).~%" erp event nil)
                       )))
            (if erp
                ;; If there is an error, the result is meaningless.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                (b* (((mv erp state)
                      ;; We use skip-proofs (but see the attachment to always-do-proofs-during-make-event-expansion below):
                      ;; TODO: Don't wrap certain events in skip-proofs?
                      (submit-event-helper-core `(skip-proofs ,event) print state))
                     ((when erp)
                      (er hard? 'submit-events-and-eval-models "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                      (mv erp nil state)))
                  (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models result-alist-acc state))
              (if trivialp
                  ;; If the theorem is trivial, no useful information is returned.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                  (b* (((mv erp state)
                        ;; We use skip-proofs (but see the attachment to always-do-proofs-during-make-event-expansion below):
                        ;; TODO: Don't wrap certain events in skip-proofs?
                        (submit-event-helper-core `(skip-proofs ,event) print state))
                       ((when erp)
                        (er hard? 'submit-events-and-eval-models "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                        (mv erp nil state)))
                    (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models result-alist-acc state))
                ;; No error, so count the result:
                (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models
                                               (acons (list current-book-absolute-path ; todo: use a relative path?
                                                            (cadr event) ; theorem-name
                                                            :all-hints-removed ; breakage-type
                                                            )
                                                      model-results
                                                      result-alist-acc)
                                               state))))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event-helper-core `(skip-proofs ,event) print state))
             ;; FIXME: Anything that tries to read from a file will give an error since the current dir won't be right.
             ((when erp)
              (cw "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp nil state))
             (- (and (acl2::print-level-at-least-tp print) (cw "~x0~%" (shorten-event event)))))
          (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models result-alist-acc state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads and then submits all the events in FILENAME, trying advice for the theorems.
;; Returns (mv erp result-alist state), where RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
;; Since this returns an error triple, it can be wrapped in revert-world.
(defun eval-models-on-book (filename ; the book, with .lisp extension, we should have already checked that it exists
                            theorems-to-try
                            num-recs-per-model
                            print
                            debug step-limit time-limit
                            server-url
                            models
                            state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or (null server-url)
                                  (stringp server-url))
                              (help::model-namesp models))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* ( ;; We must avoid including the current book (or an other book that includes it) when trying to find advice:
       (current-book-absolute-path (canonical-pathname filename nil state))
       ((when (member-equal current-book-absolute-path
                            (included-books-in-world (w state))))
        (cw "WARNING: Can't replay ~s0 because it is already included in the world.~%" filename)
        (mv nil nil state))
       ((mv dir &) (split-path filename))
       (- (cw "Evaluating advice on ~s0:~%" filename))
       ;; May be necessary for resolving #. constants in read-objects-from-book:
       (state (load-port-file-if-exists (remove-lisp-suffix filename t) state))
       ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-book filename state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp nil state))
       (len-all-events (len events))
       (events (discard-events-after-last-advice-event events theorems-to-try))
       (- (cw "(~x0 total events, ~x1 after discarding final events.)~%~%" len-all-events (len events)))
       ((when (null events))
        (cw "~%SUMMARY for book ~s0: NO EVENTS TO EVALUATE.  Theorems to try were ~X12.~%" filename theorems-to-try nil)
        (mv nil ; no error, but nothing to do for this book
            nil state))
       ;; Ensures we are working in the same dir as the book:
       ;; TODO: Ensure this gets reset upon failure, such as a package name clash.
       ((mv erp & state)
        (set-cbd-fn dir state))
       ((when erp) (mv erp nil state))
       ;; Make margins wider for nicer printing:
       (state (widen-margins state))
       ;; Ensure proofs are done during make-event expansion, even if we use skip-proofs:
       ((mv erp state) (submit-event-helper-core '(defattach (acl2::always-do-proofs-during-make-event-expansion acl2::constant-t-function-arity-0) :system-ok t) nil state))
       ((when erp) (mv erp nil state))
       ;; Submit all the events, trying advice for each defthm in theorems-to-try:
       ((mv erp result-alist state)
        (submit-events-and-eval-models events theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url models nil state))
       ((when erp) ; I suppose we could return partial results from this book instead
        (cw "Error: ~x0.~%" erp)
        (mv erp nil state))
       ;; Print stats:
       ;; TODO: Improve;
       (- (cw "Results for this book: ~X01" result-alist nil))

       ;; (- (progn$ (cw "~%SUMMARY for book ~s0:~%" filename)
       ;;            (cw "(Asked each model for ~x0 recommendations.)~%" num-recs-per-model)
       ;;            (cw "ADVICE FOUND    : ~x0~%" yes-count)
       ;;            (cw "NO ADVICE FOUND : ~x0~%" no-count)
       ;;            ;; (cw "ADD HYP ADVICE FOUND : ~x0~%" maybe-count)
       ;;            (cw "NO HINTS NEEDED : ~x0~%" trivial-count)
       ;;            (cw "ERROR           : ~x0~%" error-count)))
       ;; Undo margin widening:
       (state (unwiden-margins state)))
    (mv nil ; no error
        result-alist
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walks through the BOOK-TO-THEOREMS-ALIST, obtaining and evaluating advice for (some or no theorems in) each book.
;; Returns (mv erp event state).
(defun eval-models-on-books-fn-aux (book-to-theorems-alist
                                    base-dir
                                    num-recs-per-model
                                    print
                                    debug step-limit time-limit
                                    server-url
                                    models
                                    done-book-count
                                    result-alist-acc ; a result-alist
                                    state)
  (declare (xargs :guard (and (alistp book-to-theorems-alist)
                              (stringp base-dir)
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (help::model-namesp models)
                              (alistp result-alist-acc)
                              (natp done-book-count))
                  :mode :program
                  :stobjs state))
  (if (endp book-to-theorems-alist)
      (progn$ (cw "~%======================================================================~%")
              (cw "~%OVERALL RESULTS (~x0 total theorems):~%" (len result-alist-acc))
              (show-model-evaluations models result-alist-acc)
              (mv nil '(value-triple :invisible) state))
    (b* ((- (cw "~%======================================================================~%"))
         (- (cw "Processing book #~x0.~%" (+ 1 done-book-count)))
         (entry (first book-to-theorems-alist))
         (book (car entry))
         (theorems-to-try (cdr entry))
         ((mv erp result-alist-for-book state)
          (revert-world (eval-models-on-book (concatenate 'string base-dir "/" book)
                                             theorems-to-try
                                             num-recs-per-model
                                             print
                                             debug step-limit time-limit
                                             server-url
                                             models
                                             state)))
         (- (and erp (cw "WARNING: Error replaying ~x0.~%" book)))
         (done-book-count (+ 1 done-book-count))
         (result-alist-acc (append result-alist-for-book result-alist-acc))
         (- (progn$ (cw "~%~%Results after ~x0 books:~%" done-book-count)
                    (show-model-evaluations models result-alist-acc) ; todo: optimize?
                    ))
         ;;            (cw "ADVICE FOUND    : ~x0~%" yes-count)
         ;;            (cw "NO ADVICE FOUND : ~x0~%" no-count)
         ;;            ;; (cw "ADD HYP ADVICE FOUND : ~x0~%" maybe-count)
         ;;            (cw "NO HINTS NEEDED : ~x0~%" trivial-count)
         ;;            (cw "ERROR           : ~x0~%~%" error-count)))
         )
      (eval-models-on-books-fn-aux (rest book-to-theorems-alist)
                                   base-dir num-recs-per-model print debug step-limit time-limit server-url models done-book-count
                                   result-alist-acc
                                   state))))

;; Returns (mv erp event state).
(defun eval-models-on-books-fn (tests base-dir num-recs-per-model excluded-prefixes seed print debug step-limit time-limit server-url models num-tests state)
  (declare (xargs :guard (and (alistp tests)
                              (string-listp (strip-cars tests))
                              (symbol-listp (strip-cdrs tests))
                              (stringp base-dir)
                              (natp num-recs-per-model)
                              (string-listp excluded-prefixes)
                              (or (eq :random seed)
                                  (minstd-rand0p seed))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (or (eq :all models)
                                  (help::model-namep models) ; special case for a single model
                                  (help::model-namesp models))
                              (or (eq :all num-tests)
                                  (natp num-tests)))
                  :mode :program
                  :stobjs state))
  (b* ( ;; Elaborate options:
       (models (if (eq models :all)
                   help::*known-models*
                 (if (help::model-namep models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       ((mv seed state)
        (if (eq :random seed)
            (random$ *m31* state)
          (mv seed state)))
       (- (cw "(Using random seed of ~x0.)~%" seed))
       (- (cw "(Trying ~x0 recommendations per model.)~%" num-recs-per-model))
       (tests (clear-keys-with-matching-prefixes tests excluded-prefixes nil))
       (len-tests (len tests))
       ((when (and (not (eq :all num-tests))
                   (> num-tests len-tests)))
        (mv :not-enough-tests nil state))
       (tests (if (eq :all num-tests)
                  (prog2$ (cw "Using all ~x0 tests.~%" len-tests)
                          tests)
                (prog2$ (cw "Randomly choosing ~x0 from among the ~x1 tests.~%" num-tests len-tests)
                        (take num-tests (shuffle-list2 tests seed)))))
       (tests-sorted (merge-sort-string<-of-cadr tests))
       (book-to-theorems-alist (group-pairs tests-sorted nil))
       (book-to-theorems-alist (shuffle-list2 book-to-theorems-alist (minstd-rand0-next seed)))
       (- (cw "(Processing ~x0 tests in ~x1 books.)~%" num-tests (len book-to-theorems-alist))))
    (eval-models-on-books-fn-aux book-to-theorems-alist base-dir num-recs-per-model print debug step-limit time-limit server-url models 0 nil state)))

;; TODO: Record the kinds of recs that work (note that names may get combined with /)?
;; Rec names should not include slash or digits?
(defmacro eval-models-on-books (tests ; pairs of the form (book-name . theorem-name) where book-names are relative to BASE-DIR and have the .lisp extension
                                base-dir               ; no trailing slash
                                &key
                                (excluded-prefixes 'nil) ; relative to BASE-DIR
                                (seed ':random)
                                (server-url 'nil) ; nil means get from environment var
                                (models ':all)    ; which ML models to use
                                (num-tests ':all) ; how many books to evaluate (TODO: Better to chose a random subset of theorems, rather than books?)
                                (print 'nil)
                                (debug 'nil)
                                (step-limit '10000)
                                (time-limit '5)
                                (num-recs-per-model '20))
  `(make-event (eval-models-on-books-fn ,tests ,base-dir ,num-recs-per-model ,excluded-prefixes ,seed ,print ,debug ,step-limit ,time-limit ,server-url ,models ,num-tests state)))
