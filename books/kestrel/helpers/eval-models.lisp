; A tool to evaluate the proof-advice-generating models
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: change to HELP package

(include-book "replay-book-with-advice") ; todo: factor out common stuff
(include-book "replay-books-with-advice") ; todo: factor out common stuff: clear-keys-with-matching-prefixes
(include-book "advice")
(include-book "kestrel/utilities/split-path" :dir :system)
(include-book "kestrel/axe/merge-sort-less-than" :dir :system) ; todo: move
(include-book "kestrel/strings-light/upcase" :dir :system)
(include-book "kestrel/lists-light/remove-nth" :dir :system)
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/make-list-ac" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

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

;; pads on the left!
(defun symbol-to-left-padded-string-of-length (sym len)
  (declare (xargs :guard (and (symbolp sym)
                              (natp len))
;                  :verify-guards nil ; todo
                  ))
  (let* ((str (symbol-name sym))
         (chars (coerce str 'list))
         (new-chars (if (<= len (len chars))
                        (take len chars) ;may chop
                      (append (make-list (- len (len chars)) :initial-element #\Space)
                              chars))))
    (coerce new-chars 'string)))

;; Returns the successful-attempt-percentage.
(defun show-model-evaluation (model result-alist)
  (declare (xargs :mode :program)) ;todo
  (b* (((mv attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums total-recs-produced)
        (tabulate-resuls-for-model model result-alist 0 0 0 0 nil 0))
       (successful-attempt-percentage (quotient-to-percent-string successful-attempt-count attempt-count))
       (- (cw "Results for model ~x0 (~x1 theorem attempts, ~x2 total recs produced):~%" model attempt-count total-recs-produced))
       (- (cw "Success: ~x0 (~s1%)~%" successful-attempt-count successful-attempt-percentage))
       (- (cw "Nums of first successful recs: ~X01~%" successful-rec-nums nil)) ; todo: summarize better
       (- (cw "Top-1: ~x0 (~s1%)~%" top-1-count (quotient-to-percent-string top-1-count attempt-count)))
       (- (cw "Top-10: ~x0 (~s1%)~%~%" top-10-count (quotient-to-percent-string top-10-count attempt-count)))
       )
    successful-attempt-percentage))

;; Prints result and computes a success percentage alist.
;; RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
(defun show-model-evaluations-aux (models result-alist)
  (declare (xargs :mode :program)) ;todo
  (if (endp models)
      nil
    (let* ((model (first models))
           (successful-attempt-percentage (show-model-evaluation model result-alist))) ; prints the info
      (acons model
             successful-attempt-percentage
             (show-model-evaluations-aux (rest models) result-alist)))))

(defun show-success-percentages (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (if (endp alist)
      (cw "~%")
    (let* ((pair (first alist))
           (model (car pair))
           (percent-string (cdr pair)))
      (prog2$ (cw "~s0: ~s1%~%" (symbol-to-left-padded-string-of-length model 20) percent-string) ;todo: align better
              (show-success-percentages (rest alist))))))

;; RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
(defun show-model-evaluations (models result-alist)
  (declare (xargs :mode :program)) ;todo
  (let ((alist (show-model-evaluations-aux models result-alist)))
    (prog2$ (cw "~%Current success percentages:~%")
            (show-success-percentages alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Returns (mv erp first-working-rec-num-or-nil state).
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

(defun hint-settings-for-goal-spec (goal-spec hints)
  (declare (xargs :guard (and (stringp goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (and (consp hint)
               (stringp (car hint))
               (equal (string-upcase-gen goal-spec)
                      (string-upcase-gen (car hint))))
          (cdr hint)
        (hint-settings-for-goal-spec goal-spec (rest hints))))))

(defund remove-settings-for-goal-spec (goal-spec hints)
  (declare (xargs :guard (and (stringp goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (and (consp hint)
               (stringp (car hint))
               (equal (string-upcase-gen goal-spec)
                      (string-upcase-gen (car hint))))
          (remove-settings-for-goal-spec goal-spec (rest hints))
        (cons hint (remove-settings-for-goal-spec goal-spec (rest hints)))))))

(defun num-ways-to-break-hint-setting (keyword val)
  (declare (xargs :guard (keywordp keyword)))
  (case keyword
    (:by 1) ; can only remove the whole thing
    (:cases 1) ; can only remove the whole thing
    (:induct 1) ; can only remove the whole thing
    (:nonlinearp 1) ; can only remove the whole thing
    (:do-not (if (and (quotep val)
                      (consp (cdr val)))
                 ;; can remove each thing in the list:
                 (len (unquote val))
               1 ; can only remove the whole thing
               ))
    (:expand (len (acl2::desugar-expand-hint val)))
    (:use (len (acl2::desugar-use-hint val)))
    (:in-theory (if (or (call-of 'acl2::enable val)
                        (call-of 'acl2::disable val))
                    (len (fargs val))
                  (if (call-of 'acl2::e/d val)
                      (let ((lists (fargs val)))
                        ;; Only mess with the first 2:
                        (+ (if (< 0 (len lists)) (len (first lists)) 0)
                           (if (< 1 (len lists)) (len (second lists)) 0)))
                    ;; TODO: Handle enable*, disable*, and e/d*:
                    1 ; can only remove the whole thing
                    )))
    (otherwise 0)))

(defun num-ways-to-break-hint-settings (hint-settings)
  (declare (xargs :guard (keyword-value-listp hint-settings)))
  (if (endp hint-settings)
      0
    (let ((keyword (car hint-settings))
          (val (cadr hint-settings)))
      (+ (num-ways-to-break-hint-setting keyword val)
         (num-ways-to-break-hint-settings (cddr hint-settings))))))

;; n is 0-based and is known to be less than the number of ways to break the hint-setting.
;; Returns (mv breakage-type result), where RESULT is a list (possibly nil) to be spliced into the hint settings, replacing the KEYWORD and VAL.
(defun break-hint-setting-in-nth-way (n keyword val)
  (declare (xargs :guard (and (natp n)
                              (keywordp keyword)
                              (< n (num-ways-to-break-hint-setting keyword val)))))
  (case keyword
    (:by (mv :remove-by nil))                 ; can only remove the whole thing
    (:cases (mv :remove-cases nil))           ; can only remove the whole thing
    (:induct (mv :remove-induct nil))         ; can only remove the whole thing
    (:nonlinearp (mv :remove-nonlinearp nil)) ; can only remove the whole thing
    (:do-not (if (and (quotep val)
                      (consp (cdr val)))
                 ;; remove one thing in the list:
                 (mv :remove-do-not-item
                     (list :do-not (kwote (remove-nth n (unquote val)))))
               (mv :remove-do-not nil) ; can only remove the whole thing
               ))
    (:expand (mv :remove-expand-item
                 (list :expand (remove-nth n (acl2::desugar-expand-hint val)))))
    (:use (mv :remove-use-item
              (list :use (remove-nth n (acl2::desugar-use-hint val)))))
    (:in-theory (if (call-of 'acl2::enable val)
                    (mv :remove-enable-item
                        (list :in-theory `(,(ffn-symb val) ,@(remove-nth n (fargs val)))))
                  (if (call-of 'acl2::disable val)
                      (mv :remove-disable-item
                          (list :in-theory `(,(ffn-symb val) ,@(remove-nth n (fargs val)))))
                    (if (call-of 'acl2::e/d val)
                        (let ((lists (fargs val)))
                          (if (< n (len (first lists)))
                              (mv :remove-enable-item ; or we could indicate it was in an e/d
                                  (list :in-theory `(e/d ,(remove-nth n (first lists)) ,@(rest lists))))
                            ;; Only mess with the first 2, so it must be in the second one:
                            (mv :remove-disable-item ; or we could indicate it was in an e/d
                                (list :in-theory `(e/d ,(first lists)
                                                       ,(remove-nth (- n (len (first lists))) (second lists))
                                                       ,@(rest (rest lists)))))))
                      ;; TODO: Handle enable*, disable*, and e/d*:
                      (mv :remove-in-theory
                          nil) ; can only remove the whole thing
                      ))))
    (otherwise (mv :error (er hard 'break-hint-setting-in-nth-way "Unhandled case")))))

;; Returns (mv breakage-type hint-settings).
; n is 0-based
(defun break-hint-settings-in-nth-way (n hint-settings)
  (declare (xargs :guard (and (natp n)
                              (keyword-value-listp hint-settings)
                              (< n (num-ways-to-break-hint-settings hint-settings)))
                  :measure (len hint-settings)))
  (if (endp hint-settings)
      (mv :error (er hard? 'break-hint-settings-in-nth-way "Ran out of hint settings!"))
    (let ((keyword (car hint-settings))
          (val (cadr hint-settings)))
      (let ((ways (num-ways-to-break-hint-setting keyword val)))
        (if (< n ways)
            (mv-let (breakage-type result)
              (break-hint-setting-in-nth-way n keyword val)
              (mv breakage-type
                  (append result (cddr hint-settings))))
          (mv-let (breakage-type new-cddr)
            (break-hint-settings-in-nth-way (- n ways) (cddr hint-settings))
            (mv breakage-type
                (cons keyword (cons val new-cddr)))))))))

;; Returns (mv breakage-type hint-settings rand).
(defun randomly-break-hint-settings (hint-settings rand)
  (declare (xargs :guard (and (keyword-value-listp hint-settings)
                              (minstd-rand0p rand))))
  (let* ((total-ways (num-ways-to-break-hint-settings hint-settings)))
    (if (not (posp total-ways))
        (mv :none nil rand)
      (let* ((breakage-num (mod rand total-ways))
             (rand (minstd-rand0-next rand)))
        (mv-let (breakage-type hint-settings)
          (break-hint-settings-in-nth-way breakage-num hint-settings)
          (mv breakage-type hint-settings rand))))))

;; Returns (mv breakage-type hints rand).
(defun randomly-break-hints (hints rand)
  (declare (xargs :guard (and (true-listp hints)
                              (minstd-rand0p rand))))
  (let ((goal-hint-settings (hint-settings-for-goal-spec "Goal" hints)))
    (if (not (keyword-value-listp goal-hint-settings))
        (prog2$ (er hard? 'randomly-break-hints "Bad hint for Goal: ~x0" hints)
                (mv :none nil rand))
      (mv-let (breakage-type broken-hint-settings rand)
        (randomly-break-hint-settings goal-hint-settings rand)
        (if (eq :none breakage-type)
            (mv :none nil rand)
          (mv breakage-type
              (cons (cons "Goal" broken-hint-settings)
                    (remove-settings-for-goal-spec "Goal" hints) ; removal might not be necessary, due to shadowing
                    )
              rand))))))

;; Determines whether the Proof Advice tool can find advice for the given DEFTHM.  Either way, this also submits DEFTHM.
;; Returns (mv erp breakage-type trivialp model-results rand state), where each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
;; Here, trivialp means "no model was needed".
(defun eval-models-and-submit-defthm-event (defthm num-recs-per-model current-book-absolute-path print debug step-limit time-limit
                                             server-url
                                             breakage-plan ; :all means remove all hints, :goal-partial means remove part of the "Goal" hint -- todo: add more options
                                             models rand state)
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
                              (member-eq breakage-plan '(:all :goal-partial))
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
       (theorem-hints (cadr (assoc-keyword :hints (cdddr defthm))))

       ((when (null theorem-hints))
        (cw "Skipping ~x0 since it has no hints to remove.~%" theorem-name)
        (mv nil ; no error
            :not-attempted ; no breakage of hints possible
            t ; there were no hints (and we assume it proves without them)
            nil rand state))

       ((when (and (eq breakage-plan :goal-partial)
                   (null (hint-settings-for-goal-spec "Goal" theorem-hints))))
        (cw "Skipping ~x0 since it has no hints on Goal.~%" theorem-name)
        (mv nil ; no error
            :not-attempted ; no breakage of hints possible, given the breakage-plan (TODO: consider plans to break subgoal hints or computed hints)
            t ; there were no Goal hints for us to try removing
            nil rand state))

       ;; Break the hints:
       ((mv breakage-type broken-theorem-hints rand)
        (if (eq breakage-plan :goal-partial)
            (b* ((- (cw "Removing part of the Goal hint.~%"))
                 ;; (- (cw "rand is ~x0.~%" rand))
                 ((mv breakage-type broken-theorem-hints rand) (randomly-break-hints theorem-hints rand))
                 (rand (minstd-rand0-next rand)))
              (prog2$ (cw "Removing all the :hints.~%")
                      (mv breakage-type broken-theorem-hints rand)))
          (mv :all nil rand)))

       ((when (eq :none breakage-type))
        (cw "NOTE: No way to break hints: ~x0.~%" theorem-hints)
        (mv nil ; no error
            :not-attempted ; no breakage of hints possible (unless we consider breaking subgoal hints or computed hints)
            t ; we found no way to break the hints, for some reason (maybe only an empty enable, or something like that)
            nil rand state))
       (- (cw "(ADVICE: ~x0: " theorem-name))
       ((mv erp provedp & checkpoint-clauses state)
        (help::try-proof-and-get-checkpoint-clauses theorem-name
                                                    theorem-body
                                                    (acl2::translate-term theorem-body 'eval-models-and-submit-defthm-event (w state))
                                                    broken-theorem-hints
                                                    theorem-otf-flg ; or use nil ?
                                                    step-limit time-limit
                                                    t ; suppress-trivial-warningp
                                                    state))
       ((when erp) (mv erp nil nil nil rand state)))
    (if provedp
        (b* ((- (cw "Trivial: Broken hints worked for ~x0)~%" theorem-name)) ;todo: tabulate these
             ((mv erp state) ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event-helper-core `(skip-proofs ,defthm) print state))
             ((when erp) (mv erp nil nil nil rand state)))
          (mv nil ; no error
              breakage-type
              t   ; theorem was trivial (no hints needed)
              nil
              rand
              state))
      ;; Breaking the hints did break the theorem, yielding checkpoints:
      (b* (((mv erp model-results state)
            (eval-models-on-checkpoints checkpoint-clauses
                                        theorem-name
                                        theorem-body
                                        broken-theorem-hints
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
           ((when erp) (mv erp nil nil nil rand state))
           ((mv erp state) ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
            (submit-event-helper-core `(skip-proofs ,defthm) print state))
           ((when erp) (mv erp nil nil nil rand state))
           (- (cw ")~%")) ; todo: print which model(s) worked
           )
        (mv nil ; no error
            breakage-type
            nil ; not trivial
            model-results
            rand
            state)))))

;; Returns (mv erp result-alist rand state), where RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
;throws an error if any event fails
(defun submit-events-and-eval-models (events theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models result-alist-acc rand state)
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
                              (member-eq breakage-plan '(:all :goal-partial))
                              (help::model-namesp models)
                              (alistp result-alist-acc))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil ; no error
          result-alist-acc
          rand
          state)
    (let ((event (first events)))
      (if (advice-eventp event theorems-to-try)
          ;; It's a theorem for which we are to try advice:
          (b* ( ;; Try to prove it using advice:
               ((mv erp breakage-type trivialp model-results rand state)
                (eval-models-and-submit-defthm-event event num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models rand state))
               (- (and erp (cw "ERROR (~x0) with advice attempt for event ~X12 (continuing...).~%" erp event nil))))
            (if erp
                ;; If there is an error, the result is meaningless.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                (b* (((mv erp state)
                      (submit-event-helper-core `(skip-proofs ,event) print state))
                     ((when erp)
                      (er hard? 'submit-events-and-eval-models "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                      (mv erp nil rand state)))
                  (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models result-alist-acc rand state))
              (if trivialp
                  ;; If the theorem is trivial, no useful information is returned.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                  (b* (((mv erp state)
                        (submit-event-helper-core `(skip-proofs ,event) print state))
                       ((when erp)
                        (er hard? 'submit-events-and-eval-models "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                        (mv erp nil rand state)))
                    (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models result-alist-acc rand state))
                ;; No error, so count the result:
                (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models
                                               (acons (list current-book-absolute-path ; todo: use a relative path?
                                                            (cadr event) ; theorem-name
                                                            breakage-type)
                                                      model-results
                                                      result-alist-acc)
                                               rand
                                               state))))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event-helper-core `(skip-proofs ,event) print state))
             ;; FIXME: Anything that tries to read from a file will give an error since the current dir won't be right.
             ((when erp)
              (cw "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp nil rand state))
             (- (and (acl2::print-level-at-least-tp print) (cw "~x0~%" (shorten-event event)))))
          (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models result-alist-acc rand state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads and then submits all the events in FILENAME, trying advice for the theorems indicated by THEOREMS-TO-TRY.
;; Returns (mv erp result-alist+rand state), where RESULT-ALIST+RAND is a cons of RESULT-ALIST and RAND, and where RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
;; Since this returns an error triple, it can be wrapped in revert-world.
(defun eval-models-on-book (filename ; the book, with .lisp extension, we should have already checked that it exists
                            theorems-to-try
                            num-recs-per-model
                            print
                            debug step-limit time-limit
                            server-url breakage-plan
                            models
                            rand
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
                              (member-eq breakage-plan '(:all :goal-partial))
                              (help::model-namesp models))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* ( ;; We must avoid including the current book (or an other book that includes it) when trying to find advice:
       (current-book-absolute-path (canonical-pathname filename nil state))
       ((when (member-equal current-book-absolute-path
                            (included-books-in-world (w state))))
        (cw "WARNING: Can't replay ~s0 because it is already included in the world.~%" filename)
        (mv nil (cons nil rand) state))
       ((mv dir &) (split-path filename))
       (- (cw "Evaluating advice on ~s0:~%" filename))
       ;; May be necessary for resolving #. constants in read-objects-from-book:
       (state (load-port-file-if-exists (remove-lisp-suffix filename t) state))
       ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-book filename state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp (cons nil rand) state))
       (len-all-events (len events))
       (events (discard-events-after-last-advice-event events theorems-to-try))
       (- (cw "(~x0 total events, ~x1 after discarding final events.)~%~%" len-all-events (len events)))
       ((when (null events))
        (cw "~%SUMMARY for book ~s0: NO EVENTS TO EVALUATE.  Theorems to try were ~X12.~%" filename theorems-to-try nil)
        (mv nil ; no error, but nothing to do for this book
            (cons nil rand) state))
       ;; Ensures we are working in the same dir as the book:
       ;; TODO: Ensure this gets reset upon failure, such as a package name clash.
       ((mv erp & state)
        (set-cbd-fn dir state))
       ((when erp) (mv erp (cons nil rand) state))
       ;; Make margins wider for nicer printing:
       (state (widen-margins state))
       ;; Ensure proofs are done during make-event expansion, even if we use skip-proofs:
       ((mv erp state) (submit-event-helper-core '(defattach (acl2::always-do-proofs-during-make-event-expansion acl2::constant-t-function-arity-0) :system-ok t) nil state))
       ((when erp) (mv erp (cons nil rand) state))
       ;; Submit all the events, trying advice for each defthm in theorems-to-try:
       ((mv erp result-alist rand state)
        (submit-events-and-eval-models events theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models nil rand state))
       ((when erp) ; I suppose we could return partial results from this book instead
        (cw "Error: ~x0.~%" erp)
        (mv erp (cons nil rand) state))
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
        (cons result-alist rand)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walks through the BOOK-TO-THEOREMS-ALIST, obtaining and evaluating advice for (some or no theorems in) each book.
;; Returns (mv erp event state).
(defun eval-models-on-books-fn-aux (book-to-theorems-alist
                                    base-dir
                                    num-recs-per-model
                                    print
                                    debug step-limit time-limit
                                    server-url breakage-plan
                                    models
                                    done-book-count
                                    result-alist-acc ; a result-alist
                                    rand
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
                              (member-eq breakage-plan '(:all :goal-partial))
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
         ((mv erp result-alist-for-book+rand state)
          (revert-world (eval-models-on-book (concatenate 'string base-dir "/" book)
                                             theorems-to-try
                                             num-recs-per-model
                                             print
                                             debug step-limit time-limit
                                             server-url breakage-plan
                                             models
                                             rand
                                             state)))
         (result-alist-for-book (car result-alist-for-book+rand))
         (rand (cdr result-alist-for-book+rand))
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
                                   base-dir num-recs-per-model print debug step-limit time-limit server-url breakage-plan models done-book-count
                                   result-alist-acc
                                   rand
                                   state))))

;; Returns (mv erp event state).
(defun eval-models-on-books-fn (tests base-dir num-recs-per-model excluded-prefixes seed print debug step-limit time-limit server-url breakage-plan models num-tests state)
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
                              (member-eq breakage-plan '(:all :goal-partial))
                              (or (eq :all models)
                                  (help::model-namep models) ; special case for a single model
                                  (help::model-namesp models))
                              (or (eq :all num-tests)
                                  (natp num-tests)))
                  :mode :program
                  :stobjs state))
  (b* ( ;; Elaborate options:
       (models (if (eq models :all)
                   help::*ready-models* ; help::*known-models*
                 (if (help::model-namep models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       ;; Initialize the source of randomness:
       ((mv rand state)
        (if (eq :random seed)
            (random$ *m31* state)
          (mv seed state)))
       (- (cw "(Using random seed of ~x0.)~%" rand))
       (- (cw "(Trying ~x0 recommendations per model.)~%" num-recs-per-model))
       (tests (clear-keys-with-matching-prefixes tests excluded-prefixes nil))
       (len-tests (len tests))
       ((when (and (not (eq :all num-tests))
                   (> num-tests len-tests)))
        (mv :not-enough-tests nil state))
       ;; Choose which
       (tests (if (eq :all num-tests)
                  (prog2$ (cw "Using all ~x0 tests.~%" len-tests)
                          tests)
                (prog2$ (cw "Randomly choosing ~x0 from among the ~x1 tests.~%" num-tests len-tests)
                        (take num-tests (shuffle-list2 tests rand)))))
       (rand (minstd-rand0-next rand))
       ;; Group tests by book:
       (tests-sorted (merge-sort-string<-of-cadr tests))
       (book-to-theorems-alist (group-pairs tests-sorted nil))
       ;; Randomize book order:
       (book-to-theorems-alist (shuffle-list2 book-to-theorems-alist rand))
       (rand (minstd-rand0-next rand))
       (- (cw "(Processing ~x0 tests in ~x1 books.)~%" num-tests (len book-to-theorems-alist))))
    (eval-models-on-books-fn-aux book-to-theorems-alist base-dir num-recs-per-model print debug step-limit time-limit server-url breakage-plan models 0 nil rand state)))

;; TODO: Record the kinds of recs that work (note that names may get combined with /)?
;; TODO: Record the sources of recs that work (note that names may get combined with /)?
;; TODO: Record how often any model works.
;; TODO: Record the time taken to find the first result.
;; TODO: Determine which models solve problems on which most or all other models fail.
;; TODO: Delete only parts of hints, like Matt's tool does.
;; Rec names should not include slash or digits?
(defmacro eval-models-on-books (tests ; pairs of the form (book-name . theorem-name) where book-names are relative to BASE-DIR and have the .lisp extension
                                base-dir               ; no trailing slash
                                &key
                                (excluded-prefixes 'nil) ; relative to BASE-DIR
                                (seed ':random)
                                (server-url 'nil) ; nil means get from environment var
                                (breakage-plan ':goal-partial)
                                (models ':all)    ; which ML models to use
                                (num-tests ':all) ; how many books to evaluate (TODO: Better to chose a random subset of theorems, rather than books?)
                                (print 'nil)
                                (debug 'nil)
                                (step-limit '10000)
                                (time-limit '5)
                                (num-recs-per-model '20))
  `(make-event (eval-models-on-books-fn ,tests ,base-dir ,num-recs-per-model ,excluded-prefixes ,seed ,print ,debug ,step-limit ,time-limit ,server-url ,breakage-plan ,models ,num-tests state)))
