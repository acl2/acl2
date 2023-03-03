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
(include-book "kestrel/lists-light/remove-nth" :dir :system)
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/make-list-ac" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; TODO: removing :add-hyp gets us less the requested number of recs sometimes!

;; An indicator for a test, of the form (book-name theorem-name breakage-type).
(defun test-infop (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= 3 (len x))
       (stringp (first x))     ; book-name
       (symbolp (second x))    ; theorem-name
       (keywordp (third x)) ; breakage-type
       ))

(defun model-resultp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= 4 (len x))
       (member-eq (first x) help::*known-models*) ; model
       (natp (second x)) ; total-num-recs
       (or (null (third x)) ; first-working-rec-num-or-nil
           (posp x))
       (rationalp (fourth x)) ; time-to-find-first-working-rec
       ))

;; can be treated like an alist
(defun model-result-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (model-resultp (first x))
         (model-result-listp (rest x)))))

;; Maps test-infos to model-result-lists.
(defun result-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (test-infop (car entry))
           (model-result-listp (cdr entry))
           (result-alistp (rest alist))))))

(local (in-theory (disable natp)))
(local (defthm natp-of-+ (implies (and (natp x) (natp y)) (natp (+ x y)))))

;; todo: have defmergesort use rational-listp instead
(local (defthm all-rationalp-when-nat-listp
         (implies (nat-listp x)
                  (all-rationalp x))
         :hints (("Goal" :in-theory (enable all-rationalp)))))

;;Returns (mv attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums total-recs-produced).
(defun tabulate-resuls-for-model (model result-alist attempt-count successful-attempt-count top-1-count top-10-count successful-rec-nums-acc total-recs-produced)
  (declare (xargs :guard (and (keywordp model) ; todo: improve?
                              (result-alistp result-alist)
                              (natp attempt-count)
                              (natp successful-attempt-count)
                              (natp top-1-count)
                              (natp top-10-count)
                              (nat-listp successful-rec-nums-acc)
                              (natp total-recs-produced))
                  :verify-guards nil ; todo
                  :guard-hints (("Goal" :expand (result-alistp result-alist)))))
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

;; Returns (mv successful-rec-num num-recs-produced).
(defun union-model-results (model-results
                            successful-rec-num ; best so far, or nil
                            num-recs-produced)
  (declare (xargs :guard (and (model-result-listp model-results)
                              (or (null successful-rec-num)
                                  (posp successful-rec-num))
                              (natp num-recs-produced))))
  (if (endp model-results)
      (mv successful-rec-num num-recs-produced)
    (let* ((model-result (first model-results))
           (model-num-recs (second model-result))
           (first-working-rec-num-or-nil (third model-result)))
      (union-model-results (rest model-results)
                           (if (and first-working-rec-num-or-nil
                                    (or (null successful-rec-num)
                                        (< first-working-rec-num-or-nil
                                           successful-rec-num)))
                               first-working-rec-num-or-nil
                             successful-rec-num)
                           (+ num-recs-produced model-num-recs)))))

(defthm natp-of-mv-nth-0-of-union-model-results
  (implies (and (mv-nth 0 (union-model-results model-results successful-rec-num num-recs-produced)) ; not nill
                (or (null successful-rec-num) (natp successful-rec-num))
                (model-result-listp model-results))
           (natp (mv-nth 0 (union-model-results model-results successful-rec-num num-recs-produced))))
  :hints (("Goal" :in-theory (enable union-model-results))))

(defthm natp-of-mv-nth-1-of-union-model-results
  (implies (and (natp num-recs-produced)
                (model-result-listp model-results))
           (natp (mv-nth 1 (union-model-results model-results successful-rec-num num-recs-produced))))
  :hints (("Goal" :in-theory (enable union-model-results))))

;; Tabulates results for a hypothetical model that combines all the models (if any can prove something, the union model can prove it).
;;Returns (mv attempt-count successful-attempt-count successful-rec-nums total-recs-produced).
(defun tabulate-resuls-for-union-model (result-alist
                                        attempt-count
                                        successful-attempt-count
                                        ;; top-1-count top-10-count
                                        successful-rec-nums-acc ; the lowest successful rec from any model (if any) on each test
                                        total-recs-produced)
  (declare (xargs :guard (and (result-alistp result-alist)
                              (natp attempt-count)
                              (natp successful-attempt-count)
                              (nat-listp successful-rec-nums-acc)
                              (natp total-recs-produced))))
;  (declare (xargs :mode :program)) ;todo
  (if (endp result-alist)
      (mv attempt-count successful-attempt-count (merge-sort-< successful-rec-nums-acc) total-recs-produced)
    (b* ((result-entry (first result-alist))
         (model-results (cdr result-entry))
         ((when (not model-results))
          (er hard? 'tabulate-resuls-for-union-model "No model results for test.")
          (mv nil nil nil nil))
         ((mv this-successful-rec-num this-recs-produced) (union-model-results model-results nil 0)))
      (tabulate-resuls-for-union-model (rest result-alist)
                                       (+ 1 attempt-count)
                                       (if this-successful-rec-num (+ 1 successful-attempt-count) successful-attempt-count)
                                       (if this-successful-rec-num (cons this-successful-rec-num successful-rec-nums-acc) successful-rec-nums-acc)
                                       (+ total-recs-produced this-recs-produced)))))

;; todo: support rounding to hundredths
(defun quotient-as-percent-string (numerator denominator)
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
                              (natp len))))
  (let* ((str (symbol-name sym))
         (chars (coerce str 'list))
         (new-chars (if (<= len (len chars))
                        (take len chars) ;may chop
                      (append (make-list (- len (len chars)) :initial-element #\Space)
                              chars))))
    (coerce new-chars 'string)))

(defun count-items-<= (items num acc)
  (declare (xargs :guard (and (nat-listp items)
                              (natp num)
                              (natp acc))))
  (if (endp items)
      acc
    (count-items-<= (rest items)
                    num
                    (if (<= (first items) num)
                        (+ 1 acc)
                      acc))))

;; inefficient but simple
(defun top-n-counts-aux (curr last successful-rec-nums)
  (declare (xargs :guard (and (posp curr)
                              (posp last)
                              (nat-listp successful-rec-nums))
                  :measure (nfix (+ 1 (- last curr)))))
  (if (or (not (mbt (and (posp curr)
                         (posp last))))
          (< last curr))
      nil
    (cons (count-items-<= successful-rec-nums curr 0)
          (top-n-counts-aux (+ 1 curr) last successful-rec-nums))))

;; Returns a list (c1 c2 ... c10) where ci indicates the number elements <= i.
(defun top-n-counts (successful-rec-nums)
  (declare (xargs :guard (and (nat-listp successful-rec-nums) ; all positive, sorted
                              )))
  (top-n-counts-aux 1 10 successful-rec-nums))

;; does not include the percent signs
(defun quotients-as-percent-strings (vals denominator)
  (declare (xargs :guard (and (nat-listp vals) ; gen
                              (rationalp denominator) ; 0 leads to a result of "undefined"
                              )
                  :mode :program ; todo
                  ))
  (if (endp vals)
      nil
    (cons (quotient-as-percent-string (first vals) denominator)
          (quotients-as-percent-strings (rest vals) denominator))))

(defun print-separated-strings (strings sep)
  (declare (xargs :guard (and (string-listp strings)
                              (stringp sep))))
  (if (endp strings)
      nil
    (if (endp (rest strings))
        (cw "~s0" (first strings)) ; avoids trailing separator
      (prog2$ (cw "~s0~s1" (first strings) sep)
              (print-separated-strings (rest strings) sep)))))

;; Returns the successful-attempt-percentage.
(defun show-model-evaluation (model result-alist)
  (declare (xargs :mode :program)) ;todo
  (b* (((mv attempt-count successful-attempt-count
            & & ; top-1-count top-10-count
            successful-rec-nums
            total-recs-produced)
        (tabulate-resuls-for-model model result-alist 0 0 0 0 nil 0))
       (successful-attempt-percentage (quotient-as-percent-string successful-attempt-count attempt-count))
       (- (cw "Results for model ~x0 (~x1 theorem attempts, ~x2 total recs produced):~%" model attempt-count total-recs-produced))
       (- (cw "Success: ~x0 (~s1%)~%" successful-attempt-count successful-attempt-percentage))
       ;; (- (cw "Nums of first successful recs: ~X01~%" successful-rec-nums nil))
       ;; (- (cw "Top-1 through top-10 counts: ~X01~%" (top-n-counts successful-rec-nums) nil))
       ;todo: print total recs produced?
       (- (cw "Top-1 through top-10 percentages: ["))
       (- (print-separated-strings (quotients-as-percent-strings (top-n-counts successful-rec-nums) attempt-count) ", "))
       (- (cw "]~%"))
       ;; (- (cw "Top-1: ~x0 (~s1%)~%" top-1-count (quotient-as-percent-string top-1-count attempt-count)))
       ;; (- (cw "Top-10: ~x0 (~s1%)~%~%" top-10-count (quotient-as-percent-string top-10-count attempt-count)))
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
      nil
    (let* ((pair (first alist))
           (model (car pair))
           (percent-string (cdr pair)))
      (prog2$ (cw "~s0: ~s1%~%" (symbol-to-left-padded-string-of-length model 20) percent-string) ;todo: align better
              (show-success-percentages (rest alist))))))

;; RESULT-ALIST is a map from (book-name, theorem-name, breakage-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
(defun show-model-evaluations (models result-alist num-recs-per-model)
  (declare (xargs :mode :program)) ;todo
  (b* ((alist (show-model-evaluations-aux models result-alist)) ; prints a lot
       (- (cw "~%Current top-~x0 success percentages:~%" num-recs-per-model))
       (- (show-success-percentages alist)) ; for each model
       ;; Now the combined results:
       (- (cw "~%Combined results:~%"))
       ((mv combined-attempt-count combined-successful-attempt-count combined-successful-rec-nums combined-total-recs-produced) (tabulate-resuls-for-union-model result-alist 0 0 nil 0))
       (combined-successful-attempt-percentage (quotient-as-percent-string combined-successful-attempt-count combined-attempt-count))
       (- (cw " Attempts: ~x0~%" combined-attempt-count))
       (- (cw " Successes: ~x0 (~s1%)~%" combined-successful-attempt-count combined-successful-attempt-percentage))
       (- (cw " Total recs produced: ~x0~%" combined-total-recs-produced))
       (- (cw "Top-1 through top-10 percentages: ["))
       (- (print-separated-strings (quotients-as-percent-strings (top-n-counts combined-successful-rec-nums) combined-attempt-count) ", "))
       (- (cw "]~%"))
       (- (cw "~%")))
    nil))

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

(defund remove-hints-for-goal-spec (goal-spec hints)
  (declare (xargs :guard (and (stringp goal-spec)
                              (standard-string-p goal-spec)
                              (true-listp hints))))
  (if (endp hints)
      nil
    (let ((hint (first hints)))
      (if (hint-has-goal-specp hint goal-spec)
          ;; Keep going, as there may be more matches:
          (remove-hints-for-goal-spec goal-spec (rest hints))
        (cons hint (remove-hints-for-goal-spec goal-spec (rest hints)))))))

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

(defun num-ways-to-break-hint-keyword-value-list (hint-keyword-value-list)
  (declare (xargs :guard (keyword-value-listp hint-keyword-value-list)))
  (if (endp hint-keyword-value-list)
      0
    (let ((keyword (car hint-keyword-value-list))
          (val (cadr hint-keyword-value-list)))
      (+ (num-ways-to-break-hint-setting keyword val)
         (num-ways-to-break-hint-keyword-value-list (cddr hint-keyword-value-list))))))

(local (in-theory (enable natp))) ;todo

;; n is 0-based and is known to be less than the number of ways to break the hint-setting.
;; Returns (mv breakage-type result), where RESULT is a list (possibly nil) to be spliced into the hint settings, replacing the KEYWORD and VAL.
(defun break-hint-setting-in-nth-way (n keyword val)
  (declare (xargs :guard (and (natp n)
                              (keywordp keyword)
                              (< n (num-ways-to-break-hint-setting keyword val)))
                  :guard-hints (("Goal" :in-theory (enable natp)))))
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

;; Returns (mv breakage-type hint-keyword-value-list).
; n is 0-based
(defun break-hint-keyword-value-list-in-nth-way (n hint-keyword-value-list)
  (declare (xargs :guard (and (natp n)
                              (keyword-value-listp hint-keyword-value-list)
                              (< n (num-ways-to-break-hint-keyword-value-list hint-keyword-value-list)))
                  :measure (len hint-keyword-value-list)))
  (if (endp hint-keyword-value-list)
      (mv :error (er hard? 'break-hint-keyword-value-list-in-nth-way "Ran out of hint settings!"))
    (let ((keyword (car hint-keyword-value-list))
          (val (cadr hint-keyword-value-list)))
      (let ((ways (num-ways-to-break-hint-setting keyword val)))
        (if (< n ways)
            (mv-let (breakage-type result)
              (break-hint-setting-in-nth-way n keyword val)
              (mv breakage-type
                  (append result (cddr hint-keyword-value-list))))
          (mv-let (breakage-type new-cddr)
            (break-hint-keyword-value-list-in-nth-way (- n ways) (cddr hint-keyword-value-list))
            (mv breakage-type
                (cons keyword (cons val new-cddr)))))))))

;; Returns (mv breakage-type hint-keyword-value-list rand).
(defun randomly-break-hint-keyword-value-list (hint-keyword-value-list rand)
  (declare (xargs :guard (and (keyword-value-listp hint-keyword-value-list)
                              (minstd-rand0p rand))))
  (let* ((total-ways (num-ways-to-break-hint-keyword-value-list hint-keyword-value-list)))
    (if (not (posp total-ways))
        (mv :none nil rand)
      (let* ((breakage-num (mod rand total-ways))
             (rand (minstd-rand0-next rand)))
        (mv-let (breakage-type hint-keyword-value-list)
          (break-hint-keyword-value-list-in-nth-way breakage-num hint-keyword-value-list)
          (mv breakage-type hint-keyword-value-list rand))))))

;; Returns (mv breakage-type hints rand).
(defun randomly-break-hints (hints rand)
  (declare (xargs :guard (and (true-listp hints)
                              (minstd-rand0p rand))))
  (let ((goal-hint-keyword-value-list (hint-keyword-value-list-for-goal-spec "Goal" hints)))
    (if (not (keyword-value-listp goal-hint-keyword-value-list))
        (prog2$ (er hard? 'randomly-break-hints "Bad hint for Goal: ~x0" hints)
                (mv :none nil rand))
      (mv-let (breakage-type broken-hint-keyword-value-list rand)
        (randomly-break-hint-keyword-value-list goal-hint-keyword-value-list rand)
        (if (eq :none breakage-type)
            (mv :none nil rand)
          (mv breakage-type
              (cons (cons "Goal" broken-hint-keyword-value-list)
                    (remove-hints-for-goal-spec "Goal" hints) ; removal might not be necessary, due to shadowing
                    )
              rand))))))

(defun breakable-eventp (event breakage-plan)
  (declare (xargs :guard (member-eq breakage-plan '(:all :goal-partial))))
  (if (not (and (consp event) ; must be defthm, etc.
                (<= 3 (len event))
                (keyword-value-listp (cdddr event))))
      (er hard? 'breakable-eventp "Bad advice event in ~x0." event)
    (let ((theorem-hints (cadr (assoc-keyword :hints (cdddr event)))))
      (if (not (true-listp theorem-hints))
          (er hard? 'breakable-eventp "Bad hints in ~x0: ~x1." (cadr event) theorem-hints)
        (if (null theorem-hints)
            (prog2$ (cw "Skipping ~x0 since it has no hints to remove.~%" (cadr event))
                    nil)
          (if (and (eq breakage-plan :goal-partial)
                   (null (hint-keyword-value-list-for-goal-spec "Goal" theorem-hints)))
              ;; no breakage of hints possible, given the breakage-plan (TODO: consider plans to break subgoal hints or computed hints):
              (prog2$ (cw "Skipping ~x0 since it has no hints on Goal.~%" (cadr event))
                      nil)
            t))))))

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
       ((when (not (breakable-eventp defthm breakage-plan)))
        (mv nil ; no error
            :not-attempted ; no breakage of hints possible
            t
            nil rand state))

       ;; ((when (null theorem-hints))
       ;;  (cw "Skipping ~x0 since it has no hints to remove.~%" theorem-name)
       ;;  (mv nil ; no error
       ;;      :not-attempted ; no breakage of hints possible
       ;;      t ; there were no hints (and we assume it proves without them)
       ;;      nil rand state))

       ;; ((when (and (eq breakage-plan :goal-partial)
       ;;             (null (hint-keyword-value-list-for-goal-spec "Goal" theorem-hints))))
       ;;  (cw "Skipping ~x0 since it has no hints on Goal.~%" theorem-name)
       ;;  (mv nil ; no error
       ;;      :not-attempted ; no breakage of hints possible, given the breakage-plan (TODO: consider plans to break subgoal hints or computed hints)
       ;;      t ; there were no Goal hints for us to try removing
       ;;      nil rand state))

       ;; Break the hints:
       ((mv breakage-type broken-theorem-hints rand)
        (if (eq breakage-plan :goal-partial)
            (b* ((- (cw "Removing part of the Goal hint.~%"))
                 ;; (- (cw "rand is ~x0.~%" rand))
                 ((mv breakage-type broken-theorem-hints rand) (randomly-break-hints theorem-hints rand))
                 (rand (minstd-rand0-next rand)))
              (mv breakage-type broken-theorem-hints rand))
          ;; breakage-plan must be :all:
          (prog2$ (cw "Removing all the :hints.~%")
                  (mv :all nil rand))))

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
               (- (and erp (cw "ERROR (~x0) with advice attempt for event ~X12 (continuing...).~%" erp event nil)))) ; todo: Print the error like a msg when appropriate.
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

;; Returns a list of defthm/defthmd names.
(defun breakable-theorems-to-try (events theorems-to-try breakage-plan acc)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (member-eq breakage-plan '(:all :goal-partial))
                              (true-listp acc))))
  (if (endp events)
      (reverse acc)
    (let ((event (first events)))
      (breakable-theorems-to-try (rest events)
                                 theorems-to-try
                                 breakage-plan
                                 (if (and (advice-eventp event theorems-to-try)
                                          (breakable-eventp event breakage-plan))
                                     (cons (cadr event) acc)
                                   acc)))))

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
       (state (load-port-file-if-exists (remove-lisp-suffix filename t) state)) ; this can change the current package
       ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-book filename state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp (cons nil rand) state))
       (len-all-events (len events))
       ;; (- (cw "Theorems to try: ~X01~%" theorems-to-try nil))
       (breakable-theorems-to-try (breakable-theorems-to-try events theorems-to-try breakage-plan nil))
       ((when (null breakable-theorems-to-try))
        (cw "~%SUMMARY for book ~s0: NO EVENTS TO EVALUATE.~%" filename)
        ;; (cw "Theorems to try were ~X01.~%" theorems-to-try nil)
        (mv nil ; no error, but nothing to do for this book
            (cons nil rand) state))
       ;; There is at least one breakable defthm event to try:
       (events (discard-events-after-last-advice-event events breakable-theorems-to-try)) ; todo: what if more than one theorem with the same name?  can't happen at top-level
       (- (cw "(~x0 total events, ~x1 to try, ~x2 breakable, ~x3 after discarding final events.)~%~%" len-all-events (len theorems-to-try) (len breakable-theorems-to-try) (len events)))
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
       ;; Submit all the events, trying advice for each defthm in breakable-theorems-to-try:
       ((mv erp result-alist rand state)
        (submit-events-and-eval-models events breakable-theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit server-url breakage-plan models nil rand state))
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
                                    total-book-count
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
                              (natp done-book-count)
                              (natp total-book-count))
                  :mode :program
                  :stobjs state))
  (if (endp book-to-theorems-alist)
      (progn$ (cw "~%======================================================================~%")
              (cw "~%OVERALL RESULTS (~x0 total theorems):~%" (len result-alist-acc))
              (show-model-evaluations models result-alist-acc num-recs-per-model)
              (mv nil '(value-triple :invisible) state))
    (b* ((- (cw "~%======================================================================~%"))
         (- (cw "Processing book #~x0 of ~x1.~%" (+ 1 done-book-count) total-book-count))
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
                                   base-dir num-recs-per-model print debug step-limit time-limit server-url breakage-plan models done-book-count total-book-count
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
       (- (cw "(Trying ~x0 ~s1 per model.)~%" num-recs-per-model (if (= 1 num-recs-per-model) "recommendation" "recommendations")))
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
    (eval-models-on-books-fn-aux book-to-theorems-alist base-dir num-recs-per-model print debug step-limit time-limit server-url breakage-plan models 0
                                 (len book-to-theorems-alist)
                                 nil rand state)))

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
