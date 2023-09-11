; A tool to evaluate the proof-advice-generating models
;
; Copyright (C) 2022-2023 Kestrel Institute
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
(include-book "kestrel/hints/remove-hints" :dir :system)
(include-book "kestrel/axe/merge-sort-less-than" :dir :system) ; todo: move
(include-book "kestrel/strings-light/strip-suffix-from-string" :dir :system)
(local (include-book "kestrel/axe/merge-sort-less-than-rules" :dir :system)) ; todo: move
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/make-list-ac" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; TODO: Make a code-only book for this tool, and use it instead?

;; TODO: removing :add-hyp gets us less the requested number of recs sometimes!

(local (in-theory (disable assoc-equal natp)))

(local (in-theory (enable rationalp-when-natp acl2-numberp-when-natp integerp-when-natp <=-of-0-when-0-natp)))

;; An indicator for a test, of the form (book-name theorem-name removal-type).
(defun test-infop (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= 3 (len x))
       (stringp (first x))     ; book-name
       (symbolp (second x))    ; theorem-name
       (keywordp (third x)) ; removal-type
       ))

;; The result of a model on a test, including the model name, the total number
;; of recommendations it produced, the number of the first rec that worked
;; (1-based), and the time spent trying recs in order before the first working
;; rec was found.
(defund model-resultp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= 4 (len x))
       (help::model-namep (first x))
       (natp (second x)) ; total-num-recs
       (or (null (third x)) ; first-working-rec-num-or-nil
           (posp (third x)))
       (rationalp (fourth x)) ; time-to-find-first-working-rec
       ))

(local
 (defthm consp-when-model-resultp
   (implies (model-resultp x)
            (consp x))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm natp-of-cadr-when-model-resultp
   (implies (model-resultp x)
            (natp (cadr x)))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm cddr-when-model-resultp
   (implies (model-resultp x)
            (cddr x))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm consp-of-cddr-when-model-resultp
   (implies (model-resultp x)
            (consp (cddr x)))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm cdr-when-model-resultp
   (implies (model-resultp x)
            (cdr x))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm consp-of-cdr-when-model-resultp
   (implies (model-resultp x)
            (consp (cdr x)))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm natp-of-caddr-when-model-resultp
   (implies (model-resultp x)
            (iff (natp (caddr x))
                 (caddr x)))
   :hints (("Goal" :in-theory (enable model-resultp)))))

(local
 (defthm <-of-0-of-caddr-when-model-resultp
   (implies (model-resultp x)
            (iff (< 0 (caddr x))
                 (caddr x)))
   :hints (("Goal" :in-theory (enable model-resultp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A list of model results.
;; Can be treated like an alist.
(defun model-result-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (model-resultp (first x))
         (model-result-listp (rest x)))))

(local
 (defthm alistp-when-model-result-listp
   (implies (model-result-listp x)
            (alistp x))))

(local
 (defthm model-resultp-of-assoc-equal-when-model-result-listp
   (implies (model-result-listp x)
            (iff (model-resultp (assoc-equal key x))
                 (assoc-equal key x)))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(local
 (defthm model-resultp-of-car
   (implies (model-result-listp x)
            (iff (model-resultp (car x))
                 (consp x)))
   :hints (("Goal" :in-theory (enable model-result-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun models-that-worked (model-results)
  (declare (xargs :guard (model-result-listp model-results)))
  (if (endp model-results)
      nil
    (let* ((model-result (first model-results))
           (model-name (first model-result))
           (first-working-rec-num-or-nil (third model-result)))
      (if first-working-rec-num-or-nil
          (cons model-name (models-that-worked (rest model-results)))
        (models-that-worked (rest model-results))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Maps test-infos to model-result-lists.  Each test may thus have many
;; model-results, once for each model.
(defun result-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (test-infop (car entry))
           (model-result-listp (cdr entry))
           (result-alistp (rest alist))))))

(local
 (defthm natp-of-+
   (implies (and (natp x) (natp y))
            (natp (+ x y)))))

;; todo: have defmergesort use rational-listp instead
(local
 (defthm all-rationalp-when-nat-listp
   (implies (nat-listp x)
            (all-rationalp x))
   :hints (("Goal" :in-theory (enable all-rationalp)))))

(defund all-other-models-failedp (model model-results)
  (declare (xargs :guard (and (keywordp model) ; todo: improve?
                              (model-result-listp model-results))))
  (if (endp model-results)
      t
    (let* ((model-result (first model-results))
           (this-model (first model-result))
           (first-working-rec-num-or-nil (third model-result)))
      (if (eq model this-model)
          ;; skip since we are only interested in whether other models could prove it
          (all-other-models-failedp model (rest model-results))
        (if (not first-working-rec-num-or-nil)
            ;; this model didn't prove it, so keep looking:
            (all-other-models-failedp model (rest model-results))
          ;; we've found a different model that proved it, so MODEL is not the only one:
          nil)))))

;;Returns (mv attempt-count successful-attempt-count unique-successful-attempt-count top-1-count top-10-count successful-rec-nums total-recs-produced).
(defun tabulate-resuls-for-model (model
                                  result-alist
                                  attempt-count
                                  successful-attempt-count
                                  unique-successful-attempt-count ; how many times only this model could prove a theorem
                                  top-1-count top-10-count
                                  successful-rec-nums-acc
                                  total-recs-produced)
  (declare (xargs :guard (and (keywordp model) ; todo: improve?
                              (result-alistp result-alist)
                              (natp attempt-count)
                              (natp successful-attempt-count)
                              (natp unique-successful-attempt-count)
                              (natp top-1-count)
                              (natp top-10-count)
                              (nat-listp successful-rec-nums-acc)
                              (natp total-recs-produced))
                  :guard-hints (("Goal" :expand (result-alistp result-alist)))))
  (if (endp result-alist)
      (mv attempt-count successful-attempt-count unique-successful-attempt-count top-1-count top-10-count
          (merge-sort-< successful-rec-nums-acc)
          total-recs-produced)
    (b* ((result-entry (first result-alist))
         (model-results (cdr result-entry))
         (this-model-result (assoc-eq model model-results)))
      (if (not this-model-result) ; maybe print a warning?
          (tabulate-resuls-for-model model (rest result-alist) attempt-count successful-attempt-count unique-successful-attempt-count top-1-count top-10-count successful-rec-nums-acc total-recs-produced)
        (let* ((total-recs (second this-model-result))
               (first-working-rec-num-or-nil (third this-model-result)) ; todo: also tabulate the times
               (successp first-working-rec-num-or-nil)
               (top-1 (and successp (<= first-working-rec-num-or-nil 1)))
               (top-10 (and successp (<= first-working-rec-num-or-nil 10))) ; todo: what if we don't even ask for 10, or there are not 10, or :add-hyp gets removed?
               (unique-successp (and successp
                                     (all-other-models-failedp model model-results))))
          (tabulate-resuls-for-model model (rest result-alist)
                                     (+ 1 attempt-count)
                                     (if successp (+ 1 successful-attempt-count) successful-attempt-count)
                                     (if unique-successp (+ 1 unique-successful-attempt-count) unique-successful-attempt-count)
                                     (if top-1 (+ 1 top-1-count) top-1-count)
                                     (if top-10 (+ 1 top-10-count) top-10-count)
                                     (if successp
                                         (cons first-working-rec-num-or-nil successful-rec-nums-acc)
                                       successful-rec-nums-acc)
                                     (+ total-recs total-recs-produced)
                                     ))))))

(local
 (defthm tabulate-resuls-for-model-type
   (implies (and (keywordp model) ; todo: improve?
                 (result-alistp result-alist)
                 (natp attempt-count)
                 (natp successful-attempt-count)
                 (natp unique-successful-attempt-count)
                 (natp top-1-count)
                 (natp top-10-count)
                 (nat-listp successful-rec-nums-acc)
                 (natp total-recs-produced))
            (mv-let (attempt-count successful-attempt-count unique-successful-attempt-count top-1-count top-10-count successful-rec-nums total-recs-produced)
              (tabulate-resuls-for-model model result-alist attempt-count successful-attempt-count unique-successful-attempt-count top-1-count top-10-count successful-rec-nums-acc total-recs-produced)
              (and (natp attempt-count)
                   (natp successful-attempt-count)
                   (natp unique-successful-attempt-count)
                   (natp top-1-count)
                   (natp top-10-count)
                   (nat-listp successful-rec-nums)
                   (natp total-recs-produced))))
   :hints (("Goal" :in-theory (enable tabulate-resuls-for-model)))))

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

(local
 (defthm natp-of-mv-nth-0-of-union-model-results
   (implies (and (mv-nth 0 (union-model-results model-results successful-rec-num num-recs-produced)) ; not nill
                 (or (null successful-rec-num) (natp successful-rec-num))
                 (model-result-listp model-results))
            (natp (mv-nth 0 (union-model-results model-results successful-rec-num num-recs-produced))))
   :hints (("Goal" :in-theory (enable union-model-results model-resultp)))))

(local
 (defthm natp-of-mv-nth-1-of-union-model-results
   (implies (and (natp num-recs-produced)
                 (model-result-listp model-results))
            (natp (mv-nth 1 (union-model-results model-results successful-rec-num num-recs-produced))))
   :hints (("Goal" :in-theory (enable union-model-results)))))

;; Tabulates results for a hypothetical model that combines all the models (if any can prove something, the union model can prove it).
;; Returns (mv attempt-count successful-attempt-count successful-rec-nums total-recs-produced).
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
(defund quotient-as-percent-string (numerator denominator)
  (declare (xargs :guard (and (rationalp numerator)
                              (<= 0 numerator) ; todo gen
                              (rationalp denominator)
                              (<= 0 denominator))))
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

(local
 (defthm natp-of-count-items-<=
   (implies (natp acc)
            (natp (count-items-<= items num acc)))))

;; inefficient but simple
(defun top-n-counts-aux (curr max successful-rec-nums)
  (declare (xargs :guard (and (posp curr)
                              (posp max)
                              (nat-listp successful-rec-nums))
                  :measure (nfix (+ 1 (- max curr)))))
  (if (or (not (mbt (and (posp curr)
                         (posp max))))
          (< max curr))
      nil
    (cons (count-items-<= successful-rec-nums curr 0)
          (top-n-counts-aux (+ 1 curr) max successful-rec-nums))))

(local
 (defthm nat-listp-of-top-n-counts-aux
   (nat-listp (top-n-counts-aux curr max successful-rec-nums))))

;; Returns a list (c1 c2 ... cmax) where ci indicates the number elements <= i.
(defun top-n-counts (successful-rec-nums max)
  (declare (xargs :guard (and (nat-listp successful-rec-nums) ; all positive, sorted
                              (posp max))))
  (top-n-counts-aux 1 max successful-rec-nums))

;; does not include the percent signs
(defun quotients-as-percent-strings (vals denominator)
  (declare (xargs :guard (and (nat-listp vals) ; gen
                              (rationalp denominator) ; 0 leads to a result of "undefined"
                              (<= 0 denominator))))
  (if (endp vals)
      nil
    (cons (quotient-as-percent-string (first vals) denominator)
          (quotients-as-percent-strings (rest vals) denominator))))

(local
 (defthm string-listp-of-quotients-as-percent-strings
   (string-listp (quotients-as-percent-strings vals denominator))
   :hints (("Goal" :in-theory (enable quotients-as-percent-strings)))))

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
(defun show-model-evaluation (model result-alist num-recs-per-model)
  (declare (xargs :guard (and (keywordp model) ; tweak?
                              (result-alistp result-alist)
                              (posp num-recs-per-model))))
  (b* (((mv attempt-count successful-attempt-count unique-successful-attempt-count
            & & ; top-1-count top-10-count
            successful-rec-nums
            total-recs-produced)
        (tabulate-resuls-for-model model result-alist 0 0 0 0 0 nil 0))
       (successful-attempt-percentage (quotient-as-percent-string successful-attempt-count attempt-count))
       (unique-successful-attempt-percentage (quotient-as-percent-string unique-successful-attempt-count attempt-count))
       (model-name-string (symbol-name model)) ; all uppercase, no leading colon
       (- (cw "For ~s0: ~s1% success (~x2/~x3, ~s4% unique), ~x5 total recs):~%" model-name-string successful-attempt-percentage successful-attempt-count attempt-count unique-successful-attempt-percentage total-recs-produced))
       ;; (- (cw "Nums of first successful recs: ~X01~%" successful-rec-nums nil))
       ;; (- (cw "Top-1 through top-10 counts: ~X01~%" (top-n-counts successful-rec-nums) nil))
       (- (cw "  Top-1 through top-~x0 percentages: [" num-recs-per-model))
       (- (print-separated-strings (quotients-as-percent-strings (top-n-counts successful-rec-nums num-recs-per-model) attempt-count) ", "))
       (- (cw "]~%"))
       ;; (- (cw "Top-1: ~x0 (~s1%)~%" top-1-count (quotient-as-percent-string top-1-count attempt-count)))
       ;; (- (cw "Top-10: ~x0 (~s1%)~%~%" top-10-count (quotient-as-percent-string top-10-count attempt-count)))
       )
    successful-attempt-percentage))

;; Prints result and computes a success percentage alist.
;; RESULT-ALIST is a map from (book-name, theorem-name, removal-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
(defun show-model-evaluations-aux (models result-alist num-recs-per-model)
  (if (endp models)
      nil
    (let* ((model (first models))
           (successful-attempt-percentage (show-model-evaluation model result-alist num-recs-per-model))) ; prints the info
      (acons model
             successful-attempt-percentage
             (show-model-evaluations-aux (rest models) result-alist num-recs-per-model)))))

(defun show-success-percentages (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (if (endp alist)
      nil
    (let* ((pair (first alist))
           (model (car pair))
           (percent-string (cdr pair)))
      (prog2$ (cw "~s0: ~s1%~%" (symbol-to-left-padded-string-of-length model 30) percent-string) ;todo: align better
              (show-success-percentages (rest alist))))))

;; RESULT-ALIST is a map from (book-name, theorem-name, removal-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
(defun show-model-evaluations (models result-alist num-recs-per-model)
  (b* ((alist (show-model-evaluations-aux models result-alist num-recs-per-model)) ; prints a lot
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
       (- (print-separated-strings (quotients-as-percent-strings (top-n-counts combined-successful-rec-nums num-recs-per-model) combined-attempt-count) ", "))
       (- (cw "]~%"))
       (- (cw "~%")))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun result-cachep (cache)
  (declare (xargs :guard t))
  (and (alistp cache)
       (help::recommendation-listp (strip-cars cache))
       (boolean-listp (strip-cdrs cache))))

;; Returns t, nil, or :unknown.
(defun assoc-in-result-cache (rec cache)
  (declare (xargs :guard (and (help::recommendationp rec)
                              (result-cachep cache))
                  :guard-hints (("Goal" :in-theory (enable help::recommendation-listp)))
                  ))
  (if (endp cache)
      :unknown
    (let* ((entry (first cache))
           (entry-rec (car entry)))
      (if (help::equivalent-recommendationsp rec entry-rec)
          (progn$ ;(cw "Cache hit on ~x0.~%" rec)
                  (cdr entry))
        (assoc-in-result-cache rec (rest cache))))))

;;Returns (mv erp first-working-rec-num-or-nil result-cache state).
(defun try-recs-in-order (recs rec-num theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit model result-cache state)
  (declare (xargs :guard (and (help::recommendation-listp recs)
                              (posp rec-num)
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
                              (help::model-namep model)
                              (result-cachep result-cache))
                  :mode :program ; because of help::try-recommendation
                  :stobjs state))
  (if (endp recs)
      (prog2$ (and (acl2::print-level-at-least-tp print)
                   (cw "No working rec found for ~x0.~%" model)
                   )
              (mv nil ; no error
                  nil ; no working rec found
                  result-cache
                  state))
    (b* ((rec (first recs))
         (cache-result (assoc-in-result-cache rec result-cache))
         ((when (eq t cache-result))
          (and (acl2::print-level-at-least-tp print)
               (cw "Rec #~x0 is known to work, from the cache.~%" rec-num) ; todo: print the model name.
               )
          ;; todo: maybe print it (see below)
          (mv nil ; no-error
              rec-num ; this rec is known to work
              result-cache
              state))
         ((when (eq nil cache-result))
          (and (acl2::print-level-at-least-tp print)
               (cw "Rec #~x0 is known to fail, from the cache.~%" rec-num) ; todo: print the model name.
               )
          ;; keep looking:
          (try-recs-in-order (rest recs) (+ 1 rec-num) theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit model result-cache state))
         ;; cache-result is :unknown:
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
         ((when erp) (mv erp nil result-cache state))
         (result-cache (acons rec (if maybe-successful-rec t nil) result-cache)))
      (if maybe-successful-rec
          (b* ((- (and (acl2::print-level-at-least-tp print)
                       (cw "Rec #~x0 worked.~%" rec-num) ; todo: print the model name.
                       ))
               (state (if (acl2::print-level-at-least-tp print)
                          (b* ((state (acl2::widen-margins state))
                               (- (help::show-successful-recommendation maybe-successful-rec))
                               (state (acl2::unwiden-margins state)))
                            state)
                        state))
               (- (cw "~%")))
            (mv nil ; no-error
                rec-num ; this rec worked
                result-cache
                state))
        ;; not successful, so keep looking:
        (try-recs-in-order (rest recs) (+ 1 rec-num) theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit model result-cache state)))))


;; Walks through the MODEL-REC-ALIST, evaluating, for each model, how many recs must be tried to find one that works, and how long that takes.
;; Returns (mv erp model-results state), where each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
(defun eval-model-recs (model-rec-alist ; maps model names to rec-lists
                        theorem-name
                        theorem-body
                        theorem-hints
                        theorem-otf-flg
                        current-book-absolute-path
                        print
                        debug
                        step-limit time-limit
                        model-results-acc
                        result-cache
                        state)
  (declare (xargs :guard (and (alistp model-rec-alist) ; todo: strengthen
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
                              (true-listp model-results-acc)
                              (result-cachep result-cache))
                  :stobjs state
                  :mode :program))
  (if (endp model-rec-alist)
      (mv nil ; no error
          (reverse model-results-acc)
          state)
    (b* ((entry (first model-rec-alist))
         (model (car entry))
         (recs (cdr entry)) ; todo: these are ordered, right?
         ;; Maybe print the recommendations:
         (state (if (acl2::print-level-at-least-tp print)
                    (prog2$ (cw "~%RECOMMENDATIONS FOR ~x0:~%" model)
                            (help::show-recommendations recs state))
                  state))
         ((mv start-time state) (get-cpu-time state)) ; or we could use real time (here and below)
         (- (and (acl2::print-level-at-least-tp print)
                 (cw "TRYING RECOMMENDATIONS FOR ~x0:~%" model)))
         ((mv erp first-working-rec-num-or-nil result-cache state)
          (try-recs-in-order recs 1 theorem-name theorem-body theorem-hints theorem-otf-flg current-book-absolute-path print debug step-limit time-limit model result-cache state))
         ((mv end-time state) (get-cpu-time state))
         ((when erp) (mv erp nil state)))
      (eval-model-recs (rest model-rec-alist)
                       theorem-name theorem-body theorem-hints theorem-otf-flg
                       current-book-absolute-path print debug
                       step-limit time-limit
                       (cons (list model (len recs) first-working-rec-num-or-nil (acl2::round-to-hundredths (- end-time start-time)))
                             model-results-acc)
                       result-cache
                       state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable natp))) ;todo


;; Returns (mv removal-type hint-keyword-value-list rand).
(defun randomly-break-hint-keyword-value-list (hint-keyword-value-list rand)
  (declare (xargs :guard (and (keyword-value-listp hint-keyword-value-list)
                              (minstd-rand0p rand))))
  (let* ((total-ways (num-ways-to-remove-from-hint-keyword-value-list hint-keyword-value-list)))
    (if (not (posp total-ways))
        (mv :none nil rand)
      (let* ((breakage-num (mod rand total-ways))
             (rand (minstd-rand0-next rand)))
        (mv-let (removal-type hint-keyword-value-list)
          (remove-from-hint-keyword-value-list-in-nth-way breakage-num hint-keyword-value-list)
          (mv removal-type hint-keyword-value-list rand))))))

;; Returns (mv removal-type hints rand).
(defun randomly-break-hints (hints rand)
  (declare (xargs :guard (and (true-listp hints)
                              (minstd-rand0p rand))))
  (let ((goal-hint-keyword-value-list (hint-keyword-value-list-for-goal-spec "Goal" hints))) ; todo: what if there are multiple hints on Goal (perhaps including empty ones)?
    (if (not (keyword-value-listp goal-hint-keyword-value-list))
        (prog2$ (er hard? 'randomly-break-hints "Bad hint for Goal: ~x0" hints)
                (mv :none nil rand))
      (mv-let (removal-type broken-hint-keyword-value-list rand)
        (randomly-break-hint-keyword-value-list goal-hint-keyword-value-list rand)
        (if (eq :none removal-type)
            (mv :none nil rand)
          (mv removal-type
              (cons (cons "Goal" broken-hint-keyword-value-list)
                    ;; TODO: Removing later hints on Goal could break a proof, if they would
                    ;; be used after the proof is "settled down".
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
            (prog2$ (cw "Skipping ~x0: no hints.~%" (cadr event))
                    nil)
          (if (and (eq breakage-plan :goal-partial)
                   (null (hint-keyword-value-list-for-goal-spec "Goal" theorem-hints)))
              ;; no breakage of hints possible, given the breakage-plan (TODO: consider plans to break subgoal hints or computed hints):
              (prog2$ (cw "Skipping ~x0: no hints on Goal.~%" (cadr event))
                      nil)
            t))))))

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

;; Determines which models can find advice for the given DEFTHM.  Either way, this also submits DEFTHM.
;; Returns (mv erp removal-type trivialp model-results rand state), where each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
;; Here, trivialp means "no model was needed".
;; ttodo: think about trivialp vs :not-attempted.
(defun eval-models-and-submit-defthm-event (defthm
                                            num-recs-per-model
                                            current-book-absolute-path
                                            print debug step-limit time-limit
                                            model-info-alist
                                            model-query-timeout
                                            breakage-plan ; :all means remove all hints, :goal-partial means remove part of the "Goal" hint -- todo: add more options
                                            rand state)
  (declare (xargs :guard (and (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (eq :auto step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (eq :auto time-limit)
                                  (rationalp time-limit))
                              (help::model-info-alistp model-info-alist)
                              (natp model-query-timeout)
                              (member-eq breakage-plan '(:all :goal-partial)))
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
       (- (cw "~%(Working on ~x0~%" theorem-name)) ; paren is closed on various exit branches below.
       ((when (null theorem-hints)) ; todo: this cannot happen?
        (prog2$ (cw " Skip: ~x0 has no hints to remove.)~%" theorem-name)
                (mv nil            ; no error
                    :not-attempted ; no breakage of hints possible
                    t ; trivialp (there were no hints, and we assume it proves without them))
                    nil rand state)))
       ((when (not (breakable-eventp defthm breakage-plan)))
        (prog2$ (cw "Skip: ~x0 is not breakable by ~x1.)~%" theorem-name breakage-plan)
                (mv nil    ; no error
                    :not-attempted ; no breakage of hints possible
                    t
                    nil rand state)))
       ;; ((when (and (eq breakage-plan :goal-partial)
       ;;             (null (hint-keyword-value-list-for-goal-spec "Goal" theorem-hints))))
       ;;  (cw "Skipping ~x0 since it has no hints on Goal.~%" theorem-name)
       ;;  (mv nil ; no error
       ;;      :not-attempted ; no breakage of hints possible, given the breakage-plan (TODO: consider plans to break subgoal hints or computed hints)
       ;;      t ; there were no Goal hints for us to try removing
       ;;      nil rand state))

       ;; Break the hints:
       ((mv removal-type broken-theorem-hints rand)
        (if (eq breakage-plan :goal-partial)
            (b* ((- (cw " Removing part of the Goal hint.~%"))
                 ;; (- (cw "rand is ~x0.~%" rand))
                 ((mv removal-type broken-theorem-hints rand) (randomly-break-hints theorem-hints rand))
                 (rand (minstd-rand0-next rand)))
              (mv removal-type broken-theorem-hints rand))
          ;; breakage-plan must be :all:
          (prog2$ (cw " Removing all the :hints.~%")
                  (mv :all nil rand))))
       ((when (eq :none removal-type))
        (cw " Skip: No way to break hints: ~x0).~%" theorem-hints)
        (mv nil ; no error
            :not-attempted ; no breakage of hints possible (unless we consider breaking subgoal hints or computed hints)
            t ; we found no way to break the hints, for some reason (maybe only an empty enable, or something like that)
            nil rand state))
       (- (cw "Breaking by: ~x0.~%" removal-type))
       ;; Record time and steps for the working proof (we expect the proof to always work):
       ((mv erp provedp elapsed-time prover-steps-counted state)
        ;; todo: should we do it twice, to get a more accurate time? (on the other hand,
        ;; maybe this is fair, as GC may also occur while we are trying a rec,
        ;; causing us to lose).
        (prove$-nice-with-time-and-steps theorem-body
                                         theorem-hints
                                         nil ;instructions -- todo skip if these are present (maybe it will have no hints, so we do)
                                         theorem-otf-flg ;todo: think about this
                                         nil ; no time-limit
                                         nil ; no step-limit
                                         state))
       ((when (or erp
                  (not provedp)))
        (cw " ERROR: Failed to prove original theorem!: ~x0).~%" theorem-name)
        (mv nil ; we suppress the error, so we can continue
            :not-attempted
            t ;todo: think about this
            nil rand state))
       ;; Try the proof with the broken hints (usually will fail, yielding checkpoints):
       ;; TODO: Skip if this hit a limit?
       ((mv erp provedp & checkpoint-clauses-top checkpoint-clauses-non-top state)
        (help::try-proof-and-get-checkpoint-clauses theorem-name
                                                    theorem-body
                                                    (acl2::translate-term theorem-body 'eval-models-and-submit-defthm-event (w state))
                                                    broken-theorem-hints
                                                    theorem-otf-flg ; or use nil ?
                                                    ;; We have to use some limits here, to avoid runaway proofs, but we hope that
                                                    ;; these limits will rarely apply (they might mess up the checkpoints?):
                                                    ;; todo: are the 10000 and the 5 comparable?
                                                    (+ 100000 (* 10 prover-steps-counted))
                                                    (+ 1 (* 10 elapsed-time))
                                                    t ; suppress-trivial-warningp
                                                    state))
       ((when erp) (prog2$ (cw " ERROR: ~x0.)~%" erp)
                           (mv erp nil nil nil rand state)))
       ((when provedp)
        (b* ((- (cw " Skip: Broken hints worked for ~x0)~%" theorem-name)) ;todo: tabulate these
             ((mv erp state) ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event `(skip-proofs ,defthm) nil nil state))
             ((when erp) (mv erp nil nil nil rand state)))
          (mv nil ; no error
              removal-type
              t   ; theorem was trivial (no hints needed)
              nil
              rand
              state)))
       ;; Breaking the hints did break the theorem, yielding checkpoints:
       (- (cw " ~x0 top-level ~s1.~%" (len checkpoint-clauses-top) (if (= 1 (len checkpoint-clauses-top)) "checkpoint" "checkpoints")))
       (- (cw " ~x0 non-top-level ~s1.~%" (len checkpoint-clauses-non-top) (if (= 1 (len checkpoint-clauses-non-top)) "checkpoint" "checkpoints")))
       ;; Try all the models, except :add-hyp (todo: a general way to say which models change the theorem?!):
       (disallowed-rec-types '(:add-hyp))  ;exclude :add-hyp
       (step-limit-for-tries (if (null step-limit)
                                 nil
                               (if (eq :auto step-limit)
                                   (+ 100000 (* 3 prover-steps-counted))
                                 step-limit)))
       (time-limit-for-tries (if (null time-limit)
                                 nil
                               (if (eq :auto time-limit)
                                   (+ 1 (* 3 elapsed-time))
                                 time-limit)))
       ;; Get recommendations from all the models:
       ((mv erp model-rec-alist state) ; todo: should an error count against the model that caused it?
        (help::get-recs-from-models model-info-alist
                                    num-recs-per-model
                                    disallowed-rec-types
                                    checkpoint-clauses-top
                                    checkpoint-clauses-non-top
                                    theorem-body ; todo: put earlier
                                    ;; the presumed broken-theorem:
                                    `(defthm ,theorem-name
                                       ,theorem-body
                                       ,@(and theorem-otf-flg `(:otf-flg ,theorem-otf-flg))
                                       ,@(and broken-theorem-hints `(:hints ,broken-theorem-hints)))
                                    model-query-timeout debug print nil state))
       ((when erp) (mv erp nil nil nil rand state))
       ;; Try all the recs and record which ones worked:
       ((mv erp model-results state) ; each of the model-results is of the form (<model> <total-num-recs> <first-working-rec-num-or-nil> <total-time>).
        (eval-model-recs model-rec-alist
                         theorem-name theorem-body broken-theorem-hints theorem-otf-flg
                         current-book-absolute-path print debug
                         step-limit-for-tries time-limit-for-tries
                         nil ; empty acc
                         nil ; empty result-cache
                         state))
       ((when erp) (mv erp nil nil nil rand state)) ; todo: should an error count against the model(s) whose rec caused it?
       (models-that-worked (models-that-worked model-results))
       (- (cw "~% For ~x0, ~x1 models worked: ~X23.~%" theorem-name (len models-that-worked) models-that-worked nil))
       (- (cw "Broken hints were: ~X01.~%" broken-theorem-hints nil)) ; todo: highlight what was removed
       (- (cw "Actual hints were: ~X01.~%" theorem-hints nil))
           ;; Submit the event, so we can process further events (we use
           ;; skip-proofs for speed, but see the attachment to
           ;; always-do-proofs-during-make-event-expansion below):
       ((mv erp state)
        (submit-event `(skip-proofs ,defthm) nil nil state))
       ((when erp) (mv erp nil nil nil rand state))
       (- (cw ")~%")))
    (mv nil ; no error
        removal-type
        nil ; not trivial
        model-results
        rand
        state)))

;; Returns (mv erp result-alist rand state), where RESULT-ALIST is a map from (book-name, theorem-name, removal-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
;throws an error if any event fails
(defun submit-events-and-eval-models (events theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan result-alist-acc rand state)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (eq :auto step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (eq :auto time-limit)
                                  (rationalp time-limit))
                              (help::model-info-alistp model-info-alist)
                              (natp model-query-timeout)
                              (member-eq breakage-plan '(:all :goal-partial))
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
               ((mv erp removal-type trivialp model-results rand state)
                (eval-models-and-submit-defthm-event event num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan rand state))
               (- (and erp (cw "ERROR (~x0) with advice attempt for event ~X12 (continuing...).~%" erp event nil)))) ; todo: Print the error like a msg when appropriate.
            (if erp
                ;; If there is an error, the result is meaningless.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                (b* (((mv erp state)
                      (submit-event `(skip-proofs ,event) nil nil state))
                     ((when erp)
                      (er hard? 'submit-events-and-eval-models "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                      (mv erp nil rand state)))
                  (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan result-alist-acc rand state))
              (if trivialp
                  ;; If the theorem is trivial, no useful information is returned.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                  (b* (((mv erp state)
                        (submit-event `(skip-proofs ,event) nil nil state))
                       ((when erp)
                        (er hard? 'submit-events-and-eval-models "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                        (mv erp nil rand state)))
                    (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan result-alist-acc rand state))
                ;; No error, so count the result:
                (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan
                                               (acons (list current-book-absolute-path ; todo: use a relative path?
                                                            (cadr event) ; theorem-name
                                                            removal-type)
                                                      model-results
                                                      result-alist-acc)
                                               rand
                                               state))))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event `(skip-proofs ,event) nil nil state))
             ;; FIXME: Anything that tries to read from a file will give an error since the current dir won't be right.
             ((when erp)
              (cw "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp nil rand state))
             (- (and (acl2::print-level-at-least-tp print) (cw "~x0~%" (shorten-event event)))))
          (submit-events-and-eval-models (rest events) theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan result-alist-acc rand state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads and then submits all the events in FILENAME, trying advice for the theorems indicated by THEOREMS-TO-TRY.
;; Returns (mv erp result-alist+rand state), where RESULT-ALIST+RAND is a cons of RESULT-ALIST and RAND, and where RESULT-ALIST is a map from (book-name, theorem-name, removal-type) to lists of (model, total-num-recs, first-working-rec-num-or-nil, time-to-find-first-working-rec).
;; Since this returns an error triple, it can be wrapped in revert-world.
;; Example: (eval-models-on-book "expt.lisp" :all 10 t nil 10000 5 (help::make-model-info-alist :all (w state)) 10000 :all 1 state)
(defun eval-models-on-book (filename ; the book, with .lisp extension, we should have already checked that it exists
                            theorems-to-try
                            num-recs-per-model
                            print
                            debug step-limit time-limit
                            model-info-alist
                            model-query-timeout
                            breakage-plan
                            rand
                            state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (booleanp debug)
                              (or (null step-limit)
                                  (eq :auto step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (eq :auto time-limit)
                                  (rationalp time-limit))
                              (help::model-info-alistp model-info-alist)
                              (natp model-query-timeout)
                              (member-eq breakage-plan '(:all :goal-partial)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* ( ;; We must avoid including the current book (or an other book that includes it) when trying to find advice:
       (current-book-absolute-path (canonical-pathname filename nil state))
       ((when (member-equal current-book-absolute-path
                            (all-included-books (w state))))
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
       ((mv erp state) (submit-event '(defattach (acl2::always-do-proofs-during-make-event-expansion acl2::constant-t-function-arity-0) :system-ok t) nil nil state))
       ((when erp) (mv erp (cons nil rand) state))
       ;; Submit all the events, trying advice for each defthm in breakable-theorems-to-try:
       ((mv erp result-alist rand state)
        (submit-events-and-eval-models events breakable-theorems-to-try num-recs-per-model current-book-absolute-path print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan nil rand state))
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
;; Returns (mv erp state).
(defun eval-models-on-books (book-to-theorems-alist
                             base-dir
                             num-recs-per-model
                             print
                             debug step-limit time-limit
                             model-info-alist model-query-timeout breakage-plan
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
                                  (eq :auto step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (eq :auto time-limit)
                                  (rationalp time-limit))
                              (help::model-info-alistp model-info-alist)
                              (natp model-query-timeout)
                              (member-eq breakage-plan '(:all :goal-partial))
                              (alistp result-alist-acc)
                              (natp done-book-count)
                              (natp total-book-count))
                  :mode :program
                  :stobjs state))
  (if (endp book-to-theorems-alist)
      (progn$ (cw "~%======================================================================~%")
              (cw "~%OVERALL RESULTS (~x0 total theorems):~%" (len result-alist-acc))
              (show-model-evaluations (strip-cars model-info-alist) result-alist-acc num-recs-per-model)
              (mv nil state))
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
                                             model-info-alist model-query-timeout breakage-plan
                                             rand
                                             state)))
         (result-alist-for-book (car result-alist-for-book+rand))
         (rand (cdr result-alist-for-book+rand))
         (- (and erp (cw "WARNING: Error replaying ~x0.~%" book)))
         (done-book-count (+ 1 done-book-count))
         (result-alist-acc (append result-alist-for-book result-alist-acc))
         (- (progn$ (cw "~%~%Results after ~x0 books:~%" done-book-count)
                    (show-model-evaluations (strip-cars model-info-alist) result-alist-acc num-recs-per-model) ; todo: optimize?
                    ))
         ;;            (cw "ADVICE FOUND    : ~x0~%" yes-count)
         ;;            (cw "NO ADVICE FOUND : ~x0~%" no-count)
         ;;            ;; (cw "ADD HYP ADVICE FOUND : ~x0~%" maybe-count)
         ;;            (cw "NO HINTS NEEDED : ~x0~%" trivial-count)
         ;;            (cw "ERROR           : ~x0~%~%" error-count)))
         )
      (eval-models-on-books (rest book-to-theorems-alist)
                            base-dir num-recs-per-model print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan done-book-count total-book-count
                            result-alist-acc
                            rand
                            state))))

;; Evaluate all of the MODELS on some or all of the TESTS.  This groups the tests by book for efficiency.
;; Returns (mv erp event state).
(defun eval-models-on-tests-fn (tests base-dir num-recs-per-model excluded-prefixes seed print debug step-limit time-limit model-query-timeout breakage-plan models num-tests state)
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
                                  (eq :auto step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (eq :auto time-limit)
                                  (rationalp time-limit))
                              (natp model-query-timeout)
                              (member-eq breakage-plan '(:all :goal-partial))
                              (or (eq :all models)
                                  (eq :non-ml models)
                                  (help::model-namep models) ; special case for a single model
                                  (help::model-namesp models))
                              (or (eq :all num-tests)
                                  (natp num-tests)))
                  :mode :program
                  :stobjs state))
  (b* ( ;; Elaborate options:
       (model-info-alist (help::make-model-info-alist models (w state)))
       ;; make it an absolute path (better way to do this?):
       (base-dir (canonical-pathname base-dir t state))
       ((when (not base-dir))
        (er hard? 'eval-models-on-tests-fn "ERROR: Dir ~x0 not found." base-dir)
        (mv t nil state))
       (base-dir (strip-suffix-from-string "/" base-dir))
       (- (cw "base-dir is ~s0.~%" base-dir))
       ;; Initialize the source of randomness:
       ((mv rand state)
        (if (eq :random seed)
            (random$ *m31* state)
          (mv seed state)))
       (- (cw "(Using random seed of ~x0.)~%" rand))
       (- (cw "(Using breakage-plan ~x0.)~%" breakage-plan))
       (- (cw "(Trying ~x0 ~s1 per model.)~%" num-recs-per-model (if (= 1 num-recs-per-model) "recommendation" "recommendations")))
       (tests (clear-keys-with-matching-prefixes tests excluded-prefixes nil))
       (len-tests (len tests))
       ((when (and (not (eq :all num-tests))
                   (> num-tests len-tests)))
        (mv :not-enough-tests nil state))
       ;; Choose which tests to use:
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
       (- (cw "(Processing ~x0 tests in ~x1 books.)~%" num-tests (len book-to-theorems-alist)))
       (state (acl2::widen-margins state))
       ((mv erp state)
        (eval-models-on-books book-to-theorems-alist base-dir num-recs-per-model print debug step-limit time-limit model-info-alist model-query-timeout breakage-plan 0
                              (len book-to-theorems-alist)
                              nil rand state))
       (state (acl2::unwiden-margins state)))
    (mv erp '(value-triple :invisible) state)))

;; TODO: Record the kinds of recs that work (note that names may get combined with /)?
;; TODO: Record the sources of recs that work (note that names may get combined with /)?
;; TODO: Record how often any model works.
;; TODO: Record the time taken to find the first result.
;; TODO: Determine which models solve problems on which most or all other models fail.
;; TODO: Delete only parts of hints, like Matt's tool does.
;; Rec names should not include slash or digits?
(defmacro eval-models-on-tests (tests ; pairs of the form (book-name . theorem-name) where book-names are relative to BASE-DIR and have the .lisp extension
                                base-dir               ; no trailing slash
                                &key
                                (excluded-prefixes 'nil) ; relative to BASE-DIR
                                (seed ':random)
                                (model-query-timeout '40) ; for both connection timeout and read timeout
                                (breakage-plan ':goal-partial)
                                (models ':all)    ; which ML models to use
                                (num-tests ':all) ; how many books to evaluate (TODO: Better to chose a random subset of theorems, rather than books?)
                                (print 'nil)
                                (debug 'nil)
                                (step-limit ':auto)
                                (time-limit ':auto)
                                (num-recs-per-model '20))
  `(make-event (eval-models-on-tests-fn ,tests ,base-dir ,num-recs-per-model ,excluded-prefixes ,seed ,print ,debug ,step-limit ,time-limit ,model-query-timeout ,breakage-plan ,models ,num-tests state)))
