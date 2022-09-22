; A tool to get proof advice from a server over the web
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; SETUP:
;;
;; 1. Set the ACL2_ADVICE_SERVER environment variable to the server URL (often
;; ends in '/machine_interface')
;;
;; 2. When using this tool, consider doing (adjust-ld-history t state) so
;; that the advice tool can give advice even when the failing theorem is not
;; the most recent event.

;; TODO: Add filtering of unhelpful recommendations:
;; - (maybe) skip use-lemma when the rule had nothing to do with the goal
;; - skip add-disable-hint when the rule is already disabled (or not present?)
;; - skip add-hyp when cgen can falsify the theorem even with the hyp
;; - skip add-library when already present
;; - skip :hints that are already present or subsumed by ones already present
;; - (maybe) skip :hints that conflict with ones already present (e.g., :induct, enable vs and explicit disable)
;; - avoid anything except add-hyp when cgen can falsify the theorem (can't possibly fix the problem)
;; - (maybe) try to avoid theory-invariant errors/warnings
;; - (maybe) try to help clean up hyps (e.g., replacing a subsumed hyp when add-hyp strengthens one, maybe using tau)
;; - avoid both add-enable-hint and use-lemma of the same rule
;; - what else?

;; TODO: Maybe add a time limit for trying recommendations and keep trying more and
;; more until that limit is reached.

;; TODO: Group recommendations that need the same supporting book to be
;; included, to avoid re-including the same book later.

;; TODO: Incorporate cgen to try to see if the theorem is valid or not.  If not
;; valid, only add-hyp can help.

;; TODO: Why does getting advice take ~3 seconds?

;; TODO: Allow doing :rec <n> to try recommendation <n>

;; TODO: Consider trying the advice on the checkpoint(s), not just the goal.

;; TODO: Print times to try the recs.  Keep track of which gives the quickest proof.

;; TODO: Turn off redef (if not), to avoid prompts when including books with name clashes

;; TODO: Avoid including books that are known to be slow?

;; TODO: Avoid illegal hints, such as adding a :by when there is already a :use, or vice versa

;; TODO: Untranslate before printing (e.g., hyps)?

(include-book "kestrel/utilities/checkpoints" :dir :system)
(include-book "kestrel/utilities/nat-to-string" :dir :system)
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/prove-dollar-plus" :dir :system)
(include-book "kestrel/utilities/read-string" :dir :system) ; todo: slowish
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/world-light/defined-fns-in-term" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/typed-lists-light/string-list-listp" :dir :system)
(include-book "kestrel/alists-light/string-string-alistp" :dir :system)
(include-book "kestrel/htclient/post" :dir :system) ; todo: slow
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/big-data/packages" :dir :system) ; try to ensure all packages that might arise are known ; todo: very slow
(include-book "tools/prove-dollar" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/utilities/coerce" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/utilities/margins" :dir :system))

;; ;; Returns all disabled runes associate with NAME.
;; ;; Like disabledp but hygienic, also doesn't end in "p" since not a predicate.
;; (defun disabled-runes (name ens wrld)
;;   (declare (xargs :mode :program))
;;   (disabledp-fn name ens wrld))

(defconst *step-limit* 100000)

;; If NAME is a macro-alias, return what it represents.  Otherwise, return NAME.
;; TODO: Compare to (deref-macro-name name (macro-aliases wrld)).
(defund handle-macro-alias (name wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (not (symbolp name)) ; possible?
      name
    (let* ((macro-aliases-table (table-alist 'macro-aliases-table wrld)))
      (if (not (alistp macro-aliases-table))
          (er hard? 'handle-macro-alias "Bad macro aliases table.")
        (let ((res (assoc-eq name macro-aliases-table)))
          (if res
              (if (symbolp (cdr res))
                  (cdr res)
                (er hard? 'handle-macro-alias "Bad macro aliases table."))
            name))))))

(local (in-theory (disable state-p
                           checkpoint-list-guard
                           global-table
                           put-global
                           get-global
                           global-table-p
                           set-fmt-hard-right-margin
                           deref-macro-name)))

(defund widen-margins (state)
  (declare (xargs :stobjs state))
  (let* ((old-fmt-hard-right-margin (f-get-global 'fmt-hard-right-margin state))
         (old-fmt-soft-right-margin (f-get-global 'fmt-soft-right-margin state))
         ;; save the old values for later restoration:
         (state (f-put-global 'old-fmt-hard-right-margin old-fmt-hard-right-margin state))
         (state (f-put-global 'old-fmt-soft-right-margin old-fmt-soft-right-margin state))
         ;; Change the margins
         (state (set-fmt-hard-right-margin 410 state))
         (state (set-fmt-soft-right-margin 400 state)))
    state))

;; Same as in centaur/fty.
(defun pos-fix (x) (declare (xargs :guard t)) (if (posp x) x 1))

(defund unwiden-margins (state)
  (declare (xargs :stobjs state
                  :guard-hints (("Goal" :in-theory (enable boundp-global)))))
  ;; Restore the margins:
  (let* ((state (if (boundp-global 'old-fmt-hard-right-margin state)
                    (set-fmt-hard-right-margin (pos-fix (f-get-global 'old-fmt-hard-right-margin state)) state)
                  state))
         (state (if (boundp-global 'old-fmt-soft-right-margin state)
                    (set-fmt-soft-right-margin (pos-fix (f-get-global 'old-fmt-soft-right-margin state)) state)
                  state)))
    state))

;move
;; TODO: What kinds of things can ITEM be?  A runic-designator?  A theory?
(defund item-that-can-be-enabled/disabledp (item wrld)
  (declare (xargs :guard (and ;; (symbolp item)
                          (plist-worldp wrld)
                          (alistp (macro-aliases wrld)))
                  :verify-guards nil
                  ))
  (if (symbolp item)
      (let ((name (deref-macro-name item (macro-aliases wrld)))) ; no change if item is not a macro name
        (if (getpropc name 'runic-mapping-pairs nil wrld)
            t
          nil))
    (if (runep item wrld)
        t
      (cw "NOTE: Unknown kind of item: ~x0." item))))

;; Returns (mv erp lists)
;; Map parsed-json-array->values over a list.
(defun json-arrays-to-lists (arrays acc)
  (declare (xargs :guard (and (parsed-json-array-listp arrays)
                              (true-listp acc))))
  (if (endp arrays)
      (mv nil (reverse acc))
    (let ((array (first arrays)))
      (if (not (parsed-json-arrayp array)) ;drop?
          (mv t nil)
        (json-arrays-to-lists (rest arrays)
                              (cons (parsed-json-array->values array)
                                    acc))))))

;; (defun untranslate-list (terms iff-flg wrld)
;;   (declare (xargs :mode :program))
;;   (if (endp terms)
;;       nil
;;     (cons (untranslate (first terms) iff-flg wrld)
;;           (untranslate-list (rest terms) iff-flg wrld))))

;; (defun untranslate-clauses (clauses iff-flg wrld)
;;   (declare (xargs :mode :program))
;;   (if (endp clauses)
;;       nil
;;     (cons (untranslate-list (first clauses) iff-flg wrld)
;;           (untranslate-clauses (rest clauses) iff-flg wrld))))

(defun make-numbered-checkpoint-entries (current-number checkpoints)
  (declare (xargs :mode :program)) ; because we call fms-to-string
  (if (endp checkpoints)
      nil
    (acons (concatenate 'string "checkpoint_" (nat-to-string current-number))
           (fms-to-string "~X01" (acons #\0 (first checkpoints) (acons #\1 nil nil)))
           (make-numbered-checkpoint-entries (+ 1 current-number) (rest checkpoints)))))

(defconst *rec-to-symbol-alist*
  '(("add-by-hint" . :add-by-hint)
    ("add-cases-hint" . :add-cases-hint)
    ("add-disable-hint" . :add-disable-hint)
    ("add-do-not-hint" . :add-do-not-hint)
    ("add-enable-hint" . :add-enable-hint)
    ("add-expand-hint" . :add-expand-hint)
    ("add-hyp" . :add-hyp)
    ("add-induct-hint" . :add-induct-hint)
    ("add-library" . :add-library)
    ("add-nonlinearp-hint" . :add-nonlinearp-hint)
    ("add-use-hint" . :add-use-hint)
    ("use-lemma" . :use-lemma)))

(defconst *rec-types* (strip-cdrs *rec-to-symbol-alist*))

;; todo: strengthen
(defun recommendationp (rec)
  (declare (xargs :guard t))
  (and (true-listp rec)
       (= 6 (len rec))
       (let ((name (nth 0 rec))
             (type (nth 1 rec))
             ;; (object (nth 2 rec))
             (confidence-percent (nth 3 rec))
             ;; (book-map (nth 4 rec))
             ;; this (possibly) gets populated when we try the rec:
             ;; todo: consider :unknown until we decide if any include-books are needed
             (pre-commands (nth 5 rec)))
         (and (stringp name)
              (member-eq type *rec-types*)
              ;; object
              (and (rationalp confidence-percent)
                   (<= 0 confidence-percent)
                   (<= confidence-percent 100))
              ;; book-map
              (true-listp pre-commands)))))

(defun make-rec (name type object confidence-percent book-map pre-commands)
  (declare (xargs :guard t)) ; todo: strengthen
  (list name type object confidence-percent book-map pre-commands))

(defund update-pre-commands (pre-commands rec)
  (declare (xargs :guard (recommendationp rec)))
  (append (take 5 rec)
          (list pre-commands)))

(defund update-rec-type (new-type rec)
  (declare (xargs :guard (recommendationp rec)))
  (cons (nth 0 rec)
        (cons new-type
              (cddr rec))))

(defun show-recommendation (rec)
  (declare (xargs :guard (recommendationp rec)))
  (let* ((name (nth 0 rec))
         (type (nth 1 rec))
         (object (nth 2 rec))
         (confidence-percent (nth 3 rec))
         ;; (book-map (car (nth 4 rec)))
         ;; (pre-commands (nth 5 rec)) ; not present at this point
         )
    (cw "~s0: Try ~x1 with ~x2 (conf: ~x3%).~%" name type object (floor confidence-percent 1))))

(defun recommendation-listp (recs)
  (declare (xargs :guard t))
  (if (atom recs)
      (null recs)
    (and (recommendationp (first recs))
         (recommendation-listp (rest recs)))))

(defun show-recommendations-aux (recs)
  (declare (xargs :guard (recommendation-listp recs)))
  (if (endp recs)
      nil
    (prog2$ (show-recommendation (first recs))
            (show-recommendations-aux (rest recs)))))

;; Returns state.
(defun show-recommendations (recs state)
  (declare (xargs :guard (recommendation-listp recs)
                  :stobjs state))
  (let ((state (widen-margins state)))
    (progn$ (show-recommendations-aux recs)
            (let ((state (unwiden-margins state)))
              state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *option-names* '(:max-wins))

;; Returns (mv presentp val)
(defund get-advice-option (option-name wrld)
  (declare (xargs :guard (and (symbolp option-name)
                              (plist-worldp wrld))
                  :verify-guards nil))
  (let* ((table-alist (table-alist 'advice-options wrld))
         (res (assoc-eq option-name table-alist)))
    (if res (mv t (cdr res)) (mv nil nil))))

;; Returns the value of the option.  Throws an error if not set.
(defund get-advice-option! (option-name wrld)
  (declare (xargs :guard (and (symbolp option-name)
                              (plist-worldp wrld))
                  :verify-guards nil))
  (mv-let (presentp val)
    (get-advice-option option-name wrld)
    (if (not presentp)
        (er hard? 'get-advice-option! "Option value not set: ~x0." option-name)
      val)))

(defund advice-option-fn (option-name rest-args wrld)
  (declare (xargs :guard (and (symbolp option-name)
                              (plist-worldp wrld))
                  :verify-guards nil))
  (if (not (member-eq option-name *option-names*))
      (er hard? 'advice-option-fn "Unknown option: ~x0." option-name)
    (if (consp rest-args)
        ;; It's a set:
        (let ((option-val (first rest-args)))
          `(table advice-options ,option-name ,option-val))
      ;; It's a get:
      (let ((val (get-advice-option! option-name wrld)))
        (prog2$ (cw "~x0~%" val)
                '(value-triple :invisible))))))

;; Examples:
;; (advice-option <name>) ;; print the value of the given option
;; (advice-option <name> <val>) ;; set the value of the given option
(defmacro advice-option (option-name &rest rest-args)
  `(make-event-quiet (advice-option-fn ,option-name ',rest-args (w state))))

(advice-option :max-wins nil) ; don't limit the number of successes before we stop trying recs

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund drop-initial-newline (str)
  (declare (xargs :guard (stringp str)))
  (let ((chars (coerce str 'list)))
    (if (and (consp chars)
             (eql #\newline (first chars)))
        (coerce (rest chars) 'string)
      str)))

(defmacro fms-to-string-one-line (&rest args)
  `(drop-initial-newline ; work around problem with fms-to-string
    (fms-to-string ,@args :fmt-control-alist '((fmt-soft-right-margin . 10000)
                                               (fmt-hard-right-margin . 10000)))))

(defun show-successful-recommendation (rec)
  (declare (xargs :guard (recommendationp rec)
                  :mode :program ; because of fms-to-string
                  ))
  (let* (;; (name (nth 0 rec))
         (type (nth 1 rec))
         (object (nth 2 rec))
         ;; (confidence-percent (nth 3 rec))
         ;; (book-map (car (nth 4 rec)))
         (pre-commands (nth 5 rec))
         (english-rec (case type
                        (:add-cases-hint (fms-to-string-one-line ":cases ~x0" (acons #\0 object nil)))
                        (:add-disable-hint (fms-to-string-one-line "disabling ~x0" (acons #\0 object nil)))
                        (:add-do-not-hint (fms-to-string-one-line ":do-not ~x0" (acons #\0 object nil)))
                        ;; Same handling for both:
                        ((:add-enable-hint :use-lemma) (fms-to-string-one-line "enabling ~x0" (acons #\0 object nil)))
                        (:add-expand-hint (fms-to-string-one-line ":expand ~x0" (acons #\0 object nil)))
                        (:add-hyp (fms-to-string-one-line "adding the hyp ~x0" (acons #\0 object nil)))
                        (:add-induct-hint (fms-to-string-one-line ":induct ~x0" (acons #\0 object nil)))
                        (:add-library (fms-to-string-one-line "~x0" (acons #\0 object nil)))
                        (:add-nonlinearp-hint (fms-to-string-one-line ":nonlinearp ~x0" (acons #\0 object nil)))
                        (:add-use-hint (fms-to-string-one-line ":use ~x0" (acons #\0 object nil)))
                        (:exact-hints (fms-to-string-one-line ":hints ~x0" (acons #\0 object nil)))
                        (t (er hard? 'show-successful-recommendation "Unknown rec type: ~x0." type)))))
    (if (and pre-commands
             (not (eq :unknown pre-commands)) ; todo: eventually eliminate this
             )
        (if (consp (cdr pre-commands))
            ;; More than one pre-command:
            (cw "~s0, after doing ~&1~%" english-rec pre-commands)
          ;; Exactly one pre-command:
          (cw "~s0, after doing ~x1~%" english-rec (first pre-commands)))
      (cw "~s0~%" english-rec))))

(defun show-successful-recommendations-aux (recs)
  (declare (xargs :mode :program))
  (declare (xargs :guard (recommendation-listp recs)))
  (if (endp recs)
      nil
    (let ((rec (first recs)))
      (progn$ (cw "~S0: " (nth 0 rec))
              (show-successful-recommendation rec)
              (show-successful-recommendations-aux (rest recs))))))

;; Returns state.
(defun show-successful-recommendations (recs state)
  (declare (xargs :mode :program ;todo
                  :stobjs state))
  (let ((state (widen-margins state)))
    (progn$ (show-successful-recommendations-aux recs)
            (cw "~%")
            (let ((state (unwiden-margins state)))
              state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp form state).
(defund parse-include-book (string state)
  (declare (xargs :guard (stringp string)
                  :stobjs state))
  (b* (((mv erp form state) (read-string-as-single-item string state)) ; todo: what about packages?
       ((when erp) (mv :error-parsing-include-book nil state))
       ((when (not (and (consp form)
                        (consp (cdr form))
                        (eq 'include-book (car form))
                        (stringp (cadr form))
                        ;; incomplete check, as there may be a :dir
                        )))
        (mv :error-parsing-include-book nil state)))
    (mv nil form state)))

;; Returns (mv erp list state).
(defund parse-book-map-info-list (list acc state)
  (declare (xargs :guard (and (string-listp list)
                              (true-listp acc))
                  :stobjs state))
  (if (endp list)
      (mv nil (reverse acc) state)
    (let ((item (first list)))
      (if (equal item ":BUILTIN")
          (parse-book-map-info-list (rest list)
                                     (cons :builtin acc)
                                     state)
        ;; otherwise, it should be an include-book:
        (b* (((mv erp include-book-form state)
              (parse-include-book item state))
             ((when erp) (mv erp nil state)))
          (parse-book-map-info-list (rest list)
                                     (cons include-book-form acc)
                                     state))))))

(defthm true-listp-of-mv-nth-1-of-parse-book-map-info-list
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (parse-book-map-info-list list acc state))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-book-map-info-list))))

;; Returns (mv erp lists state) where each of the LISTS is a list of include-book forms, or the special value :builtin.
(defund parse-book-map-info-lists (lists acc state)
  (declare (xargs :guard (and (string-list-listp lists)
                              (true-listp acc))
                  :stobjs state))
  (if (endp lists)
      (mv nil (reverse acc) state)
    (b* (((mv erp list state) (parse-book-map-info-list (first lists) nil state))
         ((when erp) (mv erp nil state))
         (- (and (member-eq :builtin list)
                 (not (= 1 (len list)))
                 ;; (er hard? 'parse-book-map-info-lists "Bad book-map-info: ~x0, which parsed to ~x1." (first lists) list)
                 ;; (cw "WARNING: Bad book-map-info: ~x0, which parsed to ~x1." (first lists) list) ;todo: put back
                 ))
         (list (if (member-eq :builtin list)
                   :builtin
                 list)))
      (parse-book-map-info-lists (rest lists) (cons list acc) state))))

(defthm true-listp-of-mv-nth-1-of-parse-book-map-info-lists
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (parse-book-map-info-lists lists acc state))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-book-map-info-lists))))

;; returns (mv erp parsed-book-map state)
(defund parse-book-map (book-map state)
  (declare (xargs :stobjs state))
  (if (not (parsed-json-objectp book-map))
      (mv :ill-formed-book-map nil state)
    (b* ((dict (parsed-json-object->pairs book-map)) ; strip the :object
         (keys (strip-cars dict))
         ((when (not (string-listp keys))) (mv :ill-formed-book-map nil state))
         (vals (strip-cdrs dict))
         ((when (not (parsed-json-array-listp vals))) (mv :ill-formed-book-map nil state))
         ((mv erp syms state) (read-strings-as-single-symbols keys nil state))
         ((when erp) (mv erp nil state))
         ((mv erp lists) (json-arrays-to-lists vals nil))
         ((when erp) (mv erp nil state))
         ((when (not (string-list-listp lists))) (mv :ill-formed-book-map nil state))
         ((mv erp
              book-lists-for-keys ; each is a list of include-book-forms or :builtin
              state)
          (parse-book-map-info-lists lists nil state))
         ((when erp) (mv erp nil state)))
      (mv nil (pairlis$ syms book-lists-for-keys) state))))

(defund round-to-hundredths (x)
  (declare (xargs :guard (rationalp x)))
  (/ (floor (* x 100) 1)
     100))

;; Returns (mv erp parsed-recommendation state) where parsed-recommendation may be :none.
(defund parse-recommendation (rec rec-num state)
  (declare (xargs :guard (and (parsed-json-valuep rec)
                              (natp rec-num))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable parsed-json-objectp)))))
  (if (not (parsed-json-objectp rec))
      (progn$ (er hard? 'parse-recommendation "Bad rec: ~x0." rec)
              (mv :bad-rec nil state))
    (b* ((dict (parsed-json-object->pairs rec)) ; strip the :object
         (type (lookup-equal "type" dict))
         (object (lookup-equal "object" dict))
         (confidence (lookup-equal "confidence" dict))
         (book-map (lookup-equal "book_map" dict))
         ((mv erp book-map state) (parse-book-map book-map state))
         ((when erp)
          (if (stringp erp)
              (cw "WARNING: When parsing book map: ~s0.~%" erp)
            (cw "WARNING: When parsing book map: ~x0.~%" erp))
          (mv nil ; supressing this error for now
              :none state))
         (confidence (rfix confidence)) ; for guards
         ((when (or (< confidence 0)
                    (< 1 confidence)))
          (er hard? 'parse-recommendation "Bad confidence: ~x0." confidence)
          (mv :bad-confidence nil state))
         (confidence-percent (round-to-hundredths (* 100 confidence)))
         (res (assoc-equal type *rec-to-symbol-alist*))
         ((when (not res))
          (er hard? 'parse-recommendation "Unknown recommendation type: ~x0." type)
          (mv :unknown-rec-type nil state))
         (type-keyword (cdr res))
         ((when (not (stringp object)))
          (er hard? 'parse-recommendation "Non-string object: ~x0" object)
          (mv :bad-rec nil state))
         ((mv erp parsed-object state) (read-string-as-single-item object state)) ; todo: what about packages?
         ((when erp)
          (er hard? 'parse-recommendation "Error (~x0) parsing recommended action: ~x1." erp object)
          (mv :parse-error nil state))
         (name (concatenate 'string "ML" (nat-to-string rec-num)))
         )
      (mv nil ; no error
          (make-rec name type-keyword parsed-object confidence-percent book-map :unknown)
          state))))

;; Returns (mv erp parsed-recommendations state).
(defund parse-recommendations-aux (recs rec-num acc state)
  (declare (xargs :guard (and (parsed-json-valuesp recs)
                              (natp rec-num)
                              (true-listp acc))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable parsed-json-valuesp)))))
  (if (endp recs)
      (mv nil (reverse acc) state)
    (b* (((mv erp parsed-recommendation state) (parse-recommendation (first recs) rec-num state))
         ((when erp) (mv erp nil state)))
      (parse-recommendations-aux (rest recs)
                                 (+ 1 rec-num)
                                 (if (eq :none parsed-recommendation)
                                     acc ; omit bad rec
                                   (cons parsed-recommendation acc))
                                 state))))

;; Returns (mv erp parsed-recommendations state).
(defund parse-recommendations (recs state)
  (declare (xargs :guard (parsed-json-valuesp recs)
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable parsed-json-arrayp)))))
  (parse-recommendations-aux recs 1 nil state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Think about THM vs DEFTHM

(defun make-thm-to-attempt (body hints otf-flg)
  `(thm ,body
        ,@(and hints `(:hints ,hints))
        ,@(and otf-flg `(:otf-flg .otf-flg))))

;; Returns (mv provedp state).  Does not propagate any errors back.
(defund prove$-no-error (ctx term hints otf-flg step-limit state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp provedp state)
    ;; TODO: Drop the :time-limit once :step-limit can interrupt subsumption:
    (prove$ term :hints hints :otf-flg otf-flg :step-limit step-limit :time-limit 5)
    (if erp
        (prog2$ (cw "Syntax error in prove$ call (made by ~x0).~%" ctx)
                (mv nil state))
      (mv provedp state))))

;; Returns (mv provedp failure-info state).
(defund prove$-no-error-with-failure-info (ctx term hints otf-flg step-limit state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp provedp failure-info state)
    ;; TODO: Drop the :time-limit once :step-limit can interrupt subsumption:
    (prove$+ term :hints hints :otf-flg otf-flg :step-limit step-limit :time-limit 5 :print nil)
    (if erp
        (prog2$ (cw "Syntax error in prove$ call (made by ~x0).~%" ctx)
                (mv nil nil state))
      (mv provedp failure-info state))))

;; See :doc lemma-instance
(defund symbol-that-can-be-usedp (sym wrld)
  (declare (xargs :guard (and (symbolp sym)
                              (plist-worldp wrld))))
  (or (defined-functionp sym wrld)
      (defthm-or-defaxiom-symbolp sym wrld)))

;; Calls prove$ on FORMULA after submitting INCLUDE-BOOK-FORM, which is undone after the prove$.
;; Returns (mv erp provedp state).  If NAME-TO-CHECK is non-nil, we require it to be something
;; that can be enabled/disabled after including the book, or else we don't call prove$.
(defun prove$-with-include-book (ctx
                                 formula
                                 include-book-form
                                 name-to-check ; we ensure this exists after the include-book, or nil
                                 check-kind ; :enable or :use
                                 ;; args to prove$:
                                 hints otf-flg step-limit
                                 state)
  (declare (xargs :stobjs state :mode :program))
  (revert-world ;; ensures the include-book gets undone
   (b* (        ;; Try to include the recommended book:
        ((mv erp state) (submit-event-helper include-book-form nil nil state))
        ((when erp) ; can happen if there is a name clash
         (cw "NOTE: Event failed (possible name clash): ~x0.~%" include-book-form)
         (mv nil ; not considering this an error, since if there is a name clash we want to try the other recommendations
             nil state))
        ((when (and name-to-check
                    (if (eq :enable check-kind)
                        (not (item-that-can-be-enabled/disabledp name-to-check (w state)))
                      (if (eq :use check-kind)
                          (not (symbol-that-can-be-usedp name-to-check (w state)))
                        (er hard? 'prove$-with-include-book "Bad check-kind: ~x0." check-kind)))))
         ;; (cw "NOTE: After including ~x0, ~x1 is still not defined.~%" (cadr include-book-form) name-to-check) ;; todo: add debug arg
         (mv nil ; suppress error
             nil state))
        ((mv provedp state) (prove$-no-error ctx
                                             formula
                                             hints
                                             otf-flg
                                             step-limit
                                             state)))
     (mv nil provedp state))))

;; Try to prove FORMULA after submitting each of the INCLUDE-BOOK-FORMS (separately).
;; Returns (mv erp successful-include-book-form-or-nil state).
;; TODO: Don't return erp if we will always suppress errors.
(defun try-prove$-with-include-books (ctx
                                      formula
                                      include-book-forms
                                      name-to-check
                                      check-kind
                                      ;; args to prove$:
                                      hints otf-flg step-limit
                                      state)
  (declare (xargs :stobjs state :mode :program))
  (if (endp include-book-forms)
      (mv nil nil state)
    (b* ((form (first include-book-forms))
         ;; (- (cw "  Trying with ~x0.~%" form))
         ((mv & ; erp ; suppress errors from prove$-with-include-book (TODO: Why?)
              provedp state)
          (prove$-with-include-book ctx formula
                                    form
                                    name-to-check
                                    check-kind
                                    ;; args to prove$:
                                    hints otf-flg step-limit
                                    state))
         ;; ((when erp) (mv erp nil state))
         ((when provedp) (mv nil form state)))
      (try-prove$-with-include-books ctx
                                     formula
                                     (rest include-book-forms)
                                     name-to-check
                                     check-kind
                                     ;; args to prove$:
                                     hints otf-flg step-limit
                                     state))))

(defun cw-failure-message (snippet failure-info)
  (if (eq failure-info :step-limit-reached) ; update this is other kinds of failure-info become supported
      (cw "fail (~s0: step limit reached)~%" snippet)
    (cw "fail (~s0)~%" snippet)))

(defun cw-success-message (rec)
  (declare (xargs :mode :program)) ; todo
  (prog2$ (cw "SUCCESS: ")
          (show-successful-recommendation rec)))

;; Returns (mv erp successp state).
;; TODO: Skip if library already included
;; TODO: Skip later add-library recs if they are included by this one (though I suppose they might work only without the rest of what we get here).
;; TODO: Try any upcoming enable or use-lemma recs that (may) need this library:
(defun try-add-library (include-book-form theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name) ; todo: use to make a suggestion
           )
  (b* (((when (eq 'other include-book-form)) ; todo: can this happen, or could it be (include-book other)?
        (cw "skip (can't include catch-all library ~x0)~%" include-book-form)
        (mv nil nil state))
       ((when (not (consp include-book-form)))
        (cw "fail (ill-formed library recommendation: ~x0)~%" include-book-form)
        (mv nil nil state))
       ((mv erp provedp state)
        (prove$-with-include-book 'try-add-library theorem-body include-book-form nil nil theorem-hints theorem-otf-flg step-limit state))
       ((when erp) (mv erp nil state))
       (- (if provedp (cw-success-message rec) (cw "fail (library didn't help)~%"))))
    (mv nil (if provedp rec nil) state)))

;; TODO: Handle LET and MV-LET and nested implies and ...
(defun formula-hyp-simple (formula ;; untranslated
                           )
  (if (and (consp formula)
           (eq 'implies (ffn-symb formula)))
      (second formula)
    *t*))

(mutual-recursion
 (defun get-conjuncts-of-uterm (uterm ;; untranslated
                                )
   (if (not (consp uterm))
       (list uterm)
     (if (eq 'and (ffn-symb uterm))
         (get-conjuncts-of-uterms (fargs uterm))
       (if (and (eq 'if (ffn-symb uterm)) ; (if <x> <y> nil) is (and <x> <y>)
                (or (equal nil (farg3 uterm))
                    (equal *nil* (farg3 uterm))))
           (union-equal (get-conjuncts-of-uterm (farg1 uterm))
                        (get-conjuncts-of-uterm (farg2 uterm)))
         (list uterm)))))
 (defun get-conjuncts-of-uterms (uterms ;; untranslated
                                 )
   (if (endp uterms)
       nil
     (union-eq (get-conjuncts-of-uterm (first uterms))
               (get-conjuncts-of-uterms (rest uterms))))))

;; Returns (mv contradictp state).
(defund provably-contradictoryp (ctx formula state)
  (declare (xargs :mode :program
                  :stobjs state))
  (prove$-no-error ctx
                   `(not ,formula)
                   nil ; todo: use the theorem-hints? ;todo: don't induct?
                   nil
                   *step-limit*
                   state))

;; Returns (mv impliedp state).
(defund provably-impliesp (ctx x y state)
  (declare (xargs :mode :program
                  :stobjs state))
  (prove$-no-error ctx
                   `(implies ,x ,y)
                   nil ; todo: use the theorem-hints? ;todo: don't induct?
                   nil
                   *step-limit*
                   state))

;; Returns (mv erp successp state).
;; TODO: Don't try a hyp that is already present, or contradicts ones already present
(defun try-add-hyp (hyp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* ((translatablep (translatable-termp hyp (w state)))
       ((when (not translatablep))
        (cw "fail (hyp not translatable: ~x0)~%" hyp) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       (existing-hyp (formula-hyp-simple theorem-body))
       (existing-hyp-conjunts (get-conjuncts-of-uterm existing-hyp))
       ((when (member-equal hyp existing-hyp-conjunts))
        (cw "skip (hyp ~x0 is already present)~%" hyp)
        (mv nil nil state))
       ((mv impliedp state)
        (provably-impliesp 'try-add-hyp existing-hyp hyp state))
       ((when impliedp)
        (cw "skip (hyp ~x0 is implied by existing hyps)~%" hyp)
        (mv nil nil state))
       ((mv contradictp state)
        (provably-contradictoryp 'try-add-hyp `(and ,hyp ,existing-hyp) state))
       ((when contradictp)
        (cw "skip (hyp ~x0 would contradict existing hyps)~%" hyp)
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  ;; TODO: Add the hyp more nicely:
       ;;                  (make-thm-to-attempt `(implies ,hyp ,theorem-body) theorem-hints theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp failure-info state) (prove$-no-error-with-failure-info
                                         'try-add-hyp
                                         `(implies ,hyp ,theorem-body)
                                         theorem-hints
                                         theorem-otf-flg
                                         step-limit
                                         state))
       (rec (update-pre-commands nil rec)) ; update once we use the book map
       (- (if provedp
              (cw-success-message rec)
            (let ((translated-hyp (translate-term hyp 'try-add-hyp (w state))))
              (cw-failure-message (fms-to-string-one-line "adding hyp ~x0 didn't help" (acons #\0 translated-hyp nil)) failure-info)))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Avoid theory-invariant violations from enabling.
(defun try-add-enable-hint (rule     ; the rule to try enabling
                            book-map ; info on where the rule may be found
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            step-limit
                            rec
                            state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((when (eq rule 'other)) ;; "Other" is a catch-all for low-frequency classes
        (cw "skip (Not disabling catch-all: ~x0)~%" rule)
        (mv nil nil state))
       ((when (keywordp rule))
        (cw "skip (Not disabling unsupported item: ~x0)~%" rule) ; this can come from a ruleset of (:rules-of-class :type-prescription :here)
        (mv nil nil state))
       ((when (not (symbolp rule)))
        (cw "skip (Unsupported item: ~x0)~%" rule) ; todo: handle runes like (:TYPE-PRESCRIPTION A14 . 1)
        (mv nil nil state))
       (wrld (w state))
       (rule (handle-macro-alias rule wrld)) ; TODO: Handle the case of a macro-alias we don't know about
       )
    (if (function-symbolp rule wrld)
        ;; It's a function in the current world:
        (b* ((fn rule)
             ((when (not (logicp fn wrld)))
              (cw "skip (Can't enable ~x0. Not in :logic mode.)~%" fn)
              (mv nil nil state))
             ((when (not (and
                          ;; (defined-functionp fn wrld) ;todo
                          )))
              (cw "skip (Can't enable ~x0. No body.)~%" fn)
              (mv nil nil state))
             ;; TODO: Consider whether to enable, say the :type-prescription rule
             (rune `(:definition ,fn))
             ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
             ((when (enabled-runep rune (ens-maybe-brr state) (w state)))
              (cw "skip (~x0 is already enabled.)~%" fn)
              (mv nil nil state))
             ;; FN exists and just needs to be enabled:
             (new-hints (enable-runes-in-hints theorem-hints (list fn))) ;; todo: ensure this is nice
             ((mv provedp state)
              (prove$-no-error 'try-add-enable-hint
                               theorem-body
                               new-hints
                               theorem-otf-flg
                               step-limit
                               state))
             ((when (not provedp))
              (cw "fail (enabling function ~x0 didn't help)~%" fn)
              (mv nil nil state))
             ;; We change the rec type to ensure duplicates get removed:
             (rec (update-rec-type :add-enable-hint rec))
             (- (cw-success-message rec)))
          (mv nil rec state))
      (if (not (eq :no-body (getpropc rule 'theorem :no-body wrld))) ;todo: how to just check if the property is set?
          ;; It's a theorem in the current world:
          (b* ( ;; TODO: Consider whether to enable, say the :type-prescription rule
               (rune `(:rewrite ,rule))
               ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
               ((when (enabled-runep rune (ens-maybe-brr state) (w state)))
                (cw "skip (~x0 is already enabled.)~%" rule)
                (mv nil nil state))
               ;; RULE exists and just needs to be enabled:
               (new-hints (enable-runes-in-hints theorem-hints (list rule))) ;; todo: ensure this is nice
               ((mv provedp state)
                (prove$-no-error 'try-add-enable-hint
                                 theorem-body
                                 new-hints
                                 theorem-otf-flg
                                 step-limit
                                 state))
               ((when (not provedp))
                (cw "fail (enabling rule ~x0 didn't help)~%" rule)
                (mv nil nil state))
               ;; We change the rec type to ensure duplicates get removed:
               (rec (update-rec-type :add-enable-hint rec))
               (- (cw-success-message rec)))
            (mv nil rec state))
        ;; RULE is not currently known, so try to find where it is defined:
        (b* ((book-map-keys (strip-cars book-map))
             ((when (not (equal book-map-keys (list rule))))
              (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil rule)
              (mv :bad-book-map nil state))
             (books-to-try (lookup-eq rule book-map))
             ((when (eq :builtin books-to-try))
              (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" rule)
              (mv :bad-book-info nil state))
             ;; todo: check for empty books-to-try, or is that already checked?
             (num-books-to-try-orig (len books-to-try))
             ;; (- (and (< 1 num-books-to-try)
             ;;         (cw "NOTE: There are ~x0 books that might contain ~x1: ~X23~%" num-books-to-try rule books-to-try nil)))
             (books-to-try (if (< 3 num-books-to-try-orig)
                               (take 3 books-to-try)
                             books-to-try))
             ;; todo: ensure this is nice:
             (new-hints (enable-runes-in-hints theorem-hints (list rule))))
          ;; Not built-in, so we'll have to try finding the rule in a book:
          ;; TODO: Would be nice to not bother if it is a definition that we don't have.
          (b* ( ;; TODO: For each of these, if it works, maybe just try the include-book without the enable:
               ;; TODO: If, after including the book, the name to enable is a function, enabling it seems unlikely to help given that it didn't appear in the original proof.
               ((mv erp successful-include-book-form-or-nil state)
                (try-prove$-with-include-books 'try-add-enable-hint theorem-body books-to-try rule :enable new-hints theorem-otf-flg *step-limit* state))
               ((when erp) (mv erp nil state))
               (provedp (if successful-include-book-form-or-nil t nil))
               ;; todo: clarify whether we even found an include-book that works
               ((when (not provedp))
                (if (< 3 num-books-to-try-orig)
                    ;; todo: try more if we didn't find it?:
                    (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" (len books-to-try) num-books-to-try-orig rule)
                  (cw "fail (enabling ~x0 didn't help)~%" rule))
                (mv nil nil state))
               ;; We proved it with an include-book and an enable hint.  Now
               ;; try again but without the enable hint (maybe the include-book is enough):
               ((mv erp provedp-with-no-hint state)
                (prove$-with-include-book 'try-add-enable-hint ; todo: the redoes the include-book
                                          theorem-body
                                          successful-include-book-form-or-nil ; won't be nil
                                          nil ; name-to-check (no need to check this again)
                                          :enable
                                          ;; args to prove$:
                                          theorem-hints ; original hints, not new-hints
                                          theorem-otf-flg
                                          step-limit ; or base this on how many steps were taken when it succeeded
                                          state))
               ((when erp) (mv erp nil state))
               ;; todo: we could even try to see if a smaller library would work
               (rec (if provedp-with-no-hint
                        (list (nth 0 rec) ;name (ok to keep the same name, i guess)
                              :add-library ;; Change the rec to :add-library since the hint didn't matter!
                              successful-include-book-form-or-nil
                              (nth 3 rec) ; not very meaningful now
                              (nth 4 rec) ; not very meaningful now
                              nil ; pre-commands (always none for :add-library)
                              )
                   (update-rec-type :add-enable-hint (update-pre-commands (list successful-include-book-form-or-nil) rec))))
               (- (cw-success-message rec)))
            (mv nil
                rec
                state)))))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-disable-hint (rule theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((when (eq rule 'other)) ;; "Other" is a catch-all for low-frequency classes
        (cw "skip (Not disabling catch-all: ~x0)~%" rule)
        (mv nil nil state))
       ((when (keywordp rule))
        (cw "skip (Not disabling unsupported item: ~x0)~%" rule) ; this can come from a ruleset of (:rules-of-class :type-prescription :here)
        (mv nil nil state))
       ((when (not (item-that-can-be-enabled/disabledp rule (w state))))
        (cw "skip (Not disabling unknown name: ~x0)~%" rule) ;; For now, we don't try to including the book that brings in the thing to disable!
        (mv nil nil state))
       (rule (handle-macro-alias rule (w state))) ; TODO: Handle the case of a macro-alias we don't know about
       ((when (disabledp-fn rule (ens-maybe-brr state) (w state)))
        (cw "skip (Not disabling since already disabled: ~x0)~%" rule)
        (mv nil nil state))
       ((mv provedp state) (prove$-no-error 'try-add-disable-hint
                                            theorem-body
                                            ;; todo: ensure this is nice:
                                            (disable-runes-in-hints theorem-hints (list rule))
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (- (if provedp (cw-success-message rec) (cw "fail (disable didn't help)~%"))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Do we need to guess a substitution for the :use hint?  Then change the rec before returning...
(defun try-add-use-hint (item book-map theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq item 'other))
        (cw "skip (skipping catch-all: ~x0)~%" item)
        (mv nil nil state))
       ((when (not (symbolp item))) ; for now
        (cw "skip (unexpected object for :add-use-hint: ~x0)~%" item) ; todo: add support for other lemma-instances
        (mv nil nil state)))
    (if (symbol-that-can-be-usedp item (w state)) ; todo: what if it's defined but can't be :used?
        (b* (((mv provedp state) (prove$-no-error 'try-add-use-hint
                                                  theorem-body
                                                  ;; todo: ensure this is nice:
                                                  ;; todo: also disable the item, if appropriate
                                                  (cons `("Goal" :use ,item) theorem-hints)
                                                  theorem-otf-flg
                                                  step-limit
                                                  state))
             (- (if provedp (cw-success-message rec) (cw "fail (:use ~x0 didn't help)~%" item))))
          (mv nil (if provedp rec nil) state))
      ;; ITEM is not in the current world, so try to find where it is defined:
      (b* ((book-map-keys (strip-cars book-map))
           ((when (not (equal book-map-keys (list item))))
            (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil item)
            (mv :bad-book-map nil state))
           (books-to-try (lookup-eq item book-map))
           ((when (eq :builtin books-to-try))
            (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" item)
            (mv :bad-book-info nil state))
           ;; todo: check for empty books-to-try, or is that already checked?
           (num-books-to-try-orig (len books-to-try))
           ;; (- (and (< 1 num-books-to-try)
           ;;         (cw "NOTE: There are ~x0 books that might contain ~x1: ~X23~%" num-books-to-try item books-to-try nil)))
           (books-to-try (if (< 3 num-books-to-try-orig)
                             (take 3 books-to-try)
                           books-to-try))
           ;; todo: ensure this is nice:
           (new-hints ;; todo: ensure this is nice:
            ;; todo: also disable the item, if appropriate
            (cons `("Goal" :use ,item) theorem-hints))
           ;; TODO: Would be nice to not bother if it is a definition that we don't have.
           ;; TODO: For each of these, if it works, maybe just try the include-book without the enable:
           ;; TODO: If, after including the book, the name to enable is a function, enabling it seems unlikely to help given that it didn't appear in the original proof.
           ((mv erp successful-include-book-form-or-nil state)
            (try-prove$-with-include-books 'try-add-use-hint theorem-body books-to-try item :use new-hints theorem-otf-flg *step-limit* state))
           ((when erp) (mv erp nil state))
           (provedp (if successful-include-book-form-or-nil t nil))
           ((when (not provedp))
            (if (< 3 num-books-to-try-orig)
                ;; todo: try more if we didn't find it?:
                (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" (len books-to-try) num-books-to-try-orig item)
              (cw "fail (using ~x0 didn't help)~%" item))
            (mv nil nil state))
           ;; We proved it with an include-book and a :use hint.  Now
           ;; try again but without the :use hint (maybe the include-book is enough):
           ((mv erp provedp-with-no-hint state)
            (prove$-with-include-book 'try-add-use-hint ; todo: the redoes the include-book
                                      theorem-body
                                      successful-include-book-form-or-nil ; won't be nil
                                      nil ; name-to-check (no need to check this again)
                                      :use
                                      ;; args to prove$:
                                      theorem-hints ; original hints, not new-hints
                                      theorem-otf-flg
                                      step-limit ; or base this on how many steps were taken when it succeeded
                                      state))
           ((when erp) (mv erp nil state))
           ;; todo: we could even try to see if a smaller library would work
           (rec (if provedp-with-no-hint
                    (list (nth 0 rec) ;name (ok to keep the same name, i guess)
                          :add-library ;; Change the rec to :add-library since the hint didn't matter!
                          successful-include-book-form-or-nil
                          (nth 3 rec) ; not very meaningful now
                          (nth 4 rec) ; not very meaningful now
                          nil ; pre-commands (always none for :add-library)
                          )
                  (update-pre-commands (list successful-include-book-form-or-nil) rec)))
           (- (cw-success-message rec)))
        (mv nil
            rec
            state)))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-expand-hint (item ; the thing to expand
                            theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'other item))
        (cw "fail (ignoring recommendation to expand \"Other\")~%")
        (mv nil nil state))
       ((when (symbolp item)) ; todo: eventually remove this case
        (cw "fail (ignoring illegal recommendation to expand a symbol)~%")
        (mv nil nil state))
       ;; todo: can it be a single term?:
       ((when (not (translatable-term-listp item (w state))))
        (cw "fail (term not all translatable: ~x0)~%" item) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :expand ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-no-error 'try-add-expand-hint
                                            theorem-body
                                            ;; todo: ensure this is nice:
                                            (cons `("Goal" :expand ,item) theorem-hints)
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (- (if provedp (cw-success-message rec) (cw "fail (:expand hint didn't help)~%"))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-by-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'other item))
        (cw "fail (ignoring :by hint with catch-all \"Other\")~%")
        (mv nil nil state))
       ((when (not (symbolp item)))
        (cw "fail (unexpected :by hint: ~x0)~%" item)
        (mv nil nil state))
       ((when (not (or (getpropc item 'unnormalized-body nil (w state))
                       (getpropc item 'theorem nil (w state)))))
        (cw "skip (unknown name for :by hint: ~x0)~%" item)
        (mv nil nil state))
       ;; TTODO: Include any necessary books first
       ((mv provedp failure-info state)
        (prove$-no-error-with-failure-info 'try-add-by-hint
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           ;; todo: remove existing hints?
                                           (cons `("Goal" :by ,item) theorem-hints)
                                           theorem-otf-flg
                                           step-limit
                                           state))
       (- (if provedp (cw-success-message rec) (cw-failure-message ":by hint didn't help" failure-info))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-cases-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (not (translatable-term-listp item (w state))))
        (cw "fail (terms not all translatable: ~x0)~%" item) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :cases ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-no-error 'try-add-cases-hint
                                            theorem-body
                                            ;; todo: ensure this is nice:
                                            (cons `("Goal" :cases ,item) theorem-hints)
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (- (if provedp (cw-success-message rec) (cw "fail (:cases hint didn't help)~%"))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: We need more than a symbol
(defun try-add-induct-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec))
  (if (symbolp item)
      (prog2$ (cw "skip (need arguments of ~x0 to create :induct hint)~%" item)
              (mv nil nil state))
    ;; TODO: Flesh this out when ready:
    (mv :unsupported-induct-hint nil state)))

(defun try-exact-hints (hints theorem-body theorem-otf-flg step-limit rec state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((mv provedp failure-info state)
        (prove$-no-error-with-failure-info 'try-exact-hints
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           hints
                                           theorem-otf-flg
                                           step-limit
                                           state))
       (- (if provedp (cw-success-message rec) (cw-failure-message ":hints didn't help" failure-info))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp successful-recs state)
(defun try-recommendations (recs
                            theorem-name ; may be :thm
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            step-limit
                            max-wins
                            successful-recs
                            state)
  (declare (xargs :guard (and (recommendation-listp recs)
                              (symbolp theorem-name)
                              (pseudo-termp theorem-body)
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (true-listp successful-recs))
                  :mode :program
                  :stobjs state))
  (if (or (endp recs)
          (and (natp max-wins)
               (<= max-wins (len successful-recs))))
      (mv nil (reverse successful-recs) state)
    (b* ((rec (first recs))
         (name (car rec))
         (type (cadr rec))
         (object (caddr rec))
         ;; (confidence-percent (cadddr rec))
         (book-map (car (cddddr rec)))
         (- (cw "~s0: " name))
         ((mv & ; erp ; for now, we ignore errors and just continue
              maybe-successful-rec state)
          (case type
            ;; TODO: Pass the book-map to all who can use it:
            (:add-by-hint (try-add-by-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            (:add-cases-hint (try-add-cases-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            (:add-disable-hint (try-add-disable-hint object theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            ;; todo: do-not
            (:add-enable-hint (try-add-enable-hint object book-map theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            (:add-expand-hint (try-add-expand-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            (:add-hyp (try-add-hyp object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            (:add-induct-hint (try-add-induct-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            (:add-library (try-add-library object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            ;; todo: nonlinearp
            (:add-use-hint (try-add-use-hint object book-map theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            ;; same as for try-add-enable-hint above:
            (:use-lemma (try-add-enable-hint object book-map theorem-body theorem-hints theorem-otf-flg step-limit rec state))
            ;; Hints not from ML:
            (:exact-hints (try-exact-hints object theorem-body theorem-otf-flg step-limit rec state))
            (t (prog2$ (cw "WARNING: UNHANDLED rec type ~x0.~%" type)
                       (mv t nil state))))))
      (try-recommendations (rest recs) theorem-name theorem-body theorem-hints theorem-otf-flg step-limit max-wins
                           (if maybe-successful-rec
                               (cons maybe-successful-rec successful-recs)
                             successful-recs)
                           state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-enable-recs-aux (names num)
  (declare (xargs :guard (and (symbol-listp names)
                              (posp num))))
  (if (endp names)
      nil
    (cons (list (concatenate 'string "E" (nat-to-string num))
                :add-enable-hint
                (first names) ; the name to enable
                0            ; confidence percentage (TODO: allow unknown)
                nil ; book map ; todo: indicate that the name must be present?
                nil ; no pre-commands
                )
          (make-enable-recs-aux (rest names) (+ 1 num)))))

(local
 (defthm recommendation-listp-of-make-enable-recs-aux
   (implies (symbol-listp names)
            (recommendation-listp (make-enable-recs-aux names num)))))

;; TODO: Don't even make recs for things that are enabled?  Well, we handle that elsewhere.
(defun make-enable-recs (formula wrld)
  (declare (xargs :guard (and (pseudo-termp formula)
                              (plist-worldp wrld))
                  :mode :program))
  (let* ((translated-formula (translate-term formula 'make-enable-recs wrld))
         (fns-to-try-enabling (set-difference-eq (defined-fns-in-term translated-formula wrld)
                                                 ;; Don't bother wasting time with trying to enable implies
                                                 ;; (I suppose we coud try it if implies is disabled):
                                                 '(implies))))
    (make-enable-recs-aux fns-to-try-enabling 1)))

;; (local
;;  (defthm recommendation-listp-of-make-enable-recs
;;    (implies (pseudo-termp formula)
;;             (recommendation-listp (make-enable-recs formula wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not looking at anything but the type and object
(defun rec-presentp (type object recs)
  (if (endp recs)
      nil
    (let ((rec (first recs)))
      (if (and (eq type (nth 1 rec))
               (equal object (nth 2 rec)))
          t
        (rec-presentp type object (rest recs))))))

(mutual-recursion
 ;; Look for hints in theorems in the history
 ;; Returns a list of recs.
 (defun make-recs-from-event (event num seen-recs)
   (if (not (consp event))
       (er hard? 'make-rec-from-event "Unexpected command: ~x0." event)
     (if (eq 'local (ffn-symb event)) ; (local e1)
         (make-recs-from-event (farg1 event) num seen-recs)
       (if (eq 'encapsulate (ffn-symb event)) ; (encapsulate <sigs> e1 e2 ...)
           (make-recs-from-events (rest (fargs event)) num seen-recs)
         (if (eq 'progn (ffn-symb event)) ; (progn e1 e2 ...)
             (make-recs-from-events (fargs event) num seen-recs)
           (and (consp event) ; todo: strip local?  what else can we harvest hints from?
                (member-eq (ffn-symb event) '(defthm defthmd))
                (let ((res (assoc-keyword :hints (rest (rest (fargs event))))))
                  (and res
                       (let ((hints (cadr res)))
                         (and (not (rec-presentp :exact-hints hints seen-recs))
                              ;; make a new rec:
                              (list
                               (make-rec (concatenate 'string "H" (nat-to-string num))
                                         :exact-hints ; new kind of rec, to replace all hints
                                         (cadr res)
                                         0
                                         nil
                                         nil))))))))))))

 (defun make-recs-from-events (events num acc)
   (if (endp events)
       (reverse acc)
     (let* ((event (first events))
            (recs (make-recs-from-event event num acc))
            (acc (append recs acc))
            (num (+ (len recs) num)))
       (make-recs-from-events (rest events) num acc)))))

;; Returns (mv erp val state).
(defun make-recs-from-history (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((mv erp events state) (get-command-sequence-fn 1 :max state))
       ((when erp) (mv erp nil state)))
    (mv nil (make-recs-from-events events 1 nil) state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; from Matt K:
(defun clausify-term (term wrld)
  (declare (xargs :mode :program))
  (let* ((term (expand-some-non-rec-fns '(implies) term wrld))
         (term (remove-guard-holders term wrld)))
    (clausify term nil t (sr-limit wrld))))

;; compares the type and object fields
(defund same-recp (rec1 rec2)
  (and (equal (nth 1 rec1) (nth 1 rec2))
       (equal (nth 2 rec1) (nth 2 rec2))))

;; Remove all members of RECS that are the same as REC (wrt type and object)
(defun remove-duplicate-rec (rec recs acc)
  (if (endp recs)
      (reverse acc)
    (if (same-recp rec (first recs))
        (remove-duplicate-rec rec (rest recs) acc)
      (remove-duplicate-rec rec (rest recs) (cons (first recs) acc)))))

(local
 (defthm len-of-remove-duplicate-rec-linear
   (<= (len (remove-duplicate-rec rec recs acc))
       (+ (len recs) (len acc)))
   :rule-classes :linear))

;; Keeps the first of each set of duplicates
(defun remove-duplicate-recs (recs acc)
  (declare (xargs :measure (len recs)))
  (if (endp recs)
      (reverse acc)
    (let* ((rec (first recs))
           (reduced-rest (remove-duplicate-rec rec (rest recs) nil)))
      (remove-duplicate-recs reduced-rest
                             (cons rec acc)))))

;; Sends an HTTP POST request containing the POST-DATA to the server at
;; SERVER-URL.  Parses the response as JSON.  Returns (mv erp
;; parsed-json-response state).
(defund post-and-parse-response-as-json (server-url post-data debug state)
  (declare (xargs :guard (and (stringp server-url)
                              (string-string-alistp post-data)
                              (booleanp debug))
                  :stobjs state))
  (b* ((- (and debug (cw "POST data to be sent: ~X01.~%" post-data nil)))
       ((mv erp post-response state)
        (htclient::post server-url post-data state))
       ((when erp) (mv erp nil state))
       (- (and debug (cw "Raw POST response: ~X01~%" post-response nil)))
       ;; Parse the JSON:
       ((mv erp parsed-json-response) (parse-string-as-json post-response))
       ((when erp)
        (cw "Error parsing JSON response from ~x0.~%" server-url)
        (mv erp nil state))
       (- (and debug (cw "Parsed POST response: ~X01~%" parsed-json-response nil))))
    (mv nil parsed-json-response state)))

;; Returns (mv erp nil state).
;; TODO: Support getting checkpoints from a defun, but then we'd have no body
;; to fall back on when (equal untranslated-checkpoints '(<goal>)) (see
;; below).
(defun advice-fn (n ; number of recommendations from ML requested
                  verbose
                  server-url
                  debug
                  step-limit
                  max-wins
                  state)
  (declare (xargs :guard (and (natp n)
                              (booleanp verbose)
                              (checkpoint-list-guard t ;top-p
                                                     state)
                              (booleanp debug)
                              (or (eq :auto step-limit)
                                  (eq nil step-limit)
                                  (natp step-limit))
                              (or (eq :auto max-wins)
                                  (null max-wins)
                                  (natp max-wins)))
                  :stobjs state
                  :mode :program ; because we untranslate (for now)
                  ))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       ;; Get server info:
       ((mv erp server-url state) (if server-url (mv nil server-url state) (getenv$ "ACL2_ADVICE_SERVER" state)))
       ((when erp) (cw "ERROR getting ACL2_ADVICE_SERVER environment variable.") (mv erp nil state))
       ((when (not (stringp server-url)))
        (er hard? 'advice-fn "Please set the ACL2_ADVICE_SERVER environment variable to the server URL (often ends in '/machine_interface').")
        (mv :no-server nil state))
       ;; Get most recent failed theorem:
       (most-recent-failed-theorem (most-recent-failed-command *theorem-event-types* state))
       ((mv theorem-name theorem-body theorem-hints theorem-otf-flg)
        (if (member-eq (car most-recent-failed-theorem) '(thm rule))
            (mv :thm ; no name
                (cadr most-recent-failed-theorem)
                (cadr (assoc-keyword :hints (cddr most-recent-failed-theorem)))
                (cadr (assoc-keyword :otf-flg (cddr most-recent-failed-theorem))))
          ;; Must be a defthm, etc:
          (mv (cadr most-recent-failed-theorem)
              (caddr most-recent-failed-theorem)
              (cadr (assoc-keyword :hints (cdddr most-recent-failed-theorem)))
              (cadr (assoc-keyword :otf-flg (cdddr most-recent-failed-theorem))))))
       (- (cw "Generating advice for:~%~X01:~%" most-recent-failed-theorem nil))
       (- (and verbose (cw "Original hints were:~%~X01:~%" theorem-hints nil)))
       ;; Get the checkpoints from the failed attempt:
       (raw-checkpoint-clauses (checkpoint-list ;-pretty
                                t               ; todo: consider non-top
                                state))
       ((when (eq :unavailable raw-checkpoint-clauses))
        (er hard? 'advice-fn "No checkpoints are available (perhaps the most recent theorem succeeded).")
        (mv :no-checkpoints nil state))
       ;; Deal with unfortunate case when acl2 decides to backtrack and try induction:
       ;; TODO: Or use :otf-flg to get the real checkpoints?
       (checkpoint-clauses (if (equal raw-checkpoint-clauses '((<goal>)))
                               (clausify-term (translate-term (most-recent-failed-theorem-goal state)
                                                              'advice-fn
                                                              wrld)
                                              wrld)
                             raw-checkpoint-clauses))
       (- (and verbose (cw "Checkpoints in query: ~X01.)~%" checkpoint-clauses nil)))
       ;; Send query to server:
       ((mv erp semi-parsed-recommendations state)
        (if (zp n)
            (prog2$ (cw "Not asking server for recommendations since n=0.")
                    (mv nil
                        nil ; empty list of recommendations
                        state))
          (b* ((- (cw "Asking server for ~x0 recommendations on ~x1 ~s2...~%"
                      n
                      (len checkpoint-clauses)
                      (if (< 1 (len checkpoint-clauses)) "checkpoints" "checkpoint")))
               (post-data (acons "n" (nat-to-string n)
                                 (make-numbered-checkpoint-entries 0 checkpoint-clauses)))
               ((mv erp parsed-response state)
                (post-and-parse-response-as-json server-url post-data debug state))
               ((when erp)
                (er hard? 'advice-fn "Error in HTTP POST: ~@0" erp)
                (mv erp nil state)))
            (mv nil (parsed-json-array->values parsed-response) state))))
       ((when erp) (mv erp nil state))
       ;; Parse the individual strings in the recs:
       ((mv erp ml-recommendations state) (parse-recommendations semi-parsed-recommendations state))
       ((when erp)
        (er hard? 'advice-fn "Error parsing recommendations.")
        (mv erp nil state))
       (- (and debug (cw "Parsed ML recommendations: ~X01~%" ml-recommendations nil)))
       ;; Make some other recs:
       (enable-recommendations (make-enable-recs theorem-body wrld))
       ((mv erp historical-recommendations state) (make-recs-from-history state))
       ((when erp) (mv erp nil state))
       (recommendations (append enable-recommendations
                                historical-recommendations
                                ml-recommendations))
       ;; (num-recs (len recommendations))
       ;; Print the recommendations (for now):
       (-  (cw "~%RECOMMENDATIONS TO TRY:~%"))
       (state (show-recommendations recommendations state))
       ;; Try the recommendations:
       (- (cw "~%TRYING RECOMMENDATIONS:~%"))
       (state (widen-margins state))
       ((mv erp
            successful-recs ; result-acc ; todo: use this, and make it richer
            state)
        (try-recommendations recommendations theorem-name theorem-body theorem-hints theorem-otf-flg step-limit max-wins nil state))
       (state (unwiden-margins state))
       ((when erp)
        (er hard? 'advice-fn "Error trying recommendations: ~x0" erp)
        (mv erp nil state))
       (successful-recs-no-dupes (remove-duplicate-recs successful-recs nil))
       (removed-count (- (len successful-recs) (len successful-recs-no-dupes)))
       (- (and (posp removed-count)
               (cw "~%NOTE: ~x0 duplicate ~s1 removed.~%" removed-count
                   (if (< 1 removed-count) "successful recommendations were" "successful recommendation was"))))
       (num-successful-recs (len successful-recs-no-dupes))
       (max-wins-reachedp (and (natp max-wins) (= max-wins num-successful-recs)))
       (- (and max-wins-reachedp
               (cw "~%NOTE: Search stopped after finding ~x0 successful ~s1.~%" max-wins (if (< 1 max-wins) "recommendations" "recommendation"))))
       (state (if (posp num-successful-recs)
                  (progn$ (if (< 1 num-successful-recs)
                              (cw "~%PROOF FOUND (~x0 successful recommendations):~%" num-successful-recs)
                            (cw "~%PROOF FOUND (1 successful recommendation):~%"))
                          (progn$ ;; (cw "~%SUCCESSFUL RECOMMENDATIONS:~%")
                                  (let ((state (show-successful-recommendations successful-recs-no-dupes state)))
                                    state)))
                (prog2$ (cw "~%NO PROOF FOUND~%~%")
                        state)))
       ;; Ensure there are no checkpoints left over from an attempt to use advice, in case the user calls the tool again.
       ;; TODO: Can we restore the old gag state saved?
       ;;(state (f-put-global 'gag-state-saved nil state))

       ;; Try to ensure the checkpoints are restored, in case the tool is run again:
       (state
        (b* ((new-raw-checkpoint-clauses (checkpoint-list ;-pretty
                                          t ; todo: consider non-top
                                          state))
             ((when (equal new-raw-checkpoint-clauses raw-checkpoint-clauses))
              state ; no need to do anything
              )
             ((mv provedp state)
              (prove$-no-error 'advice-fn theorem-body theorem-hints theorem-otf-flg
                               nil ; step-limit
                               state))
             ((when provedp) ; surprising!
              (cw "Tried the theorem again and it worked!")
              state)
             (new-raw-checkpoint-clauses (checkpoint-list ;-pretty
                                          t ; todo: consider non-top
                                          state))
             ((when (not (equal new-raw-checkpoint-clauses raw-checkpoint-clauses)))
              (cw "Clearing checkpoints since we failed to restore them.~%")
              (let ((state (f-put-global 'gag-state-saved nil state)))
                state)))
          state)))
       (mv nil ; no error
        '(value-triple :invisible) state)))

(defmacro advice (&key (n '10) (verbose 'nil) (server-url 'nil) (debug 'nil) (step-limit ':auto) (max-wins ':auto))
  `(make-event-quiet (advice-fn ,n ,verbose ,server-url ,debug ,step-limit ,max-wins state)))

;; Example:
;; (acl2s-defaults :set testing-enabled nil) ; turn off testing
;; (thm (equal (- (- x)) x))
;; (advice)
;; (thm (< (mod x 8) 256))
;; (advice)
