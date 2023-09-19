; A tool to get proof advice from a server over the web
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HELP")

;; SETUP:
;;
;; 1. Execute table events to register the models, each supplying a nickname for
;; the model (a keyword), the URL of the model (a string), and the name the
;; server uses for the model (a string).  Example:
;;
;; (table advice-server :my-model '("https://example.com/machine_interface" "model1"))
;;
;; Consider putting these table events in your ~/acl2-customization.lsp.
;;
;; 2. When using this tool, consider doing (adjust-ld-history t state) so
;; that the advice tool can give advice even when the failing theorem is not
;; the most recent event.

;; Usage:
;;
;; This book provides 3 tools: defthm-advice, thm-advice, and advice.
;; - defthm-advice is like defthm but tries advice if the given hints don't prove the theorem
;; - thm-advice is like thm but tries advice if the given hints don't prove the theorem
;; - advice attempts to find the user's most recent failed proof attempt and try advice to prove it

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

(include-book "recommendations")
(include-book "model-enable")
(include-book "model-history")
(include-book "model-induct")
(include-book "model-cases")
(include-book "kestrel/utilities/book-of-event" :dir :system)
(include-book "kestrel/utilities/checkpoints" :dir :system)
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/prove-dollar-plus" :dir :system)
(include-book "kestrel/utilities/read-string" :dir :system)
(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "kestrel/utilities/wrap-all" :dir :system)
(include-book "kestrel/utilities/all-included-books" :dir :system)
(include-book "kestrel/hints/combine-hints" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/strings-light/downcase" :dir :system)
(include-book "kestrel/typed-lists-light/string-list-listp" :dir :system)
(include-book "kestrel/untranslated-terms/conjuncts-of-uterm" :dir :system)
(include-book "kestrel/alists-light/string-string-alistp" :dir :system)
(include-book "kestrel/htclient/post-light" :dir :system) ; todo: slow
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/big-data/packages" :dir :system) ; try to ensure all packages that might arise are known ; todo: very slow
(include-book "tools/prove-dollar" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
;(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/add-to-set-equal" :dir :system))
;(local (include-book "kestrel/alists-light/lookup-eq" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/utilities/coerce" :dir :system))

(local (in-theory (disable member-equal len true-listp nth reverse mv-nth
                           state-p
                           acl2::checkpoint-list-guard
                           global-table
                           put-global
                           get-global
                           set-fmt-hard-right-margin
                           acl2::deref-macro-name)))

(local (in-theory (enable stringp-of-nth-0-when-recommendationp
                          rationalp-of-nth-3-when-recommendationp
                          true-listp-when-recommendationp)))

;; ;; Returns all disabled runes associate with NAME.
;; ;; Like disabledp but hygienic, also doesn't end in "p" since not a predicate.
;; (defun disabled-runes (name ens wrld)
;;   (declare (xargs :mode :program))
;;   (disabledp-fn name ens wrld))

(defconst *step-limit* 100000)
(defconst *time-limit* 5)

;;move
;; does this already exist somewhere?
(defund acons-all-to-val (keys val alist)
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp keys)
      alist
    (acons (first keys) val (acons-all-to-val (rest keys) val alist))))

;; See :doc lemma-instance
(defund symbol-that-can-be-usedp (sym wrld)
  (declare (xargs :guard (and (symbolp sym)
                              (plist-worldp wrld))))
  (or (acl2::defined-functionp sym wrld)
      (acl2::defthm-or-defaxiom-symbolp sym wrld)))

;; Returns (mv erp name).
(defun name-from-lemma-instance (lmi)
  (declare (xargs :guard t))
  (if (atom lmi)
      (if (not (symbolp lmi))
          (prog2$ (cw "ERROR: Lemma-instance is a non-symbol atom: ~x0.~%" lmi)
                  (mv :bad-lemma-instance nil))
        ;; Usual case:
        (mv nil lmi))
    (let ((sym (first lmi)))
      (case sym
        ((:rewrite :definition :linear) ;; todo: what else?
         (if (consp (cdr lmi))
             (mv nil (second lmi))
           (prog2$ (cw "ERROR: Bad lemma-instance: ~x0.~%" lmi)
                   (mv :bad-lemma-instance nil))))
        ((:instance :functional-instance)
         (if (consp (cdr lmi))
             (name-from-lemma-instance (second lmi))
           (prog2$ (cw "ERROR: Bad lemma-instance: ~x0.~%" lmi)
                   (mv :bad-lemma-instance nil))))
        ;; todo: handle other cases:
        (otherwise (prog2$ (cw "WARNING: Unhandled lemma-instance: ~x0.~%" lmi)
                           (mv :unhandled-lemma-instance nil)))))))

;; If NAME is a macro-alias, return what it represents.  Otherwise, return NAME.
;; TODO: Compare to (deref-macro-name name (macro-aliases wrld)).
(defund handle-macro-alias (name wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (not (symbolp name)) ; possible? could be a rune?
      name
    (let* ((macro-aliases-table (table-alist 'acl2::macro-aliases-table wrld)))
      (if (not (alistp macro-aliases-table))
          (er hard? 'handle-macro-alias "Bad macro aliases table.")
        (let ((res (assoc-eq name macro-aliases-table)))
          (if res
              (if (symbolp (cdr res))
                  (cdr res)
                (er hard? 'handle-macro-alias "Bad macro aliases table."))
            name))))))

;move
;; TODO: What kinds of things can ITEM be?  A runic-designator?  A theory?
(defund item-that-can-be-enabled/disabledp (item wrld)
  (declare (xargs :guard (and ;; (symbolp item)
                          (plist-worldp wrld)
                          (alistp (macro-aliases wrld)))
                  :verify-guards nil
                  ))
  (if (symbolp item)
      (let ((name (acl2::deref-macro-name item (macro-aliases wrld)))) ; no change if item is not a macro name
        (if (getpropc name 'acl2::runic-mapping-pairs nil wrld)
            t
          nil))
    (if (acl2::runep item wrld)
        t
      (cw "NOTE: Unknown kind of item: ~x0." item))))

;; Returns (mv erp lists)
;; Map parsed-json-array->values over a list.
(defun json-arrays-to-lists (arrays acc)
  (declare (xargs :guard (and (acl2::parsed-json-array-listp arrays)
                              (true-listp acc))))
  (if (endp arrays)
      (mv nil (reverse acc))
    (let ((array (first arrays)))
      (if (not (acl2::parsed-json-arrayp array)) ;drop?
          (mv t nil)
        (json-arrays-to-lists (rest arrays)
                              (cons (acl2::parsed-json-array->values array)
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

;; todo: distinguish top from non-top checkpoints
(defun make-numbered-checkpoint-entries (current-number checkpoint-clauses)
  (declare (xargs :guard (and (natp current-number)
                              (acl2::pseudo-term-list-listp checkpoint-clauses))
                  :mode :program)) ; because of fms-to-string
  (if (endp checkpoint-clauses)
      nil
    (acons (concatenate 'string "checkpoint_" (acl2::nat-to-string current-number))
           (fms-to-string "~X01" (acons #\0 (first checkpoint-clauses) (acons #\1 nil nil)))
           (make-numbered-checkpoint-entries (+ 1 current-number) (rest checkpoint-clauses)))))

(defund rec-type-listp (types)
  (declare (xargs :guard t))
  (if (not (consp types))
      (null types)
    (and (rec-typep (first types))
         (rec-type-listp (rest types)))))

(defthm rec-type-listp-of-cdr
  (implies (rec-type-listp types)
           (rec-type-listp (cdr types)))
  :hints (("Goal" :in-theory (enable rec-type-listp))))

(defthm rec-typep-of-car
  (implies (and (rec-type-listp types)
                (consp types))
           (rec-typep (car types)))
  :hints (("Goal" :in-theory (enable rec-type-listp))))

(defthm rec-type-listp-forward-to-symbol-listp
  (implies (rec-type-listp types)
           (symbol-listp types))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rec-type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rec-type-to-string (type)
  (declare (xargs :guard (rec-typep type)))
  (car (rassoc type *rec-to-symbol-alist*)))

(defthm stringp-of-rec-type-to-string
  (implies (rec-typep type)
           (stringp (rec-type-to-string type)))
  :hints (("Goal" :in-theory (enable rec-type-to-string
                                     rec-typep
                                     member-equal))))

(defund rec-types-to-strings (types)
  (declare (xargs :guard (rec-type-listp types)
                  :guard-hints (("Goal" :in-theory (enable rec-type-listp)))))
  (if (endp types)
      nil
    (cons (rec-type-to-string (first types))
          (rec-types-to-strings (rest types)))))

(defthm string-listp-of-rec-types-to-strings
  (implies (rec-type-listp types)
           (string-listp (rec-types-to-strings types)))
  :hints (("Goal" :in-theory (enable rec-types-to-strings))))

;; TODO: Make this extensible:
(defconst *function-models*
  '(:enable-fns-body
    :enable-fns-top-cps
    :enable-fns-non-top-cps
    :enable-rules-body
    :enable-rules-top-cps
    :enable-rules-non-top-cps
    :history
    :induct
    :cases))

;; (defconst *known-models* (strip-cars *known-models-and-strings*))

;; Indicates one of the recommendation models.
(defund model-namep (x)
  (declare (xargs :guard t))
  (and (keywordp x)
       (not (eq :all x))))

;; Recognizes a (duplicate-free) list of recommendation models.
(defund model-namesp (models)
  (declare (xargs :guard t))
  (if (atom models)
      (null models)
    (and (model-namep (first models))
         ;; (not (member-equal (first models) (rest models))) ;; todo: add back?
         (model-namesp (rest models)))))

;; (defun model-to-string (model)
;;   (declare (xargs :guard (model-namep model)))
;;   (if (stringp model)
;;       model
;;     ;; must be a keyword indicating a known model:
;;     (let ((res (assoc-eq model *known-models-and-strings*)))
;;       (if res
;;           (cdr res)
;;         (er hard? 'model-to-string "Unknown :model: ~x0." model)))))

(defun model-to-nice-string (model)
  (declare (xargs :guard (model-namep model)
                  :guard-hints (("Goal" :in-theory (enable model-namep member-equal)))))
  (acl2::string-downcase-gen (symbol-name model)))

;; ;; The source of a recommendation: Either one of the ML models or the advice tool itself.
;; (defund rec-sourcep (x)
;;   (declare (xargs :guard t))
;;   (or (model-namep x) ; recs from ML models
;;       (eq :advice-tool x) ; recs generated by the advice tool
;;       ))

;; (local
;;  (defthm model-namep-forward-to-rec-sourcep
;;    (implies (model-namep x)
;;             (rec-sourcep x))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal" :in-theory (enable rec-sourcep)))))

;; ;; Recognize a true list of recommendation sources
;; (defund rec-sourcesp (sources)
;;   (declare (xargs :guard t))
;;   (if (atom sources)
;;       (null sources)
;;     (and (rec-sourcep (first sources))
;;          (rec-sourcesp (rest sources)))))

;; (local
;;  (defthm rec-sourcesp-of-cons
;;    (equal (rec-sourcesp (cons rec recs))
;;           (and (rec-sourcep rec)
;;                (rec-sourcesp recs)))
;;    :hints (("Goal" :in-theory (enable rec-sourcesp)))))

;; (local
;;  (defthm rec-sourcesp-of-append
;;    (implies (and (rec-sourcesp recs1)
;;                  (rec-sourcesp recs2))
;;             (rec-sourcesp (append recs1 recs2)))
;;    :hints (("Goal" :in-theory (enable rec-sourcesp)))))

;; (local
;;  (defthm rec-sourcesp-forward-to-true-listp
;;    (implies (rec-sourcesp recs)
;;             (true-listp recs))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal" :in-theory (enable rec-sourcesp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmergesort merge-recs-by-confidence merge-sort-recs-by-confidence rec-confidence> recommendationp :extra-theorems nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Records where a symbol "comes from".
(defun symbol-sourcep (source)
  (declare (xargs :guard t))
  (or (eq :built-in source)
      (acl2::book-name-p source) ; string or sysfile
      ))

;; Note that a book name can be a sysfile:
(defund symbol-source-listp (sources)
  (declare (xargs :guard t))
  (if (not (consp sources))
      (null sources)
    (and (symbol-sourcep (first sources))
         (symbol-source-listp (rest sources)))))

;; Maps symbols (e.g., ones occuring in action objects of recommendations) to the books that define them.
(defund symbol-tablep (tab)
  (declare (xargs :guard t))
  (or (eq :unavailable tab) ; todo: eventually remove this case?  Or allow individual symbols to be mapped to :unknown or :top-level?
      (and (symbol-alistp tab)
           (symbol-source-listp (strip-cdrs tab)))))

;; todo: strengthen?
(defund successful-recommendationp (rec)
  (declare (xargs :guard t))
  (and (true-listp rec)
       (= 8 (len rec))
       (let ((name (nth 0 rec)) ; ex: "leidos1"
             (type (nth 1 rec))
             ;; (object (nth 2 rec))
             ;; this (possibly) gets populated when we try the rec:
             (pre-commands (nth 3 rec))
             ;; (theorem-body (nth 4 rec))
             ;; (theorem-hints (nth 5 rec))
             (theorem-otf-flg (nth 6 rec))
             (symbol-table (nth 7 rec)) ; maps each symbol in the action object to its defining book
             )
         (and (stringp name)
              (rec-typep type)
              ;; object
              (pre-commandsp pre-commands)
              ;; theorem-body is an untranslated term
              ;; theorem-hints
              (booleanp theorem-otf-flg)
              (symbol-tablep symbol-table)))))

;; Extract the name from a successful-recommendation.
(defund successful-recommendation-name (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 0 rec))

;; Extract the action type from a successful-recommendation.
(defund successful-recommendation-type (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 1 rec))

;; Extract the action object from a successful-recommendation.
(defund successful-recommendation-object (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 2 rec))

;; Extract the action object from a successful-recommendation.
(defund successful-recommendation-pre-commands (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 3 rec))

;; Extract the symbol-table from a successful-recommendation.
(defund successful-recommendation-symbol-table (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 7 rec))

(local
 (defthm pre-commandsp-of-successful-recommendation-pre-commands
   (implies (successful-recommendationp rec)
            (pre-commandsp (successful-recommendation-pre-commands rec)))
   :hints (("Goal" :in-theory (enable successful-recommendationp
                                      successful-recommendation-pre-commands)))))

(local
 (defthm true-listp-of-successful-recommendation-pre-commands
   (implies (successful-recommendationp rec)
            (true-listp (successful-recommendation-pre-commands rec)))
   :hints (("Goal" :in-theory (enable successful-recommendationp
                                      successful-recommendation-pre-commands)))))

(defund make-successful-rec (name type object pre-commands theorem-body theorem-hints theorem-otf-flg symbol-table)
  (declare (xargs :guard (and (stringp name)
                              (rec-typep type)
                              ;; object
                              (pre-commandsp pre-commands)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (symbol-tablep symbol-table))))
  (list name type object pre-commands theorem-body theorem-hints theorem-otf-flg symbol-table))

(defthm successful-recommendationp-of-make-successful-rec
  (equal (successful-recommendationp (make-successful-rec name type object pre-commands theorem-body theorem-hints theorem-otf-flg symbol-table))
         (and (stringp name)
              (rec-typep type)
              ;; object
              (pre-commandsp pre-commands)
              ;; theorem-body
              ;; theorem-hints
              (booleanp theorem-otf-flg)
              (symbol-tablep symbol-table)))
  :hints (("Goal" :in-theory (enable make-successful-rec successful-recommendationp))))

;; Returns a defthm (or similar) event.
(defund successful-rec-to-simple-defthm (defthm-variant defthm-name rec rule-classes)
  (declare (xargs :guard (and (symbolp defthm-variant) ; defthm or defthmd, etc.
                              (symbolp defthm-name)
                              (successful-recommendationp rec))
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (let* ((theorem-body (nth 4 rec))
         (theorem-hints (nth 5 rec))
         (theorem-otf-flg (nth 6 rec)))
    `(,defthm-variant ,defthm-name
       ,theorem-body
       ,@(and theorem-hints `(:hints ,theorem-hints))
       ,@(and theorem-otf-flg '(:otf-flg t))
       ,@(if (equal rule-classes '(:rewrite))
             nil ; the default, so omit
           `(:rule-classes ,rule-classes)))))

;; Returns an event (a defthm or similar thing, or an encapsulate containing a defthm or similar thing).
(defund successful-rec-to-defthm (defthm-variant ; defthm or defthmd, etc.
                                   defthm-name
                                   rec
                                   rule-classes)
  (declare (xargs :guard (and (symbolp defthm-variant)
                              (symbolp defthm-name)
                              (successful-recommendationp rec))
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (let* ((pre-commands (successful-recommendation-pre-commands rec)))
    (if pre-commands
        `(encapsulate ()
           ,@(acl2::wrap-all 'local pre-commands)
           ,(successful-rec-to-simple-defthm defthm-variant defthm-name rec rule-classes))
      (successful-rec-to-simple-defthm defthm-variant defthm-name rec rule-classes))))

;; Returns a thm event.
(defund successful-rec-to-simple-thm (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (let* ((theorem-body (nth 4 rec))
         (theorem-hints (nth 5 rec))
         (theorem-otf-flg (nth 6 rec)))
    `(thm
      ,theorem-body
      ,@(and theorem-hints `(:hints ,theorem-hints))
      ,@(and theorem-otf-flg '(:otf-flg t)))))

;; Returns an event (a thm or an encapsulate containing a thm).
(defund successful-rec-to-thm (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (let* ((pre-commands (successful-recommendation-pre-commands rec)))
    (if pre-commands
        `(encapsulate ()
           ,@(acl2::wrap-all 'local pre-commands)
           ,(successful-rec-to-simple-thm rec))
      (successful-rec-to-simple-thm rec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund successful-recommendation-listp (recs)
  (declare (xargs :guard t))
  (if (atom recs)
      (null recs)
    (and (successful-recommendationp (first recs))
         (successful-recommendation-listp (rest recs)))))

;; Returns a list of (<action-type> <action-object> <symbol-table>) tuples.
(defund extract-actions-from-successful-recs (recs)
  (declare (xargs :guard (successful-recommendation-listp recs)
                  :verify-guards nil ; done below
                  ))
  (if (endp recs)
      nil
    (let ((rec (first recs)))
      (add-to-set-equal ; ensures no dups (can arise if recs are improved)
       (list (successful-recommendation-type rec)
             (successful-recommendation-object rec)
             (successful-recommendation-symbol-table rec))
       (extract-actions-from-successful-recs (rest recs))))))

(verify-guards extract-actions-from-successful-recs :hints (("Goal" :in-theory (enable successful-recommendation-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *option-names* '(:max-wins))

;; Returns (mv presentp val)
(defund get-advice-option-aux (option-name wrld)
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
    (get-advice-option-aux option-name wrld)
    (if (not presentp)
        (er hard? 'get-advice-option! "Option value not set: ~x0." option-name)
      val)))

;; todo: Or return a table event?
(defund get-advice-option-fn (option-name wrld)
  (declare (xargs :guard (and (symbolp option-name)
                              (plist-worldp wrld))
                  :verify-guards nil ; todo
                  ))
  (if (not (member-eq option-name *option-names*))
      (er hard? 'get-advice-option-fn "Unknown option: ~x0." option-name)
    (let ((val (get-advice-option! option-name wrld)))
      (prog2$ (cw "~x0~%" val)
              '(value-triple :invisible)))))

(defmacro get-advice-option (option-name)
  `(acl2::make-event-quiet (get-advice-option-fn ,option-name (w state))))

(defund set-advice-option-fn (option-name val)
  (declare (xargs :guard (and (symbolp option-name))
                  :verify-guards nil))
  (if (not (member-eq option-name *option-names*))
      (er hard? 'set-advice-option-fn "Unknown option: ~x0." option-name)
    `(table advice-options ,option-name ,val)))

(defmacro set-advice-option (option-name val)
  `(acl2::make-event-quiet (set-advice-option-fn ,option-name ,val)))

(set-advice-option :max-wins nil) ; don't limit the number of successes before we stop trying recs

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
  (declare (xargs :guard (successful-recommendationp rec)
                  :mode :program ; because of fms-to-string
                  ))
  (let* ((type (successful-recommendation-type rec))
         (object (successful-recommendation-object rec))
         (pre-commands (successful-recommendation-pre-commands rec))
         (english-rec (case type
                        (:add-by-hint (fms-to-string-one-line ":by ~x0" (acons #\0 object nil)))
                        (:add-cases-hint (fms-to-string-one-line ":cases ~x0" (acons #\0 object nil)))
                        (:add-disable-hint (fms-to-string-one-line "Disable ~x0" (acons #\0 object nil)))
                        (:add-do-not-hint (fms-to-string-one-line ":do-not ~x0" (acons #\0 object nil)))
                        ;; Same handling for both:
                        ((:add-enable-hint :use-lemma) (fms-to-string-one-line "Enable ~x0" (acons #\0 object nil)))
                        (:add-expand-hint (fms-to-string-one-line ":expand ~x0" (acons #\0 object nil)))
                        (:add-hyp (fms-to-string-one-line "Add the hyp ~x0" (acons #\0 object nil)))
                        (:add-induct-hint (fms-to-string-one-line ":induct ~x0" (acons #\0 object nil)))
                        (:add-library (fms-to-string-one-line "Original theorem" nil))
                        (:add-nonlinearp-hint (fms-to-string-one-line ":nonlinearp ~x0" (acons #\0 object nil)))
                        (:add-use-hint (fms-to-string-one-line ":use ~x0" (acons #\0 object nil)))
                        (:exact-hints (fms-to-string-one-line ":hints ~x0" (acons #\0 object nil)))
                        (t (er hard? 'show-successful-recommendation "Unknown rec type: ~x0." type)))))
    (if pre-commands
        (if (consp (cdr pre-commands))
            ;; More than one pre-command:
            (cw "~s0, after doing ~&1" english-rec pre-commands)
          ;; Exactly one pre-command:
          (cw "~s0, after doing ~x1" english-rec (first pre-commands)))
      (cw "~s0" english-rec))))

;; Always returns nil.
(defun show-successful-recommendations-aux (recs)
  (declare (xargs :guard (successful-recommendation-listp recs)
                  :mode :program))
  (if (endp recs)
      nil
    (let* ((rec (first recs))
           (name (successful-recommendation-name rec)))
      (progn$ (show-successful-recommendation rec)
              (cw " (~S0)~%" name)
              ;; todo: drop the sources:
              ;; (and (< 1 (len sources))
              ;;      (cw "~x0" sources))
              ;;(cw ": ")
              (show-successful-recommendations-aux (rest recs))))))

;; Returns state (because of the change to the margins).
(defun show-successful-recommendations (recs state)
  (declare (xargs :guard (successful-recommendation-listp recs)
                  :mode :program
                  :stobjs state))
  (let ((state (acl2::widen-margins state)))
    (progn$ (show-successful-recommendations-aux recs)
            (cw "~%")
            (let ((state (acl2::unwiden-margins state)))
              state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp include-book-form state).
(defund parse-include-book (string state)
  (declare (xargs :guard (stringp string)
                  :stobjs state))
  (b* (((mv erp form state) (acl2::read-string-as-single-item string "ACL2" state))
       ((when erp) (mv :error-parsing-include-book nil state))
       ((when (not (include-book-formp form)))
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

(defun include-book-form-or-builtin-listp (items)
  (if (atom items)
      (null items)
    (let ((item (first items)))
      (and (or (include-book-formp item)
               (eq :builtin item))
           (include-book-form-or-builtin-listp (rest items))))))

(defthm include-book-form-or-builtin-listp-of-revappend
  (implies (and (include-book-form-or-builtin-listp items1)
                (include-book-form-or-builtin-listp items2))
           (include-book-form-or-builtin-listp (revappend items1 items2)))
  :hints (("Goal" :in-theory (enable include-book-form-or-builtin-listp
                                     revappend))))

(defthm include-book-form-or-builtin-listp-of-reverse
  (implies (include-book-form-or-builtin-listp items)
           (include-book-form-or-builtin-listp (reverse items)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm include-book-form-listp-when-include-book-form-or-builtin-listp
  (implies (and (include-book-form-or-builtin-listp items)
                (not (member-equal :builtin items)))
           (include-book-form-listp items))
  :hints (("Goal" :in-theory (enable include-book-form-listp include-book-form-or-builtin-listp member-equal))))

(defthm include-book-info-listp-of-mv-nth-1-of-parse-book-map-info-list
  (implies (and (not (mv-nth 0 (parse-book-map-info-list list acc state)))
                (include-book-form-or-builtin-listp acc))
           (include-book-form-or-builtin-listp (mv-nth 1 (parse-book-map-info-list list acc state))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-book-map-info-list
                                     parse-include-book))))

;; Returns (mv erp lists state) where each of the LISTS is a list of include-book forms, or the special value :builtin.
(defund parse-book-map-info-lists (lists acc state)
  (declare (xargs :guard (and (acl2::string-list-listp lists)
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

(defthm include-book-info-listp-of-mv-nth-1-of-parse-book-map-info-lists
  (implies (include-book-info-listp acc)
           (include-book-info-listp (mv-nth 1 (parse-book-map-info-lists lists acc state))))
  :hints (("Goal" :in-theory (enable parse-book-map-info-lists include-book-info-listp
                                     include-book-infop))))

;; Returns (mv erp book-map state).
;; This will have a single key for some kinds of rec but not all (e.g., not for :add-hyp).
(defund parse-book-map (book-map state)
  (declare (xargs :stobjs state))
  (if (not (acl2::parsed-json-objectp book-map))
      (mv :ill-formed-book-map nil state)
    (b* ((dict (acl2::parsed-json-object->pairs book-map)) ; strip the :object
         (keys (strip-cars dict))
         ((when (not (string-listp keys))) (mv :ill-formed-book-map nil state))
         (vals (strip-cdrs dict))
         ((when (not (acl2::parsed-json-array-listp vals))) (mv :ill-formed-book-map nil state))
         ((mv erp syms state) (acl2::read-strings-as-single-symbols keys "ACL2" nil state))
         ((when erp) (mv erp nil state))
         ((mv erp lists) (json-arrays-to-lists vals nil))
         ((when erp) (mv erp nil state))
         ((when (not (acl2::string-list-listp lists))) (mv :ill-formed-book-map nil state))
         ((mv erp
              book-lists-for-keys ; each is a list of include-book-forms or :builtin
              state)
          (parse-book-map-info-lists lists nil state))
         ((when erp) (mv erp nil state)))
      (mv nil (pairlis$ syms book-lists-for-keys) state))))

(defthm book-mapp-of-mv-nth-1-of-parse-book-map
  (book-mapp (mv-nth 1 (parse-book-map book-map state)))
  :hints (("Goal" :in-theory (enable parse-book-map))))

(defthm confidence-percentp-of-round-to-hundredths
  (implies (confidence-percentp x)
           (confidence-percentp (acl2::round-to-hundredths x)))
  :hints (("Goal" :in-theory (enable confidence-percentp
                                     acl2::round-to-hundredths
                                     acl2::round-to-integer))))

(local
 (defthm confidence-percentp-of-*-of-100
   (implies (and (<= 0 x)
                 (<= x 1)
                 (rationalp x))
            (confidence-percentp (* 100 x)))
   :hints (("Goal" :in-theory (enable confidence-percentp)))))

;; Returns (mv erp parsed-recommendation state) where parsed-recommendation may
;; be :none (and erp be nil) if a minor error is encountered.
;; The REC should be a JSON object (i.e., a map) whose keys are
;; "type", "object", "confidence", and "book_map".  The name given to
;; the recommendation comes from the SOURCE.
(defund parse-recommendation (rec rec-num source state)
  (declare (xargs :guard (and (acl2::parsed-json-valuep rec)
                              (natp rec-num)
                              (model-namep source))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-json-objectp)))))
  (if (not (acl2::parsed-json-objectp rec))
      (progn$ (er hard? 'parse-recommendation "Bad rec: ~x0." rec)
              (mv :bad-rec nil state))
    (b* ((dict (acl2::parsed-json-object->pairs rec)) ; strip the :object
         (type (acl2::lookup-equal "type" dict))
         (object (acl2::lookup-equal "object" dict))
         (confidence (acl2::lookup-equal "confidence" dict))
         (book-map (acl2::lookup-equal "book_map" dict))
         ((mv erp book-map state) (parse-book-map book-map state))
         ((when erp)
          (cw "WARNING: When parsing book map: ~x0.~%" erp)
          (mv nil ; supressing this error for now
              :none state))
         ((when (or (not (rationalp confidence))
                    (< confidence 0)
                    (< 1 confidence)))
          (er hard? 'parse-recommendation "Bad confidence: ~x0." confidence)
          (mv :bad-confidence nil state))
         (confidence-percent (acl2::round-to-hundredths (* 100 confidence)))
         (res (assoc-equal type *rec-to-symbol-alist*))
         ((when (not res))
          (er hard? 'parse-recommendation "Unknown recommendation type: ~x0." type)
          (mv :unknown-rec-type nil state))
         (type-keyword (cdr res))
         ((when (not (stringp object)))
          (er hard? 'parse-recommendation "Non-string object: ~x0" object)
          (mv :bad-rec nil state))
         ((mv erp parsed-object state) (acl2::read-string-as-single-item object "ACL2" state))
         ((when erp)
          (cw " Error (~x0) parsing action object for ~x1: ~x2.~%" erp type object)
          (mv nil ;; :none :parse-error
              :none state))
         (name (concatenate 'string (model-to-nice-string source) "[" (acl2::nat-to-string rec-num) "]")))
      (mv nil ; no error
          (make-rec name type-keyword parsed-object confidence-percent book-map)
          state))))

;; Returns (mv erp parsed-recommendations state).
(defund parse-recommendations-aux (recs rec-num source acc state)
  (declare (xargs :guard (and (acl2::parsed-json-valuesp recs)
                              (natp rec-num)
                              (model-namep source)
                              (true-listp acc))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-json-valuesp)))))
  (if (endp recs)
      (mv nil (reverse acc) state)
    (b* (((mv erp parsed-recommendation state) (parse-recommendation (first recs) rec-num source state))
         ((when erp) (mv erp nil state)))
      (parse-recommendations-aux (rest recs)
                                 (+ 1 rec-num)
                                 source
                                 (if (eq :none parsed-recommendation)
                                     acc ; omit bad rec
                                   (cons parsed-recommendation acc))
                                 state))))

;; Returns (mv erp parsed-recommendations state).
(defund parse-recommendations (recs source state)
  (declare (xargs :guard (and (acl2::parsed-json-valuesp recs)
                              (model-namep source))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-json-arrayp)))))
  (parse-recommendations-aux recs 1 source nil state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: update this if other kinds of failure-info become supported.
(defun cw-failure-message (snippet failure-info)
  (if (eq failure-info :step-limit-reached)
      (cw "fail (~s0: step limit reached)~%" snippet)
    (if (eq failure-info :time-limit-reached)
        (cw "fail (~s0: time limit reached)~%" snippet)
      (cw "fail (~s0)~%" snippet))))

(defun cw-success-message (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :mode :program))
  (progn$ (cw "SUCCESS: ")
          (show-successful-recommendation rec)
          (cw "~%")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An interface to prove$ that doesn't pass back errors (instead printing a message).
;; Returns (mv provedp state).  Does not propagate any errors back.
(defund prove$-no-error (ctx term hints otf-flg step-limit
                             time-limit ; warning: not portable!
                             state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit)))
                  :mode :program
                  :stobjs state))
  (mv-let (erp provedp state)
    (acl2::prove$ term :hints hints :otf-flg otf-flg :step-limit step-limit :time-limit time-limit)
    (if erp
        (prog2$ (cw "Syntax error in prove$ call (made by ~x0).~%" ctx)
                (mv nil state))
      (mv provedp state))))

;; Returns (mv provedp failure-info state), where failure-info may be
;; :step-limit-reached, :time-limit-reached, or :unknown.
(defund prove$-no-error-with-failure-info (ctx term hints otf-flg step-limit
                                               time-limit ; warning: not portable!
                                               state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit)))
                  :mode :program
                  :stobjs state))
  (mv-let (erp provedp failure-info state)
    ;; TODO: Drop the :time-limit once :step-limit can interrupt subsumption:
    (acl2::prove$+ term :hints hints :otf-flg otf-flg :step-limit step-limit :time-limit time-limit :print nil)
    (if erp
        (prog2$ (cw "Syntax error in prove$ call (made by ~x0).~%" ctx)
                (mv nil nil state))
      (mv provedp failure-info state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Do this better?  Ask Matt.
(defund sysfile-from-include-book-form (form)
  (declare (xargs :guard (and (true-listp form)
                              (consp (cdr form))
                              (eq 'include-book (car form))
                              (stringp (cadr form)))))
  (if (not (equal (cddr form) '(:dir :system)))
      (er hard? 'sysfile-from-include-book-form "Unexpected include-book form: ~x0." form)
    (cons :system (concatenate 'string (cadr form) ".lisp"))))

;; The result maps each of the FNS to a sysfile, or a string, or :built-in, or
;; :top-level, or nil.
(defun symbol-table-for-fns (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))
                  :mode :program))
  (if (endp fns)
      nil
    (acons (first fns)
           (acl2::book-of-event (first fns) wrld)
           (symbol-table-for-fns (rest fns) wrld))))

(defund symbol-table-for-term (term wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))
                  :mode :program))
  (let ((fns (acl2::all-fnnames term)))
    (symbol-table-for-fns fns wrld)))

;; Returns a book-name (sysfile or string) or :built-in or :top-level or nil.
;; Converts :top-level to the current-book when current-book-absolute-path is non-nil.
(defun event-source (name current-book-absolute-path wrld)
  (declare (xargs :guard (and (symbolp name)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (plist-worldp wrld))
                  :mode :program))
  (let ((res (acl2::book-of-event name wrld)))
    (if (and (eq :top-level res)
             current-book-absolute-path)
        (acl2::filename-to-book-name current-book-absolute-path wrld)
      res)))

;; Builds a symbol-table with a single entry.
;; Converts :top-level to the current-book when current-book-absolute-path is non-nil.
(defun symbol-table-for-event (name current-book-absolute-path wrld)
  (declare (xargs :guard (and (symbolp name)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (plist-worldp wrld))
                  :mode :program))
  (let ((event-source (event-source name current-book-absolute-path wrld)))
    (if (eq :top-level event-source)
        :unavailable
      (acons name event-source nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Calls prove$ on FORMULA after submitting INCLUDE-BOOK-FORM, which is undone after the prove$.
;; ;; Returns (mv erp provedp state).  If NAME-TO-CHECK is non-nil, we require it to be defined
;; ;; after including the book (and to be the name of something appropriate, according to CHECK-KIND)
;; ;; or else we give up without calling prove$.
;; ;; TODO: Consider trying the proof anyway, even if the include-book doesn't bring
;; ;; in the name-to-check, since the proof attempt may be cheap compared to the include-book.
;; ;; How often does this happen?
;; ;; TODO: Drop the error return-value?
;; (defun prove$-with-include-book (ctx ; context (gets printed as-is, so not really a ctxp)
;;                                  formula ; untranslated
;;                                  include-book-form
;;                                  name-to-check ; we ensure this exists after the include-book (nil means nothing to check)
;;                                  check-kind    ; :enable or :use
;;                                  book-to-avoid-absolute-path ; immediately fail if the include-book causes this book to be brought in (nil means nothing to check)
;;                                  ;; args to prove$:
;;                                  hints otf-flg step-limit
;;                                  state)
;;   (declare (xargs :guard (and ;; ctx
;;                           ;; formula
;;                           (consp include-book-form)
;;                           (eq 'include-book (car include-book-form))
;;                           (symbolp name-to-check)
;;                           (or (null check-kind)
;;                               (eq :enable check-kind)
;;                               (eq :use check-kind))
;;                           (or (null book-to-avoid-absolute-path)
;;                               (stringp book-to-avoid-absolute-path))
;;                           ;; hints
;;                           (booleanp otf-flg)
;;                           (or (eq nil step-limit)
;;                               (natp step-limit)))
;;                   :stobjs state
;;                   :mode :program))
;;   (revert-world ;; ensures the include-book gets undone
;;    (b* (        ;; Try to include the recommended book:
;;         ((mv erp state) (acl2::submit-event include-book-form nil nil state))
;;         ((when erp) ; can happen if there is a name clash
;;          (cw "NOTE: Event failed (possible name clash): ~x0.~%" include-book-form)
;;          (mv nil ; suppresses error (we want to continue trying other include-books / other advice)
;;              nil state))
;;         ((when (and name-to-check
;;                     (if (eq :enable check-kind)
;;                         (not (item-that-can-be-enabled/disabledp name-to-check (w state)))
;;                       (if (eq :use check-kind)
;;                           (not (symbol-that-can-be-usedp name-to-check (w state)))
;;                         (er hard? 'prove$-with-include-book "Bad check-kind: ~x0." check-kind)))))
;;          (cw "NOTE: After ~x0, ~x1 is not defined or is not suitable.~%" include-book-form name-to-check) ;; todo: add debug arg
;;          (mv nil ; suppresses error
;;              nil state))
;;         ;; Check that we didn't bring in the book-to-avoid:
;;         ((when (member-equal book-to-avoid-absolute-path (acl2::all-included-books (w state))))
;;          (cw "NOTE: Avoiding include-book, ~x0, that would bring in the book-to-avoid.~%" include-book-form)
;;          (mv nil nil state))
;;         ;; The include-book brought in the desired name, so now try the proof:
;;         ((mv provedp state) (prove$-no-error ctx formula hints otf-flg step-limit state)))
;;      (mv nil ; suppresses any error from prove$
;;          provedp state))))

;; ;; Try to prove FORMULA after submitting each of the INCLUDE-BOOK-FORMS (separately).
;; ;; Returns (mv erp successful-include-book-form-or-nil state).
;; ;; TODO: Don't return erp if we will always suppress errors.
;; (defun try-prove$-with-include-books (ctx
;;                                       formula ; untranslated
;;                                       include-book-forms
;;                                       name-to-check
;;                                       check-kind
;;                                       book-to-avoid-absolute-path
;;                                       ;; args to prove$:
;;                                       hints otf-flg step-limit
;;                                       state)
;;   (declare (xargs :guard (and ;; ctx
;;                           ;; formula
;;                           (true-listp include-book-forms) ; todo: strengthen
;;                           (symbolp name-to-check)
;;                           (or (null check-kind)
;;                               (eq :enable check-kind)
;;                               (eq :use check-kind))
;;                           (or (null book-to-avoid-absolute-path)
;;                               (stringp book-to-avoid-absolute-path))
;;                           ;; hints
;;                           (booleanp otf-flg)
;;                           (or (eq nil step-limit)
;;                               (natp step-limit)))
;;                   :stobjs state :mode :program))
;;   (if (endp include-book-forms)
;;       (mv nil nil state)
;;     (b* ((form (first include-book-forms))
;;          ;; (- (cw "  Trying with ~x0.~%" form))
;;          ((mv & ; erp ; suppress errors from prove$-with-include-book (TODO: Why?)
;;               provedp state)
;;           (prove$-with-include-book ctx formula
;;                                     form
;;                                     name-to-check
;;                                     check-kind
;;                                     book-to-avoid-absolute-path
;;                                     ;; args to prove$:
;;                                     hints otf-flg step-limit
;;                                     state))
;;          ;; ((when erp) (mv erp nil state))
;;          ((when provedp) (mv nil form state)))
;;       (try-prove$-with-include-books ctx
;;                                      formula
;;                                      (rest include-book-forms)
;;                                      name-to-check
;;                                      check-kind
;;                                      book-to-avoid-absolute-path
;;                                      ;; args to prove$:
;;                                      hints otf-flg step-limit
;;                                      state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to prove THEOREM-BODY by enabling ITEM-TO-ENABLE after submitting INCLUDE-BOOK-FORM.
;; The include-book is undone before this returns.
;; Returns (mv maybe-successful-rec state).
;; TODO: Consider trying the proof anyway, even if the include-book doesn't bring
;; in the name-to-check, since the proof attempt may be cheap compared to the include-book.
(defun try-enable-with-include-book (include-book-form
                                     theorem-body        ; untranslated
                                     item-to-enable ; a symbol or rune
                                     current-book-absolute-path ; immediately fail if the include-book causes this book to be brought in (nil means nothing to check)
                                     avoid-current-bookp
                                     theorem-name ; may be :thm
                                     ;; args to prove$:
                                     hints otf-flg step-limit time-limit
                                     rec-name
                                     improve-recsp
                                     state)
  (declare (xargs :guard (and (consp include-book-form)
                              (eq 'include-book (car include-book-form)) ; strengthen?
                              ;; theorem-body is untranslated
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; hints are standard hints
                              (booleanp otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (stringp rec-name)
                              (booleanp improve-recsp))
                  :stobjs state
                  :mode :program))
  (b* ((name-to-enable (if (symbolp item-to-enable)
                           item-to-enable
                         (cadr item-to-enable) ; must be a rune
                         ))
       ((mv & ; ignore errors
            maybe-successful-rec state)
        (revert-world ;; ensures the include-book gets undone
         (b* (        ; Try to include the recommended book:
              ((mv erp state) (acl2::submit-event include-book-form nil nil state))
              ((when erp) ; can happen if there is a name clash
               (cw "NOTE: Event failed (name clash? uncertified book?): ~x0.~%" include-book-form)
               (mv nil nil state))
              ;; Check that we didn't bring in the current-book:
              ((when (and avoid-current-bookp
                          current-book-absolute-path
                          (member-equal current-book-absolute-path (acl2::all-included-books (w state)))))
               (cw "NOTE: Avoiding include-book, ~x0, that would bring in the current-book.~%" include-book-form)
               (mv nil nil state))
              ;; Check whether the include-book brought in the name being defined:
              ;; todo: maybe check also back in the original world
              ;; todo: do better if redundant!
              (name-clashp (and (not (eq :thm theorem-name))
                                (not (acl2::new-namep theorem-name (w state))))))
           (if (not (item-that-can-be-enabled/disabledp name-to-enable (w state)))
               ;; The item either didn't get brought in or is the wrong kind of thing, so fail:
               (prog2$ (cw "NOTE: After ~x0, ~x1 is not defined or is not suitable for enabling.~%" include-book-form name-to-enable) ;; todo: add debug arg and only print in that case
                       (mv nil nil state))
             ;; The include-book brought in the desired name (and that thing can be enabled), so now try the proof, enabling the item:
             ;; TTODO: Check if already enabled!
             (b* ((hints-with-enable (acl2::enable-items-in-hints hints (list item-to-enable) t)) ; t means use enable*
                  ((mv provedp state) (prove$-no-error 'try-enable-with-include-book theorem-body hints-with-enable otf-flg step-limit time-limit state)))
               (if provedp
                   ;; We proved it with the enable hint.  Now, try again without the enable (just the include-book):
                   (b* (((mv provedp state)
                         (if improve-recsp
                             (prove$-no-error 'try-enable-with-include-book theorem-body
                                              hints ; original hints
                                              otf-flg
                                              step-limit time-limit ; or base this on how many steps were taken when it succeeded
                                              state)
                           (mv nil state))))
                     (if provedp
                         ;; Only the include-book was needed:
                         ;; Turn the rec into an :add-library, because the library is what mattered:
                         ;; todo: we could even try to see if a smaller library would work
                         (let ((rec-name (concatenate 'string rec-name ".improved") ; we modified the rec
                                         )
                               (rec-type :add-library ;; Change the rec to :add-library since the hint didn't matter!
                                         ))
                           (mv nil
                               (if name-clashp
                                   (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                                        (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                                     (make-successful-rec rec-name
                                                          rec-type
                                                          include-book-form ; action object for :add-library
                                                          ;; pre-commands:
                                                          ;; since there is a name clash, we make a copy and prove the copy using the include-book
                                                          ;; then we prove the desired theorem using the copy
                                                          (list `(encapsulate ()
                                                                   (local ,include-book-form)
                                                                   (defthm ,defthm-copy-name
                                                                     ,theorem-body
                                                                     :rule-classes nil ; in case it's not a legal rule
                                                                     :hints ,hints ; we checked above that these hints work
                                                                     :otf-flg ,otf-flg)))
                                                          theorem-body
                                                          `(("Goal" :by ,defthm-copy-name))
                                                          nil ; otf-flg
                                                          nil ; symbol-table
                                                          ))
                                 (make-successful-rec rec-name
                                                      rec-type
                                                      include-book-form ; action object for :add-library
                                                      ;; pre-commands:
                                                      (list include-book-form)
                                                      theorem-body
                                                      hints ; original hints, no new enable
                                                      otf-flg
                                                      nil ; symbol-table
                                                      ))
                               state))
                       ;; Both the include-book and the enable were needed:
                       (mv nil
                           (if name-clashp
                               (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                                    (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                                 (make-successful-rec rec-name
                                                      :add-enable-hint
                                                      item-to-enable
                                                      ;; pre-commands:
                                                      (list `(encapsulate ()
                                                               (local ,include-book-form)
                                                               (defthm ,defthm-copy-name
                                                                 ,theorem-body
                                                                 :rule-classes nil ; in case it's not a legal rule
                                                                 :hints ,hints-with-enable ; we checked above that these hints work
                                                                 :otf-flg ,otf-flg)))
                                                      theorem-body
                                                      `(("Goal" :by ,defthm-copy-name))
                                                      nil ; otf-flg
                                                      ;; The book here may not be where the name-to-enable is actually defined:
                                                      (acons name-to-enable (sysfile-from-include-book-form include-book-form) nil)))
                             (make-successful-rec rec-name
                                                  :add-enable-hint
                                                  item-to-enable
                                                  (list include-book-form) ; pre-commands
                                                  theorem-body
                                                  hints-with-enable
                                                  otf-flg
                                                  ;; The book here may not be where the name-to-enable is actually defined:
                                                  (acons name-to-enable (sysfile-from-include-book-form include-book-form) nil)))
                             state)))
                 ;; Failed to prove, even with the enable (we could try without the enable, but it doesn't seem worth it):
                 (mv nil nil state))))))))
    (mv maybe-successful-rec state)))

;; Tries to find one of the INCLUDE-BOOK-FORMS that brings in the ITEM-TO-ENABLE and can prove THEOREM-BODY after enabling the ITEM-TO-ENABLE.
;; Returns (mv maybe-successful-rec book-limit-reachedp state).
;; May improve the recommendation if the include-book alone suffices (without the enable).
(defun try-enable-with-include-books (include-book-forms
                                      theorem-body   ; untranslated
                                      item-to-enable ; may be a rune
                                      include-book-count ; number of include-books already tried
                                      maybe-max-include-book-count
                                      current-book-absolute-path
                                      avoid-current-bookp
                                      theorem-name ; may be :thm
                                      ;; args to prove$:
                                      hints ; will be augmented with an enable of the item-to-enable
                                      otf-flg
                                      step-limit time-limit
                                      rec-name
                                      improve-recsp
                                      state)
  (declare (xargs :guard (and (true-listp include-book-forms) ; todo: strengthen
                              ;; theorem-body is untranslated
                              (natp include-book-count)
                              (or (null maybe-max-include-book-count)
                                  (natp maybe-max-include-book-count))
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              ;; hints are just regular hints
                              (booleanp otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (stringp rec-name)
                              (booleanp improve-recsp))
                  :stobjs state :mode :program))
  (if (endp include-book-forms)
      (mv nil nil state) ; no rec, did not reach the limit
    (if (and maybe-max-include-book-count
             (<= maybe-max-include-book-count include-book-count))
        (mv nil t state) ; no rec, and we reached the limit
      (b* ((include-book-form (first include-book-forms))
           ;; (- (cw "  Trying with ~x0.~%" form))
           ((mv maybe-successful-rec state)
            (try-enable-with-include-book include-book-form theorem-body item-to-enable current-book-absolute-path avoid-current-bookp theorem-name hints otf-flg step-limit time-limit rec-name improve-recsp state)))
        (if maybe-successful-rec
            (mv maybe-successful-rec nil state)
          (try-enable-with-include-books (rest include-book-forms)
                                         theorem-body
                                         item-to-enable
                                         (+ 1 include-book-count)
                                         maybe-max-include-book-count current-book-absolute-path avoid-current-bookp theorem-name hints otf-flg step-limit time-limit rec-name improve-recsp state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to prove THEOREM-BODY by :use-ing ITEM-TO-ENABLE after submitting INCLUDE-BOOK-FORM.
;; The include-book is undone before this returns.
;; Returns (mv maybe-successful-rec state).
;; TODO: Consider trying the proof anyway, even if the include-book doesn't bring
;; in the name-to-check, since the proof attempt may be cheap compared to the include-book.
(defun try-use-with-include-book (include-book-form
                                  theorem-body     ; untranslated
                                  item-to-use ; a lemma-instance
                                  name-to-use ; extracted from the item-to-use
                                  current-book-absolute-path ; immediately fail if the include-book causes this book to be brought in (nil means nothing to check)
                                  avoid-current-bookp
                                  theorem-name ; may be :thm
                                  ;; args to prove$:
                                  hints otf-flg step-limit time-limit
                                  rec-name
                                  improve-recsp
                                  state)
  (declare (xargs :guard (and (consp include-book-form)
                              (eq 'include-book (car include-book-form)) ; strengthen?
                              ;; theorem-body is untranslated
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; hints are standard hints
                              (booleanp otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (stringp rec-name)
                              (booleanp improve-recsp))
                  :stobjs state
                  :mode :program))
  (b* (((mv & ; ignore errors
            maybe-successful-rec state)
        (revert-world ;; ensures the include-book gets undone
         (b* (        ; Try to include the recommended book:
              ((mv erp state) (acl2::submit-event include-book-form nil nil state))
              ((when erp) ; can happen if there is a name clash
               (cw "NOTE: Event failed (possible name clash): ~x0.~%" include-book-form)
               (mv nil nil state))
              ;; Check that we didn't bring in the current-book:
              ((when (and avoid-current-bookp
                          current-book-absolute-path
                          (member-equal current-book-absolute-path (acl2::all-included-books (w state)))))
               (cw "NOTE: Avoiding include-book, ~x0, that would bring in the current-book.~%" include-book-form)
               (mv nil nil state))
              ;; Check whether the include-book brought in the name being defined:
              ;; todo: maybe check also back in the original world
              ;; todo: do better if redundant!
              (name-clashp (and (not (eq :thm theorem-name))
                                (not (acl2::new-namep theorem-name (w state))))))
           (if (not (symbol-that-can-be-usedp name-to-use (w state)))
               ;; The item either didn't get brought in or is the wrong kind of thing, so fail:
               (prog2$ (cw "NOTE: After ~x0, ~x1 is not defined or is not suitable for :use-ing.~%" include-book-form name-to-use) ;; todo: add debug arg and only print in that case
                       (mv nil nil state))
             ;; The include-book brought in the desired name (and that thing can be :used), so now try the proof, :use-ing the item:
             (b* ( ; todo: ensure this is nice:
                  ;; todo: also disable the item, if appropriate
                  (hints-with-use (acl2::merge-hint-setting-into-goal-hint :use item-to-use hints))
                  ((mv provedp state) (prove$-no-error 'try-use-with-include-book theorem-body hints-with-use otf-flg step-limit time-limit state)))
               (if provedp
                   ;; We proved it with the :use hint.  Now, try again without the :use (just the include-book):
                   (b* (((mv provedp state)
                         (if improve-recsp
                             (prove$-no-error 'try-use-with-include-book theorem-body
                                              hints ; original hints
                                              otf-flg
                                              step-limit time-limit ; or base this on how many steps were taken when it succeeded
                                              state)
                           (mv nil state))))
                     (if provedp
                         ;; Only the include-book was needed:
                         ;; Turn the rec into an :add-library, because the library is what mattered:
                         ;; todo: we could even try to see if a smaller library would work
                         (let ((rec-name (concatenate 'string rec-name ".improved") ; we modified the rec
                                         )
                               (rec-type :add-library ;; Change the rec to :add-library since the hint didn't matter!
                                         ))
                           (mv nil
                               (if name-clashp
                                   (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                                        (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                                     (make-successful-rec rec-name
                                                          rec-type
                                                          include-book-form ; action object for :add-library
                                                          ;; pre-commands:
                                                          ;; since there is a name clash, we make a copy and prove the copy using the include-book
                                                          ;; then we prove the desired theorem using the copy
                                                          (list `(encapsulate ()
                                                                   (local ,include-book-form)
                                                                   (defthm ,defthm-copy-name
                                                                     ,theorem-body
                                                                     :rule-classes nil ; in case it's not a legal rule
                                                                     :hints ,hints ; we checked above that these hints work
                                                                     :otf-flg ,otf-flg)))
                                                          theorem-body
                                                          `(("Goal" :by ,defthm-copy-name))
                                                          nil ; otf-flg
                                                          nil ; symbol-table
                                                          ))
                                 (make-successful-rec rec-name
                                                      rec-type
                                                      include-book-form ; action object for :add-library
                                                      ;; pre-commands:
                                                      (list include-book-form)
                                                      theorem-body
                                                      hints ; original hints, no new :use
                                                      otf-flg
                                                      nil ; symbol-table
                                                      ))
                               state))
                       ;; Both the include-book and the :use were needed:
                       (mv nil
                           (if name-clashp
                               (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                                    (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                                 (make-successful-rec rec-name
                                                      :add-use-hint
                                                      item-to-use
                                                      ;; pre-commands:
                                                      (list `(encapsulate ()
                                                               (local ,include-book-form)
                                                               (defthm ,defthm-copy-name
                                                                 ,theorem-body
                                                                 :rule-classes nil ; in case it's not a legal rule
                                                                 :hints ,hints-with-use ; we checked above that these hints work
                                                                 :otf-flg ,otf-flg)))
                                                      theorem-body
                                                      `(("Goal" :by ,defthm-copy-name))
                                                      nil ; otf-flg
                                                      ;; The book here may not be where the name-to-use is actually defined:
                                                      (acons name-to-use (sysfile-from-include-book-form include-book-form) nil)
                                                      ))
                             (make-successful-rec rec-name
                                                  :add-use-hint
                                                  item-to-use
                                                  (list include-book-form) ; pre-commands
                                                  theorem-body
                                                  hints-with-use
                                                  otf-flg
                                                  ;; The book here may not be where the name-to-use is actually defined:
                                                  (acons name-to-use (sysfile-from-include-book-form include-book-form) nil)))
                           state)))
                 ;; Failed to prove, even with the :use (we could try without the use, but it doesn't seem worth it):
                 (mv nil nil state))))))))
    (mv maybe-successful-rec state)))

;; Tries to find one of the INCLUDE-BOOK-FORMS that brings in the ITEM-TO-USE and can prove THEOREM-BODY after :use-ing the ITEM-TO-USE.
;; Returns (mv maybe-successful-rec limit-reachedp state).
;; May improve the recommendation if the include-book alone suffices (without the :use).
;; TODO: Return an print how many books we found it in.
(defun try-use-with-include-books (include-book-forms
                                   theorem-body           ; untranslated
                                   item-to-use ; a lemma-instance
                                   name-to-use ; extracted from the item-to-use
                                   include-book-count ; number of include-books already tried
                                   maybe-max-include-book-count
                                   current-book-absolute-path
                                   avoid-current-bookp
                                   theorem-name ; may be :thm
                                   ;; args to prove$:
                                   hints ; will be augmented with a :use of the item-to-use
                                   otf-flg
                                   step-limit time-limit
                                   rec-name
                                   improve-recsp
                                   state)
  (declare (xargs :guard (and (true-listp include-book-forms) ; todo: strengthen
                              ;; theorem-body is untranslated
                              (natp include-book-count)
                              (or (null maybe-max-include-book-count)
                                  (natp maybe-max-include-book-count))
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              ;; hints are just regular hints
                              (booleanp otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (stringp rec-name)
                              (booleanp improve-recsp)
                              (symbolp name-to-use))
                  :stobjs state :mode :program))
  (if (endp include-book-forms)
      (mv nil nil state)
    (if (and maybe-max-include-book-count
             (<= maybe-max-include-book-count include-book-count))
        (mv nil t state)
      (b* ((include-book-form (first include-book-forms))
           ;; (- (cw "  Trying with ~x0.~%" form))
           ((mv maybe-successful-rec state)
            (try-use-with-include-book include-book-form theorem-body item-to-use name-to-use current-book-absolute-path avoid-current-bookp theorem-name hints otf-flg step-limit time-limit rec-name improve-recsp state)))
        (if maybe-successful-rec
            (mv maybe-successful-rec nil state)
          (try-use-with-include-books (rest include-book-forms)
                                      theorem-body
                                      item-to-use name-to-use
                                      (+ 1 include-book-count)
                                      maybe-max-include-book-count current-book-absolute-path avoid-current-bookp theorem-name hints otf-flg step-limit time-limit rec-name improve-recsp state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to prove THEOREM-BODY by :induct ITEM-TO-ENABLE after submitting INCLUDE-BOOK-FORM.
;; The include-book is undone before this returns.
;; Returns (mv maybe-successful-rec state).
;; TODO: Consider trying the proof anyway, even if the include-book doesn't bring
;; in the name-to-check, since the proof attempt may be cheap compared to the include-book.
(defun try-induct-with-include-book (include-book-form
                                     theorem-body ; untranslated
                                     induct-term  ; a term
                                     name-to-induct ; extracted from the induct-term
                                     current-book-absolute-path ; immediately fail if the include-book causes this book to be brought in (nil means nothing to check)
                                     avoid-current-bookp
                                     theorem-name ; may be :thm
                                     ;; args to prove$:
                                     hints otf-flg step-limit time-limit
                                     rec-name
                                     improve-recsp
                                     state)
  (declare (xargs :guard (and (consp include-book-form)
                              (eq 'include-book (car include-book-form)) ; strengthen?
                              ;; theorem-body is untranslated
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; hints are standard hints
                              (booleanp otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (stringp rec-name)
                              (booleanp improve-recsp))
                  :stobjs state
                  :mode :program))
  (b* (((mv & ; ignore errors
            maybe-successful-rec state)
        (revert-world ;; ensures the include-book gets undone
         (b* (        ; Try to include the recommended book:
              ((mv erp state) (acl2::submit-event include-book-form nil nil state))
              ((when erp) ; can happen if there is a name clash
               (cw "NOTE: Event failed (possible name clash): ~x0.~%" include-book-form)
               (mv nil nil state))
              ;; Check that we didn't bring in the current-book:
              ((when (and avoid-current-bookp
                          current-book-absolute-path
                          (member-equal current-book-absolute-path (acl2::all-included-books (w state)))))
               (cw "NOTE: Avoiding include-book, ~x0, that would bring in the current-book.~%" include-book-form)
               (mv nil nil state))
              ;; Check whether the include-book brought in the name being defined:
              ;; todo: maybe check also back in the original world
              ;; todo: do better if redundant!
              (name-clashp (and (not (eq :thm theorem-name))
                                (not (acl2::new-namep theorem-name (w state))))))
           (if (not (acl2::recursivep name-to-induct nil (w state))) ; todo: generalize if the induct-term is not just a function call?
               ;; The item either didn't get brought in or is the wrong kind of thing, so fail:
               (prog2$ (cw "NOTE: After ~x0, ~x1 is undefined or unsuitable for :induct.~%" include-book-form name-to-induct) ;; todo: add debug arg and only print in that case
                       (mv nil nil state))
             ;; The include-book brought in the desired name (and that thing can be used with :induct), so now try the proof, with :induct item:
             (b* ((hints-with-induct (acl2::merge-hint-setting-into-goal-hint :induct induct-term hints))
                  ;; todo: switch arg order of enable-items-in-hints:
                  (hints-with-induct (acl2::enable-items-in-hints hints-with-induct (list name-to-induct ; :induction rule and definition
                                                                                          ;;`(:i ,name-to-induct)
                                                                                          ) t))
                  ((mv provedp state) (prove$-no-error 'try-induct-with-include-book theorem-body hints-with-induct otf-flg step-limit time-limit state)))
               (if provedp
                   ;; We proved it with the :induct hint.  Now, try again without the :induct (just the include-book):
                   (b* (((mv provedp state)
                         (if improve-recsp
                             (prove$-no-error 'try-induct-with-include-book theorem-body
                                              hints ; original hints
                                              otf-flg
                                              step-limit time-limit ; or base this on how many steps were taken when it succeeded
                                              state)
                           (mv nil state))))
                     (if provedp
                         ;; Only the include-book was needed:
                         ;; Turn the rec into an :add-library, because the library is what mattered:
                         ;; todo: we could even try to see if a smaller library would work
                         (let ((rec-name (concatenate 'string rec-name ".improved") ; we modified the rec
                                         )
                               (rec-type :add-library ;; Change the rec to :add-library since the hint didn't matter!
                                         ))
                           (mv nil
                               (if name-clashp
                                   (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                                        (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                                     (make-successful-rec rec-name
                                                          rec-type
                                                          include-book-form ; action object for :add-library
                                                          ;; pre-commands:
                                                          ;; since there is a name clash, we make a copy and prove the copy using the include-book
                                                          ;; then we prove the desired theorem using the copy
                                                          (list `(encapsulate ()
                                                                   (local ,include-book-form)
                                                                   (defthm ,defthm-copy-name
                                                                     ,theorem-body
                                                                     :rule-classes nil ; in case it's not a legal rule
                                                                     :hints ,hints ; we checked above that these hints work
                                                                     :otf-flg ,otf-flg)))
                                                          theorem-body
                                                          `(("Goal" :by ,defthm-copy-name))
                                                          nil ; otf-flg
                                                          nil ; symbol-table
                                                          ))
                                 (make-successful-rec rec-name
                                                      rec-type
                                                      include-book-form ; action object for :add-library
                                                      ;; pre-commands:
                                                      (list include-book-form)
                                                      theorem-body
                                                      hints ; original hints, no new :induct
                                                      otf-flg
                                                      nil ; symbol-table
                                                      ))
                               state))
                       ;; Both the include-book and the :induct were needed:
                       (mv nil
                           (if name-clashp
                               (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                                    (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                                 (make-successful-rec rec-name
                                                      :add-induct-hint
                                                      induct-term
                                                      ;; pre-commands:
                                                      (list `(encapsulate ()
                                                               (local ,include-book-form)
                                                               (defthm ,defthm-copy-name
                                                                 ,theorem-body
                                                                 :rule-classes nil ; in case it's not a legal rule
                                                                 :hints ,hints-with-induct ; we checked above that these hints work
                                                                 :otf-flg ,otf-flg)))
                                                      theorem-body
                                                      `(("Goal" :by ,defthm-copy-name))
                                                      nil ; otf-flg
                                                      ;; The book here may not be where the name-to-induct is actually defined:
                                                      (acons name-to-induct (sysfile-from-include-book-form include-book-form) nil)
                                                      ))
                             (make-successful-rec rec-name
                                                  :add-induct-hint
                                                  induct-term
                                                  (list include-book-form) ; pre-commands
                                                  theorem-body
                                                  hints-with-induct
                                                  otf-flg
                                                  ;; The book here may not be where the name-to-induct is actually defined:
                                                  (acons name-to-induct (sysfile-from-include-book-form include-book-form) nil)))
                           state)))
                 ;; Failed to prove, even with the :induct (we could try without the induct, but it doesn't seem worth it):
                 (mv nil nil state))))))))
    (mv maybe-successful-rec state)))

;; Tries to find one of the INCLUDE-BOOK-FORMS that brings in the INDUCT-TERM and can prove THEOREM-BODY after :induct with the INDUCT-TERM.
;; Returns (mv maybe-successful-rec limit-reachedp state).
;; May improve the recommendation if the include-book alone suffices (without the :induct).
;; TODO: Return an print how many books we found it in.
(defun try-induct-with-include-books (include-book-forms
                                      theorem-body ; untranslated
                                      induct-term  ; a term
                                      name-to-induct ; extracted from the induct-term
                                      include-book-count ; number of include-books already tried
                                      maybe-max-include-book-count
                                      current-book-absolute-path
                                      avoid-current-bookp
                                      theorem-name ; may be :thm
                                      ;; args to prove$:
                                      hints ; will be augmented with a :induct of the induct-term
                                      otf-flg
                                      step-limit time-limit
                                      rec-name
                                      improve-recsp
                                      state)
  (declare (xargs :guard (and (true-listp include-book-forms) ; todo: strengthen
                              ;; theorem-body is untranslated
                              (natp include-book-count)
                              (or (null maybe-max-include-book-count)
                                  (natp maybe-max-include-book-count))
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              ;; hints are just regular hints
                              (booleanp otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (stringp rec-name)
                              (booleanp improve-recsp)
                              (symbolp name-to-induct))
                  :stobjs state :mode :program))
  (if (endp include-book-forms)
      (mv nil nil state)
    (if (and maybe-max-include-book-count
             (<= maybe-max-include-book-count include-book-count))
        (mv nil t state)
      (b* ((include-book-form (first include-book-forms))
           ;; (- (cw "  Trying with ~x0.~%" form))
           ((mv maybe-successful-rec state)
            (try-induct-with-include-book include-book-form theorem-body induct-term name-to-induct current-book-absolute-path avoid-current-bookp theorem-name hints otf-flg step-limit time-limit rec-name improve-recsp state)))
        (if maybe-successful-rec
            (mv maybe-successful-rec nil state)
          (try-induct-with-include-books (rest include-book-forms)
                                         theorem-body
                                         induct-term name-to-induct
                                         (+ 1 include-book-count)
                                         maybe-max-include-book-count current-book-absolute-path avoid-current-bookp theorem-name hints otf-flg step-limit time-limit rec-name improve-recsp state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to prove the theorem after doing the given include-book.
;; Returns (mv erp maybe-successful-rec state).
;; TODO: Skip if library already included
;; TODO: Skip later add-library recs if they are included by this one (though I suppose they might work only without the rest of what we get here).
;; TODO: Try any upcoming enable or use-lemma recs that (may) need this library:
(defun try-add-library (include-book-form current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :stobjs state
                  :guard (and (consp include-book-form)
                              (eq 'include-book (car include-book-form))
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name) ; may be :thm
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit) ; todo: should this also apply to the time to include the library?
                                  (rationalp time-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :mode :program))
  (b* ( ;; TODO: Give up here if the include-book-form corresponds to the current-book-absolute-path.
       ((when (eq 'acl2::other include-book-form)) ; todo: can this happen, or could it be (include-book other)?
        (and (acl2::print-level-at-least-tp print) (cw "skip (can't include catch-all library ~x0)~%" include-book-form))
        (mv nil nil state))
       ((when (not (consp include-book-form)))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ill-formed library recommendation: ~x0)~%" include-book-form))
        (mv nil nil state))
       ((mv & ; ignore errors
            maybe-successful-rec state)
        (revert-world ;; ensures the include-book gets undone
         (b* (        ; Try to include the recommended book:
              ((mv erp state) (acl2::submit-event include-book-form nil nil state))
              ((when erp) ; can happen if there is a name clash
               (cw "NOTE: Event failed (possible name clash): ~x0.~%" include-book-form)
               (mv nil nil state))
              ;; Check that we didn't bring in the current-book:
              ((when (and avoid-current-bookp
                          current-book-absolute-path
                          (member-equal current-book-absolute-path (acl2::all-included-books (w state)))))
               (cw "NOTE: Avoiding include-book, ~x0, that would bring in the current-book.~%" include-book-form)
               (mv nil nil state))
              )
           ;; The include-book is ok, so now try the proof:
           (b* (((mv provedp state) (prove$-no-error 'try-add-library theorem-body theorem-hints theorem-otf-flg step-limit time-limit state)))
             (if provedp
                 ;; We proved it with this include-book:
                 ;; todo: we could even try to see if a smaller library would work
                 (mv nil
                     (if ;; Check whether the include-book brought in the name being defined:
                         ;; todo: do better if redundant!
                         (and (not (eq :thm theorem-name))
                              (not (acl2::new-namep theorem-name (w state))))
                         (b* ((- (cw "NOTE: Working around name clash on ~x0.~%" theorem-name))
                              (defthm-copy-name (intern$ (concatenate 'string (symbol-name theorem-name) "-TEMP-FOR-PROOF-ADVICE") "HELP")))
                           (make-successful-rec (nth 0 rec)
                                                :add-library
                                                include-book-form ; action object for :add-library
                                                ;; pre-commands:
                                                ;; since there is a name clash, we make a copy and prove the copy using the include-book
                                                ;; then we prove the desired theorem using the copy
                                                (list `(encapsulate ()
                                                         (local ,include-book-form)
                                                         (defthm ,defthm-copy-name
                                                           ,theorem-body
                                                           :rule-classes nil ; in case it's not a legal rule
                                                           :hints ,theorem-hints ; we checked above that these hints work
                                                           :otf-flg ,theorem-otf-flg)))
                                                theorem-body
                                                `(("Goal" :by ,defthm-copy-name))
                                                nil ; otf-flg
                                                nil ; symbol-table
                                                ))
                       (make-successful-rec (nth 0 rec)
                                            :add-library
                                            include-book-form ; action object for :add-library
                                            ;; pre-commands:
                                            (list include-book-form)
                                            theorem-body
                                            theorem-hints ; we checked above that these hints work
                                            theorem-otf-flg
                                            nil ; symbol-table
                                            ))
                     state)
               ;; Failed to prove:
               (mv nil nil state)))))))
    (if maybe-successful-rec
        (prog2$ (and (acl2::print-level-at-least-tp print) (cw-success-message maybe-successful-rec))
                (mv nil maybe-successful-rec state))
      (prog2$ (and (acl2::print-level-at-least-tp print) (cw "fail (library didn't help)~%"))
              (mv nil nil state)))))

;; TODO: Handle LET and MV-LET and nested implies and ...
;; TODO: Should we translate this first?
(defun formula-hyp-simple (formula ;; untranslated
                           )
  (if (and (consp formula)
           (eq 'implies (acl2::ffn-symb formula)))
      (second formula)
    *t*))

;; Returns (mv contradictp state).
(defund provably-contradictoryp (ctx formula state)
  (declare (xargs :mode :program
                  :stobjs state))
  (prove$-no-error ctx
                   `(not ,formula)
                   nil ; todo: use the theorem-hints? ;todo: don't induct?
                   nil
                   *step-limit*
                   *time-limit* ; todo: reduce?
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
                   *time-limit* ; todo: reduce?
                   state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Don't try a hyp that is already present, or contradicts ones already present
(defun try-add-hyp (hyp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and (pseudo-termp hyp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hint
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq hyp 'acl2::unknown/untrained)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not adding hyp: ~x0)~%" hyp))
        (mv nil nil state))
       (translatablep (acl2::translatable-termp hyp (w state)))
       ((when (not translatablep))
        (and (acl2::print-level-at-least-tp print) (cw "fail (hyp not translatable: ~x0)~%" hyp)) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       (existing-hyp (formula-hyp-simple theorem-body))
       (existing-hyp-conjunts (acl2::conjuncts-of-uterm existing-hyp))
       ;; TODO: Since hyp is translated, perhaps we should translate existing-hyp-conjunts:
       ((when (member-equal hyp existing-hyp-conjunts))
        (and (acl2::print-level-at-least-tp print) (cw "skip (hyp ~x0 is already present)~%" hyp))
        (mv nil nil state))
       ((mv impliedp state)
        (provably-impliesp 'try-add-hyp existing-hyp hyp state))
       ((when impliedp)
        (and (acl2::print-level-at-least-tp print) (cw "skip (hyp ~x0 is implied by existing hyps)~%" hyp))
        (mv nil nil state))
       ((mv contradictp state)
        (provably-contradictoryp 'try-add-hyp `(and ,hyp ,existing-hyp) state))
       ((when contradictp)
        (and (acl2::print-level-at-least-tp print) (cw "skip (hyp ~x0 would contradict existing hyps)~%" hyp))
        (mv nil nil state))
       (new-theorem-body `(implies ,hyp ,theorem-body)) ; todo: merge hyp in better
       ((mv provedp failure-info state) (prove$-no-error-with-failure-info
                                         'try-add-hyp
                                         new-theorem-body
                                         theorem-hints
                                         theorem-otf-flg
                                         step-limit time-limit
                                         state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-hyp
                                 hyp
                                 nil ; no pre-commands ; todo update this once we use the book map
                                 new-theorem-body
                                 theorem-hints
                                 theorem-otf-flg
                                 (symbol-table-for-term hyp (w state))))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp
                   (cw-success-message rec)
                 (let ((translated-hyp (acl2::translate-term hyp 'try-add-hyp (w state))))
                   (cw-failure-message (fms-to-string-one-line "adding hyp ~x0 didn't help" (acons #\0 translated-hyp nil)) failure-info))))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Avoid theory-invariant violations from enabling.
;; TODO: Support passing in multiple rules, but then we might have to find a book for each one (should be safe if they are all in the goal)?
(defun try-add-enable-hint (rule     ; the rule to try enabling
                            book-map ; info on where the rule may be found
                            current-book-absolute-path
                            avoid-current-bookp
                            theorem-name ; may be :thm
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            step-limit time-limit
                            rec ; todo: just pass in the rec name (here and elsewhere)
                            improve-recsp
                            print
                            state)
  (declare (xargs :guard (and ;; (symbolp rule) ; todo: can be a rune?
                              (book-mapp book-map)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (recommendationp rec)
                              (booleanp improve-recsp)
                              ;; print
                              )
                  :stobjs state :mode :program))
  (b* (((when (eq rule 'acl2::other)) ;; "Other" is a catch-all for low-frequency classes
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not enabling catch-all: ~x0)~%" rule))
        (mv nil nil state))
       ((when (eq rule 'acl2::unknown/untrained)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not enabling: ~x0)~%" rule))
        (mv nil nil state))
       ((when (keywordp rule))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not enabling unsupported item: ~x0)~%" rule)) ; this can come from a ruleset of (:rules-of-class :type-prescription :here)
        (mv nil nil state))
       ((when (not (symbolp rule)))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Unsupported item: ~x0)~%" rule)) ; todo: handle runes like (:TYPE-PRESCRIPTION A14 . 1)
        (mv nil nil state))
       (wrld (w state))
       (rec-name (nth 0 rec))
       (rule-or-macro-alias rule)
       (rule (handle-macro-alias rule wrld)) ; TODO: What about a macro-alias we don't know about?
       )
    (if (function-symbolp rule wrld)
        ;; It's a function in the current world:
        (b* ((fn rule)
             ((when (not (acl2::logicp fn wrld)))
              (and (acl2::print-level-at-least-tp print) (cw "skip (Can't enable ~x0. Not in :logic mode.)~%" fn))
              (mv nil nil state)) ; no error but no successful rec
             ((when (not (acl2::fn-definedp fn wrld)))
              (and (acl2::print-level-at-least-tp print) (cw "skip (Can't enable ~x0. No body.)~%" fn))
              (mv nil nil state)) ; no error but no successful rec
             ;; TODO: Consider whether to enable, say the :type-prescription rule
             (rune `(:definition ,fn))
             ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
             ((when (acl2::enabled-runep rune (acl2::ens-maybe-brr state) (w state)))
              (and (acl2::print-level-at-least-tp print) (cw "skip (~x0 is already enabled.)~%" fn))
              (mv nil nil state))
             ;; FN exists and just needs to be enabled:
             (new-hints (acl2::enable-items-in-hints theorem-hints (list fn) t))
             ((mv provedp failure-info state)
              (prove$-no-error-with-failure-info 'try-add-enable-hint
                                                 theorem-body
                                                 new-hints
                                                 theorem-otf-flg
                                                 step-limit time-limit
                                                 state))
             (failure-snippet (fms-to-string-one-line "enabling function ~x0 didn't help" (acons #\0 fn nil)))
             ((when (not provedp))
              (and (acl2::print-level-at-least-tp print) (cw-failure-message failure-snippet failure-info))
              (mv nil nil state))
             (rec (make-successful-rec rec-name
                                       :add-enable-hint ; in case it was a :use-lemma rec, we force the type to be :add-enable-hint here, to ensure duplicates get removed
                                       rule-or-macro-alias
                                       nil
                                       theorem-body new-hints theorem-otf-flg
                                       (symbol-table-for-event rule current-book-absolute-path wrld)))
             (- (and (acl2::print-level-at-least-tp print)
                     (cw-success-message rec))))
          (mv nil rec state))
      (if (not (eq :no-body (getpropc rule 'acl2::theorem :no-body wrld))) ;todo: how to just check if the property is set?
          ;; It's a theorem in the current world:
          (b* ( ;; TODO: Consider whether to enable, say, the :type-prescription rule
               (rune `(:rewrite ,rule))
               ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
               ((when (acl2::enabled-runep rune (acl2::ens-maybe-brr state) (w state)))
                (and (acl2::print-level-at-least-tp print) (cw "skip (~x0 is already enabled.)~%" rule))
                (mv nil nil state))
               ;; RULE exists and just needs to be enabled:
               (new-hints (acl2::enable-items-in-hints theorem-hints (list rule) nil))
               ((mv provedp state)
                (prove$-no-error 'try-add-enable-hint
                                 theorem-body
                                 new-hints
                                 theorem-otf-flg
                                 step-limit time-limit
                                 state))
               ((when (not provedp))
                (and (acl2::print-level-at-least-tp print) (cw "fail (enabling rule ~x0 didn't help)~%" rule))
                (mv nil nil state))
               ;; We change the rec type to ensure duplicates get removed:
               (rec (make-successful-rec rec-name
                                         :add-enable-hint
                                         rule-or-macro-alias
                                         nil
                                         theorem-body new-hints theorem-otf-flg (symbol-table-for-event rule current-book-absolute-path wrld)))
               (- (and (acl2::print-level-at-least-tp print)
                       (cw-success-message rec))))
            (mv nil rec state))
        ;; RULE is not currently known, so try to find where it is defined:
        (b* ((book-map-keys (strip-cars book-map))
             ((when (not (equal book-map-keys (list rule)))) ; todo: relax this?
              (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil rule)
              (mv :bad-book-map nil state))
             (include-book-info (acl2::lookup-eq rule book-map))
             ((when (eq :builtin include-book-info))
              (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" rule)
              (mv :bad-book-info nil state))
             ;; todo: check for empty books-to-try (here and elsewhere?)
             (include-books-to-try include-book-info) ; renames for clarity
             ((when (null include-books-to-try))
              (and (acl2::print-level-at-least-tp print) (cw "fail (no books given to find ~x0 for enabling)~%" rule))
              (mv nil nil state))
             (- (if (acl2::print-level-at-least-verbosep print)
                    (cw "(~x0 books given to find ~x1 for enabling: ~X23)~%" (len include-books-to-try) rule include-books-to-try nil)
                  (if (acl2::print-level-at-least-tp print)
                      (cw "(~x0 books given to find ~x1 for enabling)~%" (len include-books-to-try) rule)
                    nil)))
             (max-books-to-try 3)
             ;; TODO: Would be nice to not bother if it is a definition that we don't have, but how to tell without including the book?
             ;; TODO: If, after including the book, the name to enable is a function, enabling it seems unlikely to help given that it didn't appear in the original proof.
             ;; TODO: Try to get a good variety of books here, if there are too many to try them all:
             ;; todo: try more if we didn't find it?
             ((mv maybe-successful-rec book-limit-reachedp state)
              (try-enable-with-include-books include-books-to-try
                                             theorem-body
                                             rule
                                             0 ; include-book-count
                                             max-books-to-try
                                             current-book-absolute-path
                                             avoid-current-bookp
                                             theorem-name
                                             theorem-hints ; will be augmented with an enable of the item-to-enable
                                             theorem-otf-flg
                                             step-limit time-limit
                                             rec-name
                                             improve-recsp
                                             state)))
          (if maybe-successful-rec
              (prog2$ (and (acl2::print-level-at-least-tp print)
                           (cw-success-message maybe-successful-rec))
                      (mv nil maybe-successful-rec state))
            ;; failed:
            (if book-limit-reachedp
                (prog2$ (and (acl2::print-level-at-least-tp print)
                             ;; todo: clarify whether we even found an include-book that works:
                             (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" max-books-to-try (len include-books-to-try) rule))
                        (mv nil nil state))
              (prog2$ (and (acl2::print-level-at-least-tp print) (cw "fail (enabling ~x0 didn't help)~%" rule))
                      (mv nil nil state)))))))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-disable-hint (rule current-book-absolute-path theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and (symbolp rule) ; todo: never a rune?
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :stobjs state
                  :mode :program))
  (b* (((when (eq rule 'acl2::other)) ;; "Other" is a catch-all for low-frequency classes
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling catch-all: ~x0)~%" rule))
        (mv nil nil state))
       ((when (eq rule 'acl2::unknown/untrained)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling: ~x0)~%" rule))
        (mv nil nil state))
       ((when (keywordp rule))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling unsupported item: ~x0)~%" rule)) ; this can come from a ruleset of (:rules-of-class :type-prescription :here)
        (mv nil nil state))
       ((when (not (item-that-can-be-enabled/disabledp rule (w state))))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling unknown name: ~x0)~%" rule)) ;; For now, we don't try to including the book that brings in the thing to disable!
        (mv nil nil state))
       (rule (handle-macro-alias rule (w state))) ; TODO: Handle the case of a macro-alias we don't know about
       ((when (acl2::disabledp-fn rule (acl2::ens-maybe-brr state) (w state)))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling since already disabled: ~x0)~%" rule))
        (mv nil nil state))
       ;; todo: ensure this is nice:
       (new-hints (acl2::disable-items-in-hints theorem-hints (list rule) t)) ; t means use disable*
       ((mv provedp state) (prove$-no-error 'try-add-disable-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit time-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-disable-hint
                                 rule
                                 nil
                                 theorem-body new-hints theorem-otf-flg
                                 (symbol-table-for-event rule current-book-absolute-path (w state))))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (disable didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Do we need to guess a substitution for the :use hint?  Then change the rec before returning...
;; TTODO: Handle the case where the included book has a name clash with the desired-name (see what we do for add-enable-hint)
(defun try-add-use-hint (item ; a lemma-instance
                         book-map
                         current-book-absolute-path avoid-current-bookp
                         theorem-name theorem-body theorem-hints theorem-otf-flg
                         step-limit time-limit rec improve-recsp print state)
  (declare (xargs :guard (and (book-mapp book-map)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (recommendationp rec)
                              (booleanp improve-recsp)
                              ;; print
                              )
                  :stobjs state
                  :mode :program))
  (b* (;; Handle some weird cases:
       ((when (eq item 'acl2::other))
        (and (acl2::print-level-at-least-tp print) (cw "skip (skipping catch-all: ~x0)~%" item))
        (mv nil nil state))
       ((when (eq item 'acl2::unknown/untrained)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not :use-ing ~x0)~%" item))
        (mv nil nil state))
       ;; Extract the name (symbol) of the lemma-instance:
       ((mv erp name-to-use) (name-from-lemma-instance item))
       ((when erp)
        (cw "error (Unhandled lemma instance: ~x0)~%" item)
        (mv erp nil state))
       (rec-name (nth 0 rec)))
    (if (symbol-that-can-be-usedp name-to-use (w state)) ; todo: what if it's defined but can't be :used?
        (b* (                                     ;; todo: ensure this is nice:
             ;; todo: also disable the name-to-use, if appropriate
             (new-hints (acl2::merge-hint-setting-into-goal-hint :use item theorem-hints))
             ((mv provedp state) (prove$-no-error 'try-add-use-hint
                                                  theorem-body
                                                  new-hints
                                                  theorem-otf-flg
                                                  step-limit time-limit
                                                  state))
             (rec (make-successful-rec rec-name
                                       :add-use-hint
                                       item
                                       nil
                                       theorem-body new-hints theorem-otf-flg
                                       (symbol-table-for-event name-to-use current-book-absolute-path (w state))))
             (- (and (acl2::print-level-at-least-tp print)
                     (if provedp (cw-success-message rec) (cw "fail (:use ~x0 didn't help)~%" item)))))
          (mv nil (if provedp rec nil) state))
      ;; NAME-TO-USE is not in the current world, so try to find where it is defined:
      (b* ((book-map-keys (strip-cars book-map))
           ((when (not (member-equal name-to-use book-map-keys)))
            (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil name-to-use)
            (mv :bad-book-map nil state))
           (include-book-info (acl2::lookup-eq name-to-use book-map))
           ((when (eq :builtin include-book-info))
            (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" name-to-use)
            (mv :bad-book-info nil state))
           ;; TODO: Filter out include-books that are known to clash with this tool?
           (include-books-to-try include-book-info) ; renames for clarity
           (max-books-to-try 3)
             ;; TODO: Would be nice to not bother if it is a definition that we don't have, but how to tell without including the book?
             ;; TODO: If, after including the book, the name to :use is a function, :use-ing it seems unlikely to help given that it didn't appear in the original proof.
             ;; TODO: Try to get a good variety of books here, if there are too many to try them all:
           ((mv maybe-successful-rec limit-reachedp state)
            ;; TODO: We should also ensure that all names in the subst are defined when we try include-books:
            (try-use-with-include-books (if (< max-books-to-try (len include-books-to-try)) (take max-books-to-try include-books-to-try) include-books-to-try) ;; todo: try more if we didn't find it?
                                           theorem-body
                                           item
                                           name-to-use
                                           0 ; include-book-count
                                           max-books-to-try
                                           current-book-absolute-path
                                           avoid-current-bookp
                                           theorem-name
                                           theorem-hints ; will be augmented with a :use of item
                                           theorem-otf-flg
                                           step-limit time-limit
                                           rec-name
                                           improve-recsp
                                           state)))
        (if maybe-successful-rec
            (prog2$ (and (acl2::print-level-at-least-tp print)
                         (cw-success-message maybe-successful-rec))
                    (mv nil maybe-successful-rec state))
          ;; failed:
          (if limit-reachedp
              (prog2$ (and (acl2::print-level-at-least-tp print)
                           ;; todo: clarify whether we even found an include-book that works:
                           (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" max-books-to-try (len include-books-to-try) name-to-use))
                      (mv nil nil state))
            (prog2$ (and (acl2::print-level-at-least-tp print)
                         (cw "fail (:use ~x0 didn't help)~%" item))
                    (mv nil nil state))))))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-expand-hint (item ; the thing to expand
                            theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (or (null time-limit)
                              (rationalp time-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'acl2::other item))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring recommendation to expand \"Other\")~%"))
        (mv nil nil state))
       ((when (eq 'acl2::unknown/untrained item)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not :expand-ing ~x0)~%" item))
        (mv nil nil state))
       ((when (symbolp item)) ; todo: eventually remove this case
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring illegal recommendation to expand a symbol)~%"))
        (mv nil nil state))
       ;; todo: can it be a single term?:
       ;; todo: can it be :lambdas?
       ((when (not (acl2::translatable-term-listp item (w state))))
        (and (acl2::print-level-at-least-tp print) (cw "fail (terms not all translatable: ~x0)~%" item)) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; todo: ensure this is nice:
       (new-hints (acl2::merge-hint-setting-into-goal-hint :expand item theorem-hints))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (acl2::submit-event
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (acl2::merge-hint-setting-into-goal-hint :expand item theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-no-error 'try-add-expand-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit time-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-expand-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg :unavailable))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:expand hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-by-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (or (null time-limit)
                              (rationalp time-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'acl2::other item))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring :by hint with catch-all \"Other\")~%"))
        (mv nil nil state))
       ((when (eq 'acl2::unknown/untrained item)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring :by hint with ~x0)~%" item))
        (mv nil nil state))
       ((when (not (symbolp item)))
        (and (acl2::print-level-at-least-tp print) (cw "fail (unexpected :by hint: ~x0)~%" item))
        (mv nil nil state))
       ((when (not (or (getpropc item 'acl2::unnormalized-body nil (w state))
                       (getpropc item 'acl2::theorem nil (w state)))))
        (and (acl2::print-level-at-least-tp print) (cw "skip (unknown name for :by hint: ~x0)~%" item))
        (mv nil nil state))
       ;; TTODO: Include any necessary books first
       ;; todo: ensure this is nice:
       ;; todo: remove existing hints?
       (new-hints (acl2::merge-hint-setting-into-goal-hint :by item theorem-hints))
       ((mv provedp failure-info state)
        (prove$-no-error-with-failure-info 'try-add-by-hint
                                           theorem-body
                                           new-hints
                                           theorem-otf-flg
                                           step-limit time-limit
                                           state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-by-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg :unavailable))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw-failure-message ":by hint didn't help" failure-info)))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-cases-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (or (null time-limit)
                              (rationalp time-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'acl2::unknown/untrained item))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring :cases hint with ~x0)~%" item))
        (mv nil nil state))
       ((when (not (true-listp item)))
        (and (acl2::print-level-at-least-tp print) (cw "fail (:cases not a true list: ~x0)~%" item))
        (mv nil nil state))
       ((when (not (acl2::translatable-term-listp item (w state))))
        (and (acl2::print-level-at-least-tp print) (cw "fail (:cases not all translatable: ~x0)~%" item)) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; todo: ensure this is nice:
       (new-hints (acl2::merge-hint-setting-into-goal-hint :cases item theorem-hints))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (acl2::submit-event
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (acl2::merge-hint-setting-into-goal-hint  :cases item
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-no-error 'try-add-cases-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit time-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-cases-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg :unavailable))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:cases hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-nonlinearp-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (or (null time-limit)
                              (rationalp time-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq item 'acl2::unknown/untrained)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not adding :nonlinearp hint of ~x0)~%" item))
        (mv nil nil state))
       ((when (not (booleanp item)))
        (and print (cw "WARNING: Invalid value for :nonlinearp: ~x0.~%" item))
        (mv nil nil state) ; or we could return erp=t here
        )
       ;; todo: ensure this is nice:
       (new-hints (acl2::merge-hint-setting-into-goal-hint :nonlinearp item theorem-hints))
       ((mv provedp state) (prove$-no-error 'try-add-nonlinearp-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit time-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-nonlinearp-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg nil))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:nonlinearp hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-do-not-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (or (null time-limit)
                              (rationalp time-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'acl2::unknown/untrained item)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring :do-not hint with ~x0)~%" item))
        (mv nil nil state))
       ;; Can't easily check the :do-not hint syntactically...
       ;; todo: ensure this is nice:
       (new-hints (acl2::merge-hint-setting-into-goal-hint :do-not item theorem-hints))
       ((mv provedp state) (prove$-no-error 'try-add-do-not-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit time-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-do-not-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg nil))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:do-not hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: We need more than a symbol
;; TODO: Consider :induction rules that are defthms.
(defun try-add-induct-hint (item
                            book-map ; info on where the rule may be found
                            current-book-absolute-path avoid-current-bookp
                            theorem-name theorem-body theorem-hints theorem-otf-flg
                            step-limit time-limit rec improve-recsp print state)
  (declare (xargs :guard (and ;; item can be a term, or maybe just a symbol?
                          (book-mapp book-map)
                          (or (null current-book-absolute-path)
                              (stringp current-book-absolute-path))
                          (booleanp avoid-current-bookp)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (or (null time-limit)
                              (rationalp time-limit))
                          (recommendationp rec)
                          (booleanp improve-recsp)
                          ;; print
                          )
                  :stobjs state :mode :program))
  (b* (((when (eq 'acl2::unknown/untrained item)) ;; A leidos model can return this
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring :induct hint with ~x0)~%" item))
        (mv nil nil state))
       (rec-name (nth 0 rec))
       (wrld (w state))
       ((when (and (symbolp item)
                   (not (member-eq item '(t nil))))) ; todo: :induct nil currently always fails?
        ;; We've been given just a symbol, not a whole term, and it's not T or NIL.
        ;; TODO: Try looking for calls of the given symbol in the theorem (or checkpoints?), maybe just ones where the actuals for the measured-subset are vars?:
        (prog2$ (and (acl2::print-level-at-least-tp print) (cw "skip (need arguments of ~x0 to create :induct hint)~%" item))
                (mv nil nil state)))
       ;; Decide whether the ITEM is ok.  If so, get the function symbol and check whether it is known in the world:
       ((mv okp name-to-induct knownp)
        (if (symbolp item) ; must be t or nil (see check above)
            (mv t nil t)
          ;; ITEM must be a term:
          (let ((induct-term item))
            (if (not (and (consp induct-term)
                          (symbolp (acl2::ffn-symb induct-term))))
                (mv nil nil nil)
              ;; structure is ok, but is it a known function?
              (let ((name-to-induct (acl2::ffn-symb induct-term)))
                (if (acl2::defined-functionp name-to-induct wrld)
                    (if (acl2::recursivep name-to-induct nil wrld)
                        (if (let ((controlling-actuals (filter-actuals-for-formals (acl2::fn-formals name-to-induct wrld) (acl2::fargs induct-term) (acl2::measured-subset+ name-to-induct wrld))))
                              (and (symbol-listp controlling-actuals) ; controlling actuals must be distinct vars (see :doc induction)
                                   (no-duplicatesp-eq controlling-actuals)))
                            (mv t name-to-induct t)
                          (mv nil nil nil))
                      (mv nil nil nil))
                  ;; ok but not known:
                  (mv t name-to-induct nil)))))))
       ((when (not okp))
        (and (acl2::print-level-at-least-tp print) (cw "skip (:induct hint, ~x0, is not a suitable :induct hint)~%" item))
        (mv nil nil state)))
    (if knownp
        ;; Don't need to include any books:
        (b* ((new-hints (acl2::merge-hint-setting-into-goal-hint :induct item theorem-hints))
             ;; We go ahead and enable the :induction rune explicitly:
             (new-hints (if name-to-induct ; will be nil for :induct t or :induct nil
                            (acl2::enable-items-in-hints new-hints (list name-to-induct) ; :induction rule and definition
                                                         ;; (list `(:i ,name-to-induct))
                                                         t)
                          new-hints))
             ((mv provedp state) (prove$-no-error 'try-add-induct-hint theorem-body new-hints theorem-otf-flg step-limit time-limit state))
             (rec (make-successful-rec rec-name
                                       :add-induct-hint
                                       item
                                       nil
                                       theorem-body new-hints theorem-otf-flg
                                       (symbol-table-for-event name-to-induct current-book-absolute-path wrld)))
             (- (and (acl2::print-level-at-least-tp print)
                     (if provedp (cw-success-message rec) (cw "fail (:induct ~x0 didn't help)~%" item)))))
          (mv nil (if provedp rec nil) state))
      ;; NAME-TO-INDUCT is not in the current world, so try to find where it is defined:
      ;; TODO: Go look for books that may define other things in the term (should there usually be just one function?).
      (b* ((book-map-keys (strip-cars book-map))
           ((when (not (member-equal name-to-induct book-map-keys)))
            (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil name-to-induct)
            (mv :bad-book-map nil state))
           (include-book-info (acl2::lookup-eq name-to-induct book-map))
           ((when (eq :builtin include-book-info))
            (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" name-to-induct)
            (mv :bad-book-info nil state))
           ;; TODO: Filter out include-books that are known to clash with this tool?
           (include-books-to-try include-book-info) ; renames for clarity
           (max-books-to-try 3)
           ;; TODO: Try to get a good variety of books here, if there are too many to try them all:
           ((mv maybe-successful-rec limit-reachedp state)
            ;; TODO: We should also ensure that all names in the item are defined when we try include-books:
            (try-induct-with-include-books include-books-to-try
                                           theorem-body
                                           item
                                           name-to-induct
                                           0 ; include-book-count
                                           max-books-to-try
                                           current-book-absolute-path
                                           avoid-current-bookp
                                           theorem-name
                                           theorem-hints ; will be augmented with a :induct of item
                                           theorem-otf-flg
                                           step-limit time-limit
                                           rec-name
                                           improve-recsp
                                           state)))
        (if maybe-successful-rec
            (prog2$ (and (acl2::print-level-at-least-tp print)
                         (cw-success-message maybe-successful-rec))
                    (mv nil maybe-successful-rec state))
          ;; failed:
          (if limit-reachedp
              (prog2$ (and (acl2::print-level-at-least-tp print)
                           ;; todo: clarify whether we even found an include-book that works:
                           (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" max-books-to-try (len include-books-to-try) name-to-induct))
                      (mv nil nil state))
            (prog2$ (and (acl2::print-level-at-least-tp print)
                         (cw "fail (:induct ~x0 didn't help)~%" item))
                    (mv nil nil state))))))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-exact-hints (hints theorem-body theorem-otf-flg step-limit time-limit rec print state)
  (declare (xargs :guard (and (true-listp hints)
                              ;; theorem-body is an untranslated term
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :stobjs state :mode :program))
  (b* (((mv provedp failure-info state)
        (prove$-no-error-with-failure-info 'try-exact-hints
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           hints
                                           theorem-otf-flg
                                           step-limit time-limit
                                           state))
       (rec (make-successful-rec (nth 0 rec)
                                 :exact-hints
                                 hints
                                 nil
                                 theorem-body hints theorem-otf-flg :unavailable))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw-failure-message ":hints didn't help" failure-info)))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Pass in previous successful add-libraries and avoid anything else that brings in those libraries?
(defun try-recommendation (rec
                           current-book-absolute-path
                           avoid-current-bookp
                           theorem-name ; may be :thm
                           theorem-body
                           theorem-hints
                           theorem-otf-flg
                           step-limit time-limit
                           improve-recsp
                           print
                           state)
  (declare (xargs :guard (and (recommendationp rec)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (booleanp improve-recsp)
                              (acl2::print-levelp print))
                  :mode :program
                  :stobjs state))
  (b* ((name (nth 0 rec))
       (type (nth 1 rec))
       (object (nth 2 rec))
       ;; (confidence-percent (nth 3 rec))
       (book-map (nth 4 rec))
       (- (and (acl2::print-level-at-least-tp print) (cw "~s0: " name)))
       ((mv & ; erp ; for now, we ignore errors and just continue
            maybe-successful-rec ; may be fleshed out (pre-commands, hints, etc.)
            state)
        (case type
          ;; TODO: Pass the book-map and the current-book-absolute-path to all who can use it:
          (:add-by-hint (try-add-by-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-cases-hint (try-add-cases-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-disable-hint (try-add-disable-hint object current-book-absolute-path theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-do-not-hint (try-add-do-not-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-enable-hint (try-add-enable-hint object book-map current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec improve-recsp print state))
          (:add-expand-hint (try-add-expand-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-hyp (try-add-hyp object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-induct-hint (try-add-induct-hint object book-map current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec improve-recsp print state))
          (:add-library (try-add-library object current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-nonlinearp-hint (try-add-nonlinearp-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec print state))
          (:add-use-hint (try-add-use-hint object book-map current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec improve-recsp print state))
          ;; same as for try-add-enable-hint above:
          (:use-lemma (try-add-enable-hint object book-map current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit rec improve-recsp print state))
          ;; Hints not from ML:
          (:exact-hints (try-exact-hints object theorem-body theorem-otf-flg step-limit time-limit rec print state))
          (t (prog2$ (cw "WARNING: UNHANDLED rec type ~x0.~%" type)
                     (mv t nil state))))))
    (mv nil ; never an error (for now)
        maybe-successful-rec
        state)))

;; Tries to find rec(s) which, together with the supplied THEOREM-HINTS, suffices to prove the theorem.
;; Tries each of the RECS in turn until MAX-WINS successful ones are found or there are none left.
;; Returns (mv erp successful-recs extra-recs-ignoredp state)
;; TODO: Move down.
(defun try-recommendations (recs
                            current-book-absolute-path
                            avoid-current-bookp
                            theorem-name ; may be :thm
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            step-limit time-limit
                            max-wins
                            improve-recsp
                            print
                            successful-recs ; an accumulator
                            state)
  (declare (xargs :guard (and (recommendation-listp recs)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or (null max-wins)
                                  (natp max-wins))
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (true-listp successful-recs))
                  :mode :program
                  :stobjs state))
  (if (endp recs)
      (mv nil (reverse successful-recs) nil state)
    (if (and max-wins
             (<= max-wins (len successful-recs)))
        (mv nil (reverse successful-recs) t state)
      (b* ((rec (first recs))
           ((mv & ; erp ; for now, we ignore errors and just continue
                maybe-successful-rec ; may be fleshed out (pre-commands, hints, etc.)
                state)
            (try-recommendation rec current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit improve-recsp print state)))
        (try-recommendations (rest recs)
                             current-book-absolute-path avoid-current-bookp
                             theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit max-wins improve-recsp print
                             (if maybe-successful-rec
                                 (cons maybe-successful-rec successful-recs)
                               successful-recs)
                             state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; from Matt K:
(defun clausify-term (term wrld)
  (declare (xargs :mode :program))
  (let* ((term (acl2::expand-some-non-rec-fns '(implies) term wrld))
         (term (remove-guard-holders term wrld)))
    (acl2::clausify term nil t (acl2::sr-limit wrld))))

;; compares most of the fields
(defund equivalent-successful-recommendationsp (rec1 rec2)
  (declare (xargs :guard (and (successful-recommendationp rec1)
                              (successful-recommendationp rec2))
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (and (equal (nth 1 rec1) (nth 1 rec2)) ; same type
       (equal (nth 2 rec1) (nth 2 rec2)) ; same object
       (equal (nth 3 rec1) (nth 3 rec2)) ; same pre-commands
       (equal (nth 4 rec1) (nth 4 rec2)) ; same theorem-body
       (equal (nth 5 rec1) (nth 5 rec2)) ; same theorem-hints
       (equal (nth 6 rec1) (nth 6 rec2)) ; same theorem-otf-flg
       (equal (nth 7 rec1) (nth 7 rec2)) ; same symbol-table
       ))

;; Returns a member of RECS that is equivalent to REC, or nil.
(defund find-equivalent-successful-rec (rec recs)
  (declare (xargs :guard (and (successful-recommendationp rec)
                              (successful-recommendation-listp recs))
                  :guard-hints (("Goal" :in-theory (enable successful-recommendation-listp)))))
  (if (endp recs)
      nil
    (let ((this-rec (first recs)))
      (if (equivalent-successful-recommendationsp rec this-rec)
          this-rec
        (find-equivalent-successful-rec rec (rest recs))))))

(defthm recommendationp-of-find-equivalent-successful-rec
  (implies (and (find-equivalent-successful-rec rec recs)
                (recommendation-listp recs))
           (recommendationp (find-equivalent-successful-rec rec recs)))
  :hints (("Goal" :in-theory (enable find-equivalent-successful-rec recommendation-listp))))

;; Can this be slow?
(defun merge-successful-rec-into-recs (rec recs)
  (declare (xargs :guard (and (successful-recommendationp rec)
                              (successful-recommendation-listp recs))
                  :verify-guards nil ; todo
                  ))
  (let ((match (find-equivalent-successful-rec rec recs)))
    (if match
        (cons (make-successful-rec (concatenate 'string (nth 0 rec) "/" (nth 0 match)) ; combine the names
                                   (nth 1 rec) ; type is same in both
                                   (nth 2 rec) ; object is same in both
                                   (nth 3 rec) ; pre-commands are same in both
                                   (nth 4 rec) ; theorem-body is same in both
                                   (nth 5 rec) ; theorem-hints are same in both
                                   (nth 6 rec) ; theorem-otf-flg is same in both
                                   (nth 7 rec) ; symbol-table is same in both
                                   )
              (remove-equal match recs))
      (cons rec recs))))

;; This effectively reverses the first arg.
(defun merge-successful-recs-into-recs (recs1 recs2)
  (declare (xargs :guard (and (successful-recommendation-listp recs1)
                              (successful-recommendation-listp recs2))
                  :verify-guards nil ; todo
                  :guard-hints (("Goal" :in-theory (enable successful-recommendation-listp)))))
  (if (endp recs1)
      recs2
    (merge-successful-recs-into-recs (rest recs1) (merge-successful-rec-into-recs (first recs1) recs2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sends an HTTP POST request containing the POST-DATA to the server at
;; SERVER-URL.  Parses the response as JSON.
;; Returns (mv erp parsed-json-response state).
(defund post-and-parse-response-as-json (server-url timeout post-data debug state)
  (declare (xargs :guard (and (stringp server-url)
                              (natp timeout)
                              (acl2::string-string-alistp post-data)
                              (booleanp debug))
                  :stobjs state))
  (b* ((- (and debug (cw "POST data to be sent: ~X01.~%" post-data nil)))
       ((mv erp post-response state)
        (htclient::post-light server-url post-data state `((:connect-timeout ,timeout)
                                                           (:read-timeout ,timeout))))
       ((when erp)
        (cw "~%Error received from HTTP POST:~%~@0.~%" erp)
        (mv erp nil state))
       (- (and debug (cw "Raw POST response: ~X01~%" post-response nil)))
       ;; Parse the JSON:
       ((mv erp parsed-json-response) (acl2::parse-string-as-json post-response))
       ((when erp)
        (cw "Error parsing JSON response from ~x0: ~s1~%" server-url post-response)
        (mv erp nil state))
       (- (and debug (cw "Parsed POST response: ~X01~%" parsed-json-response nil))))
    (mv nil parsed-json-response state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a member of RECS that is equivalent to REC, or nil.
(defund find-equivalent-rec (rec recs)
  (declare (xargs :guard (and (recommendationp rec)
                              (recommendation-listp recs))
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp recs)
      nil
    (let ((this-rec (first recs)))
      (if (equivalent-recommendationsp rec this-rec)
          this-rec
        (find-equivalent-rec rec (rest recs))))))

(defthm recommendationp-of-find-equivalent-rec
  (implies (and (find-equivalent-rec rec recs)
                (recommendation-listp recs))
           (recommendationp (find-equivalent-rec rec recs)))
  :hints (("Goal" :in-theory (enable find-equivalent-rec recommendation-listp))))

;; Can this be slow?
(defun merge-rec-into-recs (rec recs)
  (declare (xargs :guard (and (recommendationp rec)
                              (recommendation-listp recs))))
  (let ((match (find-equivalent-rec rec recs)))
    (if match
        (cons (make-rec (concatenate 'string (nth 0 rec) "/" (nth 0 match)) ; combine the names
                        (nth 1 rec) ; same in both
                        (nth 2 rec) ; same in both
                        (max (nth 3 rec) (nth 3 match)) ; take max confidence (todo: do better?)
                        (combine-book-maps (nth 4 rec) (nth 4 match)))
              (remove-equal match recs))
      (cons rec recs))))

(defthm recommendation-listp-of-merge-rec-into-recs
 (implies (and (recommendationp recs)
               (recommendation-listp recs))
          (recommendation-listp (merge-rec-into-recs recs recs)))
 :hints (("Goal" :in-theory (enable merge-rec-into-recs recommendation-listp))))

;; This effectively reverses the first arg.
(defun merge-recs-into-recs (recs1 recs2)
  (declare (xargs :guard (and (recommendation-listp recs1)
                              (recommendation-listp recs2))
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp recs1)
      recs2
    (merge-recs-into-recs (rest recs1) (merge-rec-into-recs (first recs1) recs2))))

(defthm recommendation-listp-of-merge-recs-into-recs
 (implies (and (recommendation-listp recs1)
               (recommendation-listp recs2))
          (recommendation-listp (merge-recs-into-recs recs1 recs2)))
 :hints (("Goal" :in-theory (enable merge-recs-into-recs recommendation-listp))))

(defun recommendation-list-listp (rec-lists)
  (declare (xargs :guard t))
  (if (atom rec-lists)
      (null rec-lists)
    (and (recommendation-listp (first rec-lists))
         (recommendation-list-listp (rest rec-lists)))))

(defund merge-rec-lists-into-recs (rec-lists recs)
  (declare (xargs :guard (and (recommendation-list-listp rec-lists)
                              (recommendation-listp recs))
                  :verify-guards nil ; done below
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp rec-lists)
      recs
    (merge-rec-lists-into-recs (reverse (rest rec-lists)) ; preserve the order
                               (merge-recs-into-recs (reverse (first rec-lists)) recs))))

(defthm recommendation-list-listp-of-revappend
  (implies (and (recommendation-list-listp rec-lists1)
                (recommendation-list-listp rec-lists2))
           (recommendation-list-listp (revappend rec-lists1 rec-lists2)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm recommendation-list-listp-of-reverse
  (implies (recommendation-list-listp rec-lists)
           (recommendation-list-listp (reverse rec-lists)))
  :hints (("Goal" :in-theory (enable reverse))))

(defthm recommendation-listp-of-merge-recs-lists-into-recs
  (implies (and (recommendation-list-listp rec-lists)
                (recommendation-listp recs))
           (recommendation-listp (merge-rec-lists-into-recs rec-lists recs)))
  :hints (("Goal" :in-theory (enable merge-rec-lists-into-recs))))

(verify-guards merge-rec-lists-into-recs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-disallowed-recs (recs disallowed-rec-types acc)
  (declare (xargs :guard (and (recommendation-listp recs)
                              (rec-type-listp disallowed-rec-types)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp recs)
      (reverse acc)
    (let* ((rec (first recs))
           (type (nth 1 rec)))
      (if (member-eq type disallowed-rec-types)
          ;; Drop the rec:
          (remove-disallowed-recs (rest recs) disallowed-rec-types acc)
        ;; Keep the rec:
        (remove-disallowed-recs (rest recs) disallowed-rec-types (cons rec acc))))))

;; (defund remove-disallowed-rec-types-from-alist (rec-alist disallowed-rec-types print)
;;   (declare (xargs :guard (and (alistp rec-alist)
;;                               (recommendation-list-listp rec-lists)
;;                               (rec-type-listp disallowed-rec-types)
;;                               (acl2::print-levelp print))
;;                   :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
;;   (if (endp rec-lists)
;;       nil
;;     (b* ((rec-list (first rec-lists))
;;          (rec-count-before-removal (len rec-list))
;;          (rec-list (remove-disallowed-recs rec-list disallowed-rec-types nil))
;;          (rec-count-after-removal (len rec-list))
;;          (- (and (< rec-count-after-removal rec-count-before-removal) ; todo: this doesn't catch disallowed enable or history recs suppressed elsewhere
;;                  (acl2::print-level-at-least-tp print)
;;                  ;; todo: pass in and print the source of the recs here:
;;                  (cw "NOTE: Removed ~x0 recommendations of disallowed types.~%" (- rec-count-before-removal rec-count-after-removal)))))
;;       (cons rec-list
;;             (remove-disallowed-rec-types-from-alist (rest rec-alist) disallowed-rec-types print)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The information about a model, either :function, meaning it's an ACL2
;; function, or a list containing a server URL and the name by which the server
;; knows the model.  Also allowed is nil, meaning the model is disabled.
(defund model-infop (info)
  (declare (xargs :guard t))
  (or (and (true-listp info)
           (= 2 (len info))
           (stringp (first info))  ; server URL
           (stringp (second info)) ; name of the model, on that server
           )
      (eq info :function) ; model is just function, no server needed
      (null info)         ; model is disabled
      ))

;; Recgonizes an alist that binds each model-name to one of:
;; 1. a doublet containing a server URL and the name the server uses for the model, both strings
;; 2. the symbol :function, meaning the model is just an ACL2 function to call
;; 3. nil, meaning the model is disabled.
(defun model-info-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (model-namep (car entry))
           (model-infop (cdr entry))
           (model-info-alistp (rest alist))))))

;; Returns (mv erp recs state).  If phase is :all, we expect no recs back.
(defun get-recs-from-ml-model (model
                               num-recs
                               disallowed-rec-types
                               checkpoint-clauses-top
                               ;; checkpoint-clauses-non-top ; todo: use these too
                               broken-theorem
                               model-info ; the URL, etc.
                               timeout debug print
                               ;; :start means we start the model but don't wait for the answer (will ask again later)
                               ;; :retrieve means we previously started the model and now want the answer
                               ;; :all means we are not using the start-and-return optimization
                               phase
                               state)
  (declare (xargs :guard (and (model-namep model)
                              (natp num-recs)
                              (rec-type-listp disallowed-rec-types)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              ;; (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              ;; broken-theorem is a thm or defthm form
                              (model-infop model-info)
                              (natp timeout)
                              (booleanp debug)
                              (acl2::print-levelp print)
                              (member-eq phase '(:start :retrieve :all)))
                  :mode :program ; because of make-numbered-checkpoint-entries
                  :stobjs state))
  (b* (((when (not model-info))
        (er hard? 'get-recs-from-ml-model "No info for model ~x0." model)
        (mv :missing-model-info nil state))
       ((when (eq :function model-info))
        (er hard? 'get-recs-from-ml-model "Unexpected model info for ~x0." model)
        (mv :unexpected-model-info nil state))
       (server-url (first model-info))
       (model-string (second model-info))
       ((when (not (stringp server-url)))
        (er hard? 'advice-fn "Server URL is not a string: ~x0." server-url)
        (mv :no-server nil state))
       ((when (not (stringp model-string)))
        (er hard? 'advice-fn "Model name for server is not a string: ~x0." model-string)
        (mv :no-server nil state))
       (- (and print (cw "Server for ~x0 is ~s1.~%" model server-url)))
       ;; Send query to server:
       ((mv erp semi-parsed-response state) ;; semi-parsed means the JSON has been parsed
        (if (zp num-recs) ;handle this higher up?
            (prog2$ (cw "Not asking server for recommendations since num-recs=0.")
                    (mv nil
                        nil ; no server response
                        state))
          (b* ((- (and (acl2::print-level-at-least-tp print)
                       (cw "Asking server for ~x0 recommendations from ~x1 on ~x2 ~s3: " ; the line is ended below when we print the time
                           num-recs
                           model
                           (len checkpoint-clauses-top)
                           (if (< 1 (len checkpoint-clauses-top)) "checkpoints" "checkpoint"))))
               ;; Assemble the data to send with the POST request (an alist):
               (post-data (acons "use-group" model-string ; the name of the model to use (often a group of models, one for each action type)
                                 (acons "n" (acl2::nat-to-string num-recs)
                                        (acons "broken-theorem" (fms-to-string "~X01" (acons #\0 broken-theorem (acons #\1 nil nil))) ;; todo: should we translate this?
                                               (make-numbered-checkpoint-entries 0 checkpoint-clauses-top)))))
               ;; Turn off certain recommendation types (TODO: Could a generative model return something like :exact-hints?):
               (post-data (acons-all-to-val (rec-types-to-strings (remove-eq :exact-hints disallowed-rec-types)) ; todo: drop this?  can the models handle disallowed unknown rec types?
                                            "off"
                                            post-data))
               (post-data (if (eq :start phase)
                              (acons "start-and-return" "true" post-data) ; starts the model working, must call it later on the same args to get the answer
                            (if (eq :retrieve phase)
                                (acons "retrieve-started" "true" post-data)
                              post-data)))
               ;; Send POST request to server and parse the response:
               ((mv erp semi-parsed-response state)
                (post-and-parse-response-as-json server-url timeout post-data debug state))
               ((when erp)
                ;; (er hard? 'get-recs-from-ml-model "Error in HTTP POST: ~@0" erp) ; was catching rare "output operation on closed SSL stream" errors
                (mv erp nil state)))
            (mv nil semi-parsed-response state))))
       ((when erp) (mv erp nil state)))
    (if (eq :start phase)
        (mv nil nil state) ;; todo: check that the parsed response is the expected string
      ;; We expect to have received actual recs:
      (b* (((when (not (acl2::parsed-json-arrayp semi-parsed-response)))
            (er hard? 'get-recs-from-ml-model "Error: Response from server is not a JSON array: ~x0." semi-parsed-response)
            (mv :bad-server-response nil state))
           (semi-parsed-recommendations (acl2::parsed-json-array->values semi-parsed-response))
           (- (if (not (consp semi-parsed-recommendations))
                  (cw " WARNING: No recommendations returned from server for ~x0.~%" model)
                (if (not (equal num-recs (len semi-parsed-recommendations)))
                    (cw " WARNING: Number of recs returned from server for ~x0 is ~x1 but we requested ~x2.~%" model (len semi-parsed-recommendations) num-recs)
                  nil)))
           ;; Parse the individual strings in the recs:
           ((mv erp ml-recommendations state) (parse-recommendations semi-parsed-recommendations model state))
           ((when erp)
            (er hard? 'get-recs-from-ml-model "Error parsing recommendations.")
            (mv erp nil state))
           (- (and debug (cw "Parsed ML recommendations: ~X01~%" ml-recommendations nil))))
        (mv nil ; no error
            ml-recommendations
            state)))))

;; Goes through the MODELS, getting recs from each.  Returns an alist from model-names to rec-lists.
;; Returns (mv erp model-rec-alist state), where MODEL-REC-ALIST maps model-names to rec lists.
(defun get-recs-from-models (model-info-alist
                             num-recs-per-model
                             disallowed-rec-types
                             checkpoint-clauses-top
                             checkpoint-clauses-non-top
                             translated-theorem-body
                             broken-theorem ; a thm or defthm form
                             timeout
                             debug
                             print
                             phase
                             acc
                             state)
  (declare (xargs :guard (and (model-info-alistp model-info-alist)
                              (natp num-recs-per-model)
                              (rec-type-listp disallowed-rec-types)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              (natp timeout)
                              (booleanp debug)
                              (acl2::print-levelp print)
                              (member-eq phase '(:retrieve :all)))
                  :mode :program
                  :stobjs state))
;  (declare (ignore checkpoint-clauses-non-top)) ; ttodo
  (if (endp model-info-alist)
      (mv nil (reverse acc) state) ; no error
    (b* ((entry (first model-info-alist))
         (model (car entry))
         (model-info (cdr entry))
         (print-timep (acl2::print-level-at-least-tp print))
         ;; Record the start time (if we will need it):
         ((mv start-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
         ;; Dispatch to the model:
         ((mv erp recs state)
          (case model
            ;; TODO: Make the dispatch to heursitics generic, so we don't have to mention them all here:
            (:enable-fns-body
             ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
             (if (member-eq :add-enable-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-enable-fns-body-recs translated-theorem-body num-recs-per-model print state)))
            (:enable-fns-top-cps
             ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
             (if (member-eq :add-enable-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-enable-fns-checkpoints-recs checkpoint-clauses-top num-recs-per-model print state)))
            (:enable-fns-non-top-cps
             ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
             (if (member-eq :add-enable-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-enable-fns-checkpoints-recs checkpoint-clauses-non-top num-recs-per-model print state)))
            (:enable-rules-body
             ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
             (if (member-eq :add-enable-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-enable-rules-body-recs translated-theorem-body num-recs-per-model print state)))
            (:enable-rules-top-cps
             ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
             (if (member-eq :add-enable-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-enable-rules-checkpoints-recs checkpoint-clauses-top num-recs-per-model print state)))
            (:enable-rules-non-top-cps
             ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
             (if (member-eq :add-enable-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-enable-rules-checkpoints-recs checkpoint-clauses-non-top num-recs-per-model print state)))
            (:history
             ;; Make recs based on hints given to recent theorems:
             (if (member-eq :exact-hints disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-recs-from-history num-recs-per-model print state)))
            (:induct
             ;; Make recs that suggest induction schemes:
             (if (member-eq :add-induct-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-induct-recs translated-theorem-body checkpoint-clauses-top checkpoint-clauses-non-top num-recs-per-model print state)))
            (:cases
             ;; Make recs that try splitting into cases:
             (if (member-eq :add-cases-hint disallowed-rec-types)
                 (mv nil nil state) ; don't bother creating recs as they will be disallowed below
               (make-cases-recs translated-theorem-body checkpoint-clauses-top checkpoint-clauses-non-top num-recs-per-model print state)))
            (otherwise
             ;; It's a normal ML model:
             (get-recs-from-ml-model model num-recs-per-model disallowed-rec-types checkpoint-clauses-top broken-theorem model-info timeout debug print phase state))))
         ((mv done-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
         (- (and erp (cw "Error using ~x0.~%" model))) ; but continue
         (- (if print-timep
                (let* ((time-diff (- done-time start-time))
                       (time-diff (if (< time-diff 0)
                                      (prog2$ (cw "Warning: negative elapsed time reported: ~x0.~%")
                                              0)
                                    time-diff)))
                  (progn$ (cw "Got ~x0 recs in " (len recs))
                          (acl2::print-to-hundredths time-diff)
                          (cw "s~%") ; s = seconds
                          ))
              (cw "Got ~x0 recs.~%" (len recs))))
         ;; Remove any recs that are disallowed (todo: drop this now? or print something here?):
         (recs (remove-disallowed-recs recs disallowed-rec-types nil)))
      (get-recs-from-models (rest model-info-alist)
                            num-recs-per-model disallowed-rec-types checkpoint-clauses-top checkpoint-clauses-non-top translated-theorem-body broken-theorem
                            timeout debug print phase
                            ;; Associate this model with its recs in the result:
                            (acons model recs acc)
                            state))))

;; Returns (mv erp state)
(defun startup-models (model-info-alist
                       num-recs-per-model
                       disallowed-rec-types
                       checkpoint-clauses-top
                       checkpoint-clauses-non-top
                       translated-theorem-body
                       broken-theorem ; a thm or defthm form
                       timeout
                       debug
                       print
                       state)
  (declare (xargs :guard (and (model-info-alistp model-info-alist)
                              (natp num-recs-per-model)
                              (rec-type-listp disallowed-rec-types)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              (natp timeout)
                              (booleanp debug)
                              (acl2::print-levelp print))
                  :mode :program
                  :stobjs state)
           (irrelevant translated-theorem-body) ; todo!
           )
  (if (endp model-info-alist)
      (mv nil state) ; no error
    (b* ((entry (first model-info-alist))
         (model (car entry))
         (model-info (cdr entry))
         (print-timep (acl2::print-level-at-least-tp print))
         ;; Record the start time (if we will need it):
         ((mv start-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
         ;; Dispatch to the model:
         ((mv erp
              & ; recs should be nil
              state)
          (case model
            ;; TODO: Make the dispatch to heursitics generic, so we don't have to mention them all here:
            ((:enable-fns-body :enable-fns-top-cps :enable-fns-non-top-cps
              :enable-rules-body :enable-rules-top-cps :enable-rules-non-top-cps
              :history :induct :cases)
             (mv nil nil state) ; no need to start the model
             )
            (otherwise
             ;; It's a normal ML model:
             (get-recs-from-ml-model model num-recs-per-model disallowed-rec-types checkpoint-clauses-top broken-theorem model-info timeout debug print :start state))))
         ((mv done-time state) (if print-timep (acl2::get-real-time state) (mv 0 state)))
         (- (and erp (cw "Error using ~x0.~%" model))) ; but continue
         (- (if print-timep
                (let* ((time-diff (- done-time start-time))
                       (time-diff (if (< time-diff 0)
                                      (prog2$ (cw "Warning: negative elapsed time reported: ~x0.~%")
                                              0)
                                    time-diff)))
                  (progn$ (cw "Started model in ")
                          (acl2::print-to-hundredths time-diff)
                          (cw "s~%") ; s = seconds
                          ))
              nil)))
      (startup-models (rest model-info-alist)
                      num-recs-per-model disallowed-rec-types checkpoint-clauses-top checkpoint-clauses-non-top translated-theorem-body broken-theorem
                      timeout debug print
                      ;; Associate this model with its recs in the result:
                      state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test whether REC1 is better than REC2 (todo: consider making this more sophisticated).
(defund better-recp (rec1 rec2)
  (declare (xargs :guard (and (successful-recommendationp rec1)
                              (successful-recommendationp rec2))
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (let ((type1 (nth 1 rec1))
        (type2 (nth 1 rec2)))
    ;; :add-hyp recs are worse than all others:
    (if (eq :add-hyp type1)
        nil
      (if (eq :add-hyp type2)
          t
        ;; neither is an :add-hyp:
        (if (eq :add-library type1)
            nil
          (if (eq :add-library type2)
              t
            nil))))))

(acl2::defmergesort merge-recs-by-quality merge-sort-recs-by-quality better-recp successful-recommendationp :extra-theorems nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Attempts to prove the given theorem using the given hints.  If the proof
;; worked, returns a recommendation that includes the hints that worked.
;; Otherwise, unless there is an error, returns the checkpoints from the failed
;; proof attempt.  Returns (mv erp provedp rec checkpoint-clauses-top checkpoint-clauses-non-top state) where
;; PROVEDP determines whether REC or CHECKPOINTS is meaningful.
(defun try-proof-and-get-checkpoint-clauses (theorem-name
                                             theorem-body
                                             translated-theorem-body
                                             theorem-hints
                                             theorem-otf-flg
                                             step-limit time-limit
                                             suppress-trivial-warningp
                                             state)
  (declare (xargs :guard (and (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              (pseudo-termp translated-theorem-body)
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (booleanp suppress-trivial-warningp))
                  :stobjs state
                  :mode :program))
  (b* ( ;; Try the theorem with the given hints (todo: consider also getting rid of any existng hints):
       ((mv provedp state)
        ;; todo: print if a limit is reached
        (prove$-no-error 'try-proof-and-get-checkpoints theorem-body theorem-hints theorem-otf-flg step-limit time-limit state))
       ;; TODO: What if the step-limit applied?  We may want to see how many steps this attempt uses, to decide how many steps to allow in future attempts.
       ((when provedp)
        ;; The original hints worked!
        (and (not suppress-trivial-warningp)
             (if (not theorem-hints)
                 (cw "WARNING: Proved ~x0 with no hints.~%" theorem-name)
               (cw "WARNING: Proved ~x0 with original hints.~%" theorem-name)))
        (mv nil ; no error
            t   ; proved (with the original hints)
            (make-successful-rec "original" :exact-hints theorem-hints nil theorem-body theorem-hints theorem-otf-flg :unavailable)
            nil ; checkpoints, meaningless
            nil ; checkpoints, meaningless
            state))
       ;; The proof failed, so get the checkpoints:
       (raw-checkpoint-clauses-top (acl2::checkpoint-list t ; top-level checkpoints
                                                          state))
       ((when (eq :unavailable raw-checkpoint-clauses-top))
        ;; Can this happen?  :doc Checkpoint-list indicates that :unavailable means the proof succeeded.
        (cw "WARNING: Unavailable checkpoints after failed proof of ~x0.~%" theorem-name)
        (mv :no-checkpoints nil nil nil nil state))
       ;; Deal with unfortunate case when acl2 decides to backtrack and try induction:
       ;; TODO: Or use :otf-flg to get the real checkpoints?
       (checkpoint-clauses-top (if (equal raw-checkpoint-clauses-top '((acl2::<goal>)))
                               (prog2$ (cw "Note: Replacing bogus checkpoints.~%") ; todo: eventually remove this?
                                       (clausify-term translated-theorem-body (w state)))
                             raw-checkpoint-clauses-top))
       ((when (null checkpoint-clauses-top))
        ;; A step-limit may fire before checkpoints can be generated:
        (cw "WARNING: No checkpoints after failed proof of ~x0 (perhaps a limit fired).~%" theorem-name)
        (mv :no-checkpoints nil nil nil nil state))
       ;; Now the non-top checkpoints, of which there may be none:
       (checkpoint-clauses-non-top (acl2::checkpoint-list nil ; non-top-level checkpoints
                                                          state))
       ;; todo: any special values to handle here?
       )
    (mv nil ; no error
        nil ; didn't prove
        nil ; meaningless
        checkpoint-clauses-top
        checkpoint-clauses-non-top
        state)))

;; Gets recommendations from all models and tries them.
;; Returns (mv erp successp best-rec state).
(defun best-rec-for-checkpoints (checkpoint-clauses-top
                                 checkpoint-clauses-non-top
                                 theorem-name
                                 theorem-body
                                 theorem-hints
                                 theorem-otf-flg
                                 broken-theorem
                                 num-recs-per-model
                                 current-book-absolute-path
                                 avoid-current-bookp
                                 improve-recsp
                                 print
                                 model-info-alist
                                 timeout
                                 debug
                                 step-limit time-limit
                                 disallowed-rec-types ;todo: for this, handle the similar treatment of :use-lemma and :add-enable-hint?
                                 max-wins
                                 start-and-return
                                 state)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              ;; broken-theorem is a thm or defthm form
                              (natp num-recs-per-model)
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (model-info-alistp model-info-alist)
                              (natp timeout)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (or ;; (eq :auto max-wins)
                               (null max-wins)
                               (natp max-wins))
                              (rec-type-listp disallowed-rec-types)
                              (booleanp start-and-return))
                  :stobjs state
                  :mode :program))
  (b* ((state (acl2::widen-margins state))
       ;; Start all the models working, in parallel:
       (translated-theorem-body (acl2::translate-term theorem-body 'best-rec-for-checkpoints (w state)))

       ;; Maybe start the models working:
       ((mv erp state)
        (if start-and-return
            (prog2$ (cw "Starting the models:~%")
                    (startup-models model-info-alist num-recs-per-model disallowed-rec-types checkpoint-clauses-top checkpoint-clauses-non-top
                                    translated-theorem-body broken-theorem timeout debug print state))
          (mv nil state)))
       ((when erp) (mv erp nil nil state))

       ;; Go back and get the recs from the models (TODO: Could reduce waiting even more by trying some recs first):
       ;; WARNING: Keep args in sync between startup-models and get-recs-from-models (except startup-models has no acc)!
       (- (cw "Querying the models:~%"))
       ((mv erp model-rec-alist state)
        (get-recs-from-models model-info-alist num-recs-per-model disallowed-rec-types checkpoint-clauses-top checkpoint-clauses-non-top
                              translated-theorem-body broken-theorem timeout debug print
                              (if start-and-return :retrieve :all)
                              nil state))
       ((when erp) (mv erp nil nil state))
       ;; Combine all the lists:
       (recommendation-lists (strip-cdrs model-rec-alist))
       (recommendations (merge-rec-lists-into-recs recommendation-lists nil)) ; also removes duplicates
       ;; Sort the whole list by confidence (hope the numbers are comparable):
       (recommendations (merge-sort-recs-by-confidence recommendations)) ; todo: not a stable sort, messes up the order
       ;; Maybe print the recommendations:
       (state (if (acl2::print-level-at-least-tp print)
                  (prog2$ (cw "~%RECOMMENDATIONS TO TRY:~%")
                          (show-recommendations recommendations state))
                state))
       ;; Try the recommendations:
       (- (and print (cw "~%TRYING ~x0 RECOMMENDATIONS:~%" (len recommendations))))
       ((mv erp successful-recs extra-recs-ignoredp state)
        (try-recommendations recommendations current-book-absolute-path avoid-current-bookp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit time-limit max-wins improve-recsp print nil state))
       (state (acl2::unwiden-margins state))
       ((when erp)
        (er hard? 'advice-fn "Error trying recommendations: ~x0" erp)
        (mv erp nil nil state))
       ;; Remove duplicates:
       (successful-recs-no-dupes (merge-successful-recs-into-recs successful-recs nil))
       (removed-count (- (len successful-recs) (len successful-recs-no-dupes)))
       (- (and (posp removed-count)
               (acl2::print-level-at-least-tp print)
               (cw "~%NOTE: ~x0 duplicate ~s1 removed.~%" removed-count
                   (if (< 1 removed-count) "successful recommendations were" "successful recommendation was"))))
       (num-successful-recs (len successful-recs-no-dupes))
       (- (and extra-recs-ignoredp ;;max-wins-reachedp
               (acl2::print-level-at-least-tp print)
               (cw "~%NOTE: Search stopped after finding ~x0 successful ~s1.~%" max-wins (if (< 1 max-wins) "recommendations" "recommendation"))))
       ;; Sort the recs:
       (sorted-successful-recs (merge-sort-recs-by-quality successful-recs-no-dupes))
       ;; Show the successful recs:
       (state (if (posp num-successful-recs)
                  (if print
                      (progn$ (if (< 1 num-successful-recs)
                                  (cw "~%PROOF FOUND (~x0 successful recommendations):~%" num-successful-recs)
                                (cw "~%PROOF FOUND (1 successful recommendation):~%"))
                              (progn$ ;; (cw "~%SUCCESSFUL RECOMMENDATIONS:~%")
                               (let ((state (show-successful-recommendations sorted-successful-recs state))) ; why does this return state?
                                 state)))
                    state)
                (prog2$ (and print (cw "~%NO PROOF FOUND~%~%"))
                        state))))
    (mv nil                        ; no error
        (posp num-successful-recs) ; whether we succeeded
        (first sorted-successful-recs)
        state)))

;; Tries the theorem with the supplied hints.  If that doesn't prove the theorem, this requests and tries advice.
;; Returns (mv erp successp best-rec state).
(defun best-rec-for-theorem (theorem-name
                             theorem-body
                             translated-theorem-body
                             theorem-hints
                             theorem-otf-flg
                             broken-theorem
                             num-recs-per-model
                             current-book-absolute-path
                             avoid-current-bookp
                             improve-recsp
                             print
                             model-info-alist
                             timeout
                             debug
                             step-limit time-limit
                             disallowed-rec-types
                             max-wins
                             suppress-trivial-warningp
                             start-and-return
                             state)
  (declare (xargs :guard (and (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              (pseudo-termp translated-theorem-body)
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              ;; broken-theorem is a thm or defthm form
                              (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp avoid-current-bookp)
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (model-info-alistp model-info-alist)
                              (natp timeout)
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (rec-type-listp disallowed-rec-types)
                              (or ;; (eq :auto max-wins)
                               (null max-wins)
                               (natp max-wins))
                              (booleanp suppress-trivial-warningp)
                              (booleanp start-and-return))
                  :stobjs state
                  :mode :program))
  (b* (((mv erp provedp rec checkpoint-clauses-top checkpoint-clauses-non-top state)
        (try-proof-and-get-checkpoint-clauses theorem-name
                                              theorem-body
                                              translated-theorem-body
                                              theorem-hints
                                              theorem-otf-flg
                                              step-limit time-limit
                                              suppress-trivial-warningp
                                              state))
       ((when erp) (mv erp nil nil state)))
    (if provedp
        (mv nil ; no error
            t   ; success
            rec
            state)
      ;; Didn't prove using the supplied hints, so try advice:
      (best-rec-for-checkpoints checkpoint-clauses-top
                                checkpoint-clauses-non-top
                                theorem-name
                                theorem-body
                                theorem-hints
                                theorem-otf-flg
                                broken-theorem
                                num-recs-per-model
                                current-book-absolute-path
                                avoid-current-bookp
                                improve-recsp
                                print
                                model-info-alist
                                timeout
                                debug
                                step-limit time-limit
                                disallowed-rec-types
                                max-wins
                                start-and-return
                                state))))

;; Keeps the entries in ALIST that correspond to the MODELS.  Also does some
;; checking and skips models whose info is nil.
(defund filter-advice-server-alist (alist models)
  (declare (xargs :guard (and (model-info-alistp alist)
                              (acl2::keyword-listp models))))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (name (car entry))
           (info (cdr entry)))
      (if (not (member-eq name models))
          (filter-advice-server-alist (rest alist) models)
        (if (null info)
            (prog2$ (cw "NOTE: Skipping model ~x0 (disabled).~%" name) ; perhaps the user called TABLE with a value of nil to suppress the model
                    (filter-advice-server-alist (rest alist) models))
          (if (not (model-infop info))
              (er hard? 'filter-advice-server-alist "Bad model info: ~x0." entry)
            (cons entry (filter-advice-server-alist (rest alist) models))))))))

;; Returns a model-info-alist representing the selected MODELS, using the acl2::advice-server table.
(defund make-model-info-alist (models wrld)
  (declare (xargs :guard (and (or (eq :all models)
                                  (eq :non-ml models)
                                  (model-namep models) ; represents a singleton set
                                  (model-namesp models))
                              (plist-worldp wrld))
                  :verify-guards nil ; todo: and use tools!
                  ))
  (let* (;; Desugar :non-ml option:
         (models (if (eq :non-ml models) *function-models* models))
         ;; single model stands for singleton list of that model:
         (models (if (model-namep models) ; excludes :all
                     (list models)
                   models))
         ;; reverse, just to match the order in which the user probably set the keys:
         (advice-server-alist (reverse (table-alist 'acl2::advice-server wrld))))
    (if (not (and (model-info-alistp advice-server-alist)
                  (no-duplicatesp (strip-cars advice-server-alist))))
        (er hard? 'make-model-info-alist "Bad advice-server-alist: ~x0." advice-server-alist)
      (let* ( ;; Models that are simply ACL2 functions:
             (all-function-models *function-models*)
             (function-models (if (eq :all models)
                                  all-function-models
                                (intersection-eq all-function-models models)))
             ;; Server models:
             (all-server-models (strip-cars advice-server-alist))
             (server-models (if (eq :all models)
                                all-server-models
                              (intersection-eq all-server-models models)))
             (unknown-models (if (eq :all models)
                                 nil
                               (set-difference-eq (set-difference-eq models function-models) server-models))))
        (if unknown-models
            (er hard? 'make-model-info-alist "Unknown models: ~x0." unknown-models)
          (append (acons-all-to-val function-models :function nil)
                  (filter-advice-server-alist advice-server-alist server-models)))))))

;; Returns (mv erp event state).
(defun defthm-advice-fn (theorem-name
                         theorem-body ; an untranslated term
                         theorem-hints
                         theorem-otf-flg
                         rule-classes
                         num-recs-per-model
                         improve-recsp
                         print
                         timeout
                         debug
                         step-limit time-limit
                         disallowed-rec-types
                         max-wins
                         models
                         start-and-return
                         state)
  (declare (xargs :guard (and (symbolp theorem-name)
                              ;; theorem-body
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              ;; rule-classes
                              (natp num-recs-per-model)
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (natp timeout)
                              (booleanp debug)
                              (or (eq :auto step-limit) ; means use *step-limit*
                                  (eq nil step-limit) ; means no limit
                                  (natp step-limit))
                              (or (eq :auto time-limit) ; means use *time-limit*
                                  (eq nil time-limit) ; means no limit
                                  (rationalp time-limit))
                              (rec-type-listp disallowed-rec-types)
                              (or (eq :auto max-wins)
                                  (null max-wins)
                                  (natp max-wins))
                              (or (eq :all models)
                                  (eq :non-ml models)
                                  (model-namep models) ; represents a singleton set
                                  (model-namesp models))
                              (booleanp start-and-return))
                  :stobjs state
                  :mode :program))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (model-info-alist (make-model-info-alist models wrld))
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (time-limit (if (eq :auto time-limit) *time-limit* time-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       (translated-theorem-body (acl2::translate-term theorem-body 'defthm-advice-fn wrld))
       ((mv erp successp best-rec state)
        (best-rec-for-theorem theorem-name
                              theorem-body
                              translated-theorem-body
                              theorem-hints
                              theorem-otf-flg
                              ;; the presumed broken-theorem:
                              `(defthm ,theorem-name ,theorem-body
                                 ,@(and theorem-otf-flg `(:otf-flg ,theorem-otf-flg))
                                 ,@(and theorem-hints `(:hints ,theorem-hints)))
                              num-recs-per-model
                              nil ; no book to avoid (for now)
                              t
                              improve-recsp
                              print
                              model-info-alist
                              timeout
                              debug
                              step-limit time-limit
                              disallowed-rec-types
                              max-wins
                              nil
                              start-and-return
                              state))
       ((when erp) (mv erp nil state)))
    (if successp
        (let ((event (successful-rec-to-defthm 'defthm theorem-name best-rec rule-classes)))
          (prog2$ (and print (cw "Submitting:~%~X01~%" event nil)) ; todo: improve indenting when printing
                  (mv nil event state)))
      (mv :no-proof-found nil state))))

;; A replacement for defthm that uses advice to try to prove the theorem.  Note
;; that this may be slow (if many pieces of advice are tried), and it makes a
;; call to the advice server over the Internet.  So it may be best not to leave
;; calls of defthm-advice in your book, once suitable advice has been found.
;; todo: add instructions
(defmacro defthm-advice (name
                         body
                         &key
                         (hints 'nil)
                         (otf-flg 'nil)
                         ;; options for the advice:
                         (n '10) ; num-recs-per-model
                         (improve-recsp 't)
                         (print 't)
                         (timeout '60) ; for both connection timeout and read timeout
                         (debug 'nil)
                         (step-limit ':auto)
                         (time-limit ':auto)
                         (disallowed-rec-types 'nil)
                         (max-wins ':auto)
                         (models ':all)
                         (rule-classes '(:rewrite))
                         (start-and-return 't)
                         )
  `(acl2::make-event-quiet
    (defthm-advice-fn ',name ',body ',hints ,otf-flg ',rule-classes ,n ,improve-recsp ,print ,timeout ,debug ,step-limit ,time-limit ',disallowed-rec-types ,max-wins ,models ',start-and-return state)))

;; Just a synonym in ACL2 package
(defmacro acl2::defthm-advice (&rest rest) `(defthm-advice ,@rest))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event state).
(defun thm-advice-fn (theorem-body ; an untranslated term
                      theorem-hints
                      theorem-otf-flg
                      num-recs-per-model
                      improve-recsp
                      print
                      timeout
                      debug
                      step-limit time-limit
                      disallowed-rec-types
                      max-wins
                      models
                      start-and-return
                      state)
  (declare (xargs :guard (and ;; theorem-body
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (natp num-recs-per-model)
                          (booleanp improve-recsp)
                          (acl2::print-levelp print)
                          (natp timeout)
                          (booleanp debug)
                          (or (eq :auto step-limit)   ; means use *step-limit*
                              (eq nil step-limit)     ; means no limit
                              (natp step-limit))
                          (or (eq :auto time-limit)   ; means use *time-limit*
                              (eq nil time-limit)     ; means no limit
                              (rationalp time-limit))
                          (rec-type-listp disallowed-rec-types)
                          (or (eq :auto max-wins)
                              (null max-wins)
                              (natp max-wins))
                          (or (eq :all models)
                              (eq :non-ml models)
                              (model-namep models) ; represents a singleton set
                              (model-namesp models))
                          (booleanp start-and-return))
                  :stobjs state
                  :mode :program))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (model-info-alist (make-model-info-alist models wrld))
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (time-limit (if (eq :auto time-limit) *time-limit* time-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       (translated-theorem-body (acl2::translate-term theorem-body 'thm-advice-fn wrld))
       ((mv erp successp best-rec state)
        (best-rec-for-theorem 'the-thm
                              theorem-body
                              translated-theorem-body
                              theorem-hints
                              theorem-otf-flg
                              ;; the presumed broken-theorem:
                              `(thm ,theorem-body
                                 ,@(and theorem-otf-flg `(:otf-flg ,theorem-otf-flg))
                                 ,@(and theorem-hints `(:hints ,theorem-hints)))
                              num-recs-per-model
                              nil ; no book to avoid (for now)
                              t
                              improve-recsp
                              print
                              model-info-alist
                              timeout
                              debug
                              step-limit time-limit
                              disallowed-rec-types
                              max-wins
                              nil
                              start-and-return
                              state))
       ((when erp) (mv erp nil state)))
    (if successp
        (let ((event (successful-rec-to-thm best-rec)))
          (prog2$ (and print (cw "Submitting:~%~X01~%" event nil)) ; todo: improve indenting when printing
                  (mv nil event state)))
      (mv :no-proof-found nil state))))

;; todo: add instructions
(defmacro thm-advice ( ; no name
                      body
                      &key
                      (hints 'nil)
                      (otf-flg 'nil)
                      ;; options for the advice:
                      (n '10) ; num-recs-per-model
                      (print 't)
                      (timeout '60) ; for both connection timeout and read timeout
                      (debug 'nil)
                      (step-limit ':auto)
                      (time-limit ':auto)
                      (disallowed-rec-types 'nil)
                      (max-wins ':auto)
                      (models ':all)
                      (improve-recsp 't)
                      ;; no rule-classes
                      (start-and-return 't)
                      )
  `(acl2::make-event-quiet
    (thm-advice-fn ',body ',hints ,otf-flg ,n ,improve-recsp ,print ,timeout ,debug ,step-limit ,time-limit ',disallowed-rec-types ,max-wins ,models ',start-and-return  state)))

;; Just a synonym in ACL2 package
(defmacro acl2::thm-advice (&rest rest) `(thm-advice ,@rest))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nil state).
;; TODO: Support getting checkpoints from a defun, but then we'd have no body
;; to fall back on when (equal untranslated-checkpoints '(<goal>)) (see
;; below).
(defun advice-fn (n ; number of recommendations from ML requested
                  improve-recsp
                  print
                  timeout
                  debug
                  step-limit time-limit
                  disallowed-rec-types
                  max-wins
                  models
                  start-and-return
                  state)
  (declare (xargs :guard (and (natp n)
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (natp timeout)
                              (acl2::checkpoint-list-guard t ;top-p
                                                     state)
                              (booleanp debug)
                              (or (eq :auto step-limit)
                                  (eq nil step-limit)
                                  (natp step-limit))
                              (or (eq :auto time-limit)
                                  (eq nil time-limit)
                                  (rationalp time-limit))
                              (rec-type-listp disallowed-rec-types)
                              (or (eq :auto max-wins)
                                  (null max-wins)
                                  (natp max-wins))
                              (or (eq :all models)
                                  (eq :non-ml models)
                                  (model-namep models) ; represents a singleton set
                                  (model-namesp models))
                              (booleanp start-and-return))
                  :stobjs state
                  :mode :program ; because we untranslate (for now)
                  ))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (model-info-alist (make-model-info-alist models wrld))
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (time-limit (if (eq :auto time-limit) *time-limit* time-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       ;; Get most recent failed theorem:
       (most-recent-failed-theorem (acl2::most-recent-failed-command acl2::*theorem-event-types* state))
       ((mv theorem-name theorem-body theorem-hints theorem-otf-flg) ; todo: hints won't be right for rule/defrule
        (if (member-eq (car most-recent-failed-theorem) '(thm acl2::rule))
            (mv :thm ; no name
                (cadr most-recent-failed-theorem)
                (cadr (assoc-keyword :hints (cddr most-recent-failed-theorem)))
                (cadr (assoc-keyword :otf-flg (cddr most-recent-failed-theorem))))
          ;; Must be a defthm, defrule, etc:
          (mv (cadr most-recent-failed-theorem)
              (caddr most-recent-failed-theorem)
              (cadr (assoc-keyword :hints (cdddr most-recent-failed-theorem)))
              (cadr (assoc-keyword :otf-flg (cdddr most-recent-failed-theorem))))))
       (- (and print (cw "Generating advice for:~%~X01:~%" most-recent-failed-theorem nil)))
       (- (and (acl2::print-level-at-least-tp print) (cw "Original hints were:~%~X01.~%" theorem-hints nil)))
       ;; Get the checkpoints from the failed attempt:
       ;; TODO: Consider trying again with no hints, in case the user gave were wrongheaded.
       (raw-checkpoint-clauses-top (acl2::checkpoint-list t ; top-level checkpoints
                                    state))
       ((when (eq :unavailable raw-checkpoint-clauses-top))
        (er hard? 'advice-fn "No checkpoints are available (perhaps the most recent theorem succeeded).")
        (mv :no-checkpoints nil state))
       ;; Deal with unfortunate case when acl2 decides to backtrack and try induction:
       ;; TODO: Or use :otf-flg to get the real checkpoints?
       (checkpoint-clauses-top (if (equal raw-checkpoint-clauses-top '((acl2::<goal>)))
                               (clausify-term (acl2::translate-term (acl2::most-recent-failed-theorem-goal state)
                                                                    'advice-fn
                                                                    wrld)
                                              wrld)
                               raw-checkpoint-clauses-top))
       (checkpoint-clauses-non-top (acl2::checkpoint-list nil ; non-top-level checkpoints
                                                          state))
       (- (and (acl2::print-level-at-least-tp print) (cw "Top-level Proof checkpoints to use: ~X01.~%" checkpoint-clauses-top nil)))
       (- (and (acl2::print-level-at-least-tp print) (cw "Non-top-level Proof checkpoints to use: ~X01.~%" checkpoint-clauses-non-top nil)))
       ((mv erp
            & ;; successp
            & ;; best-rec
            state)
        (best-rec-for-checkpoints checkpoint-clauses-top
                                  checkpoint-clauses-non-top
                                  theorem-name
                                  theorem-body
                                  theorem-hints
                                  theorem-otf-flg
                                  most-recent-failed-theorem
                                  n ; number of recommendations from ML requested
                                  nil ; no current-book (TODO: Maybe avoid the last LDed book, in case they are working on it now)
                                  t ; avoid the current-book (but there isn't one, currently)
                                  improve-recsp
                                  print
                                  model-info-alist
                                  timeout
                                  debug
                                  step-limit time-limit
                                  disallowed-rec-types
                                  max-wins
                                  start-and-return
                                  state))
       ((when erp) (mv erp nil state))
       ;; Ensure there are no checkpoints left over from an attempt to use advice, in case the user calls the tool again.
       ;; TODO: Can we restore the old gag state saved?
       ;;(state (f-put-global 'gag-state-saved nil state))

       ;; Try to ensure the checkpoints are restored, in case the tool is run again:
       (state
        (b* ((new-raw-checkpoint-clauses-top (acl2::checkpoint-list
                                              t ; todo: consider non-top
                                              state))
             ((when (equal new-raw-checkpoint-clauses-top raw-checkpoint-clauses-top))
              state ; no need to do anything
              )
             ((mv provedp state)
              (prove$-no-error 'advice-fn theorem-body theorem-hints theorem-otf-flg
                               nil ; step-limit
                               nil ; time-limit
                               state))
             ((when provedp) ; surprising!
              (cw "WARNING: Tried the theorem again and it worked!")
              state)
             (new-raw-checkpoint-clauses-top (acl2::checkpoint-list
                                              t ; todo: consider non-top
                                              state))
             ((when (not (equal new-raw-checkpoint-clauses-top raw-checkpoint-clauses-top)))
              (acl2::print-level-at-least-tp print)
              (cw "Clearing checkpoints since we failed to restore them.~%")
              (let ((state (f-put-global 'gag-state-saved nil state)))
                state)))
          state)))
       (mv nil ; no error
        '(value-triple :invisible) state)))

;; Generate advice for the most recent failed theorem.
(defmacro advice (&key (n '10) ; num-recs-per-model
                       (improve-recsp 't)
                       (print 't)
                       (timeout '60) ; for both connection timeout and read timeout
                       (debug 'nil)
                       (step-limit ':auto)
                       (time-limit ':auto)
                       (disallowed-rec-types 'nil)
                       (max-wins ':auto)
                       (models ':all)
                       (start-and-return 't))
  `(acl2::make-event-quiet (advice-fn ,n ,improve-recsp ,print ,timeout ,debug ,step-limit ,time-limit ',disallowed-rec-types ,max-wins ,models ',start-and-return state)))

;; Just a synonym in ACL2 package
(defmacro acl2::advice (&rest rest) `(advice ,@rest))

;; Example:
;; (acl2s-defaults :set testing-enabled nil) ; turn off testing
;; (thm (equal (- (- x)) x))
;; (advice)
;; (thm (< (mod x 8) 256))
;; (advice)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This supports the generation of training data to improve an existing ML model.
;; Returns (mv erp successful-actions state) where each successful-action is of the form (<action-type> <action-object> <symbol-table>).
;; TODO: Also return the source of each rec?
;; TODO: Also return unsuccessful actions?
;; WARNING: This should not be used for evaluation of models/recommendations, as it allows the current-book to be used to prove checkpoints from its own theorems!
(defun all-successful-actions-for-checkpoints (checkpoint-clauses-top
                                               checkpoint-clauses-non-top
                                               theorem-body ; untranslated
                                               theorem-hints
                                               theorem-otf-flg
                                               num-recs-per-model
                                               current-book-absolute-path
                                               improve-recsp ; whether to try to improve successful recommendations
                                               print
                                               model-info-alist
                                               ;; timeout: TODO add
                                               debug
                                               step-limit
                                               time-limit
                                               disallowed-rec-types ; todo: for this, handle the similar treatment of :use-lemma and :add-enable-hint?
                                               state)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp checkpoint-clauses-top)
                              (acl2::pseudo-term-list-listp checkpoint-clauses-non-top)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (natp num-recs-per-model)
                              (or (null current-book-absolute-path)
                                  (stringp current-book-absolute-path))
                              (booleanp improve-recsp)
                              (acl2::print-levelp print)
                              (model-info-alistp model-info-alist)
                              ;; (natp timeout) ; todo
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null time-limit)
                                  (rationalp time-limit))
                              (rec-type-listp disallowed-rec-types))
                  :stobjs state
                  :mode :program))
  (b* ( ;; Get all the recs to try:
       (broken-theorem ;; the presumed broken-theorem:
        `(defthm fake-theorem-name ; todo: use the real name?
           ,theorem-body
           ,@(and theorem-otf-flg `(:otf-flg ,theorem-otf-flg))
           ,@(and theorem-hints `(:hints ,theorem-hints))))
       (translated-theorem-body (acl2::translate-term theorem-body 'all-successful-actions-for-checkpoints (w state)))
       (timeout 40 ; todo
                )
       ((mv erp model-rec-alist state)
        (get-recs-from-models model-info-alist num-recs-per-model disallowed-rec-types checkpoint-clauses-top checkpoint-clauses-non-top
                              translated-theorem-body broken-theorem timeout debug print
                              :all ; todo: can we use start-and-return here?
                              nil state))
       ((when erp) (mv erp nil state))
       ;; Combine all the lists:
       (recommendation-lists (strip-cdrs model-rec-alist))
       (recommendations (merge-rec-lists-into-recs recommendation-lists nil)) ; also removes duplicates
       ;; Maybe print the recommendations:
       (state (if (acl2::print-level-at-least-tp print)
                  (prog2$ (cw "~%RECOMMENDATIONS TO TRY:~%")
                          (show-recommendations recommendations state))
                state))
       ;; Try the recommendations:
       (- (and print (cw "~%TRYING RECOMMENDATIONS:~%")))
       (state (acl2::widen-margins state))
       ((mv erp successful-recs
            & ; extra-recs-ignoredp
            state)
        (try-recommendations recommendations current-book-absolute-path
                             nil ; avoid-current-bookp ; allow recs from the current book, since we are just generating training data
                             :thm
                             theorem-body theorem-hints theorem-otf-flg step-limit time-limit
                             nil ; max-wins
                             improve-recsp print nil state))
       (state (acl2::unwiden-margins state))
       ((when erp)
        (er hard? 'advice-fn "Error trying recommendations: ~x0" erp)
        (mv erp nil state))
       ;; Remove duplicates:
       (successful-recs-no-dupes (merge-successful-recs-into-recs successful-recs nil))
       ;; (removed-count (- (len successful-recs) (len successful-recs-no-dupes)))
       ;; (- (and (posp removed-count)
       ;;         (acl2::print-level-at-least-tp print)
       ;;         (cw "~%NOTE: ~x0 duplicate ~s1 removed.~%" removed-count
       ;;             (if (< 1 removed-count) "successful recommendations were" "successful recommendation was"))))
       (num-successful-recs (len successful-recs-no-dupes))
       (- (and print
               (if (= 0 num-successful-recs)
                   (cw "~%(No successful recommendations):~%")
                 (if (= 1 num-successful-recs)
                     (cw "~%(1 successful recommendation):~%")
                   (cw "~%(~x0 successful recommendations):~%" num-successful-recs))))))
    (mv nil ; no error
        (extract-actions-from-successful-recs successful-recs)
        state)))

;; Example call:
;; (help::all-successful-actions-for-checkpoints (list (list '(equal (len (append x y)) (binary-+ (len x) (len y)))))
;;                                               (list (list '(equal (len (append x y)) (binary-+ (len x) (len y)))))
;;                                               '(equal (len (append x y)) (+ (len x) (len y)))
;;                                               nil ; theorem-hints
;;                                               nil ; theorem-otf-flg
;;                                               10  ; num-recs-per-model
;;                                               "/home/ewsmith/acl2/books/kestrel/arithmetic-light/mod.lisp" ; current-book-absolute-path
;;                                               t ; whether to try to improve successful recommendations
;;                                               nil ; print
;;                                               nil ; debug
;;                                               nil ; step-limit
;;                                               nil ; time-limit
;;                                               '(:add-hyp :exact-hints) ; disallowed-rec-types
;;                                               help::*known-models*
;;                                               state)
