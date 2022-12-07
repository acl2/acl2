; A tool to get proof advice from a server over the web
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HELP")

;; SETUP:
;;
;; 1. Set the ACL2_ADVICE_SERVER environment variable to the server URL (often
;; ends in '/machine_interface')
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

(include-book "kestrel/utilities/checkpoints" :dir :system)
(include-book "kestrel/utilities/nat-to-string" :dir :system)
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/theory-hints" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/prove-dollar-plus" :dir :system)
(include-book "kestrel/utilities/read-string" :dir :system) ; todo: slowish
(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/wrap-all" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/included-books-in-world" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/world-light/defined-fns-in-term" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/strings-light/downcase" :dir :system)
(include-book "kestrel/typed-lists-light/string-list-listp" :dir :system)
(include-book "kestrel/untranslated-terms/conjuncts-of-uterm" :dir :system)
(include-book "kestrel/alists-light/string-string-alistp" :dir :system)
(include-book "kestrel/htclient/post" :dir :system) ; todo: slow
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/big-data/packages" :dir :system) ; try to ensure all packages that might arise are known ; todo: very slow
(include-book "tools/prove-dollar" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/utilities/coerce" :dir :system))

(local (in-theory (disable member-equal len true-listp nth)))

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
    (let* ((macro-aliases-table (table-alist 'acl2::macro-aliases-table wrld)))
      (if (not (alistp macro-aliases-table))
          (er hard? 'handle-macro-alias "Bad macro aliases table.")
        (let ((res (assoc-eq name macro-aliases-table)))
          (if res
              (if (symbolp (cdr res))
                  (cdr res)
                (er hard? 'handle-macro-alias "Bad macro aliases table."))
            name))))))

(local (in-theory (disable state-p
                           acl2::checkpoint-list-guard
                           global-table
                           put-global
                           get-global
                           set-fmt-hard-right-margin
                           acl2::deref-macro-name)))

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

(defun make-numbered-checkpoint-entries (current-number checkpoints)
  (declare (xargs :mode :program)) ; because we call fms-to-string
  (if (endp checkpoints)
      nil
    (acons (concatenate 'string "checkpoint_" (acl2::nat-to-string current-number))
           (fms-to-string "~X01" (acons #\0 (first checkpoints) (acons #\1 nil nil)))
           (make-numbered-checkpoint-entries (+ 1 current-number) (rest checkpoints)))))

(defconst *rec-to-symbol-alist*
  '(("add-by-hint" . :add-by-hint) ; rare
    ("add-cases-hint" . :add-cases-hint) ; rare
    ("add-disable-hint" . :add-disable-hint)
    ("add-do-not-hint" . :add-do-not-hint) ; very rare
    ("add-enable-hint" . :add-enable-hint)
    ("add-expand-hint" . :add-expand-hint)
    ("add-hyp" . :add-hyp)
    ("add-induct-hint" . :add-induct-hint)
    ("add-library" . :add-library)
    ("add-nonlinearp-hint" . :add-nonlinearp-hint) ; very rare
    ("add-use-hint" . :add-use-hint)
    ;; Confusingly named: Does not indicate a :use hint:
    ("use-lemma" . :use-lemma)))

(defconst *ml-rec-types* (strip-cdrs *rec-to-symbol-alist*))

(defconst *all-rec-types* (cons :exact-hints *ml-rec-types*))

(defund confidence-percentp (p)
  (declare (xargs :guard t))
  (and (rationalp p)
       (<= 0 p)
       (<= p 100)))

(defconst *known-models-and-strings*
  '((:calpoly . "kestrel-calpoly")
    ;; note the capital L:
    (:leidos . "Leidos")
    ;; (:leidos-gpt . "leidos-gpt")
    ))

(defconst *known-models* (strip-cars *known-models-and-strings*))

(defconst *extra-rec-sources*
  '(:enable :history))

;; Indicates one of the machine learning recommendation models.  Either one of
;; the known models, or a string representing some unknown model (gets passed
;; through to the HTTP request).
(defund model-namep (x)
  (declare (xargs :guard t))
  (or (stringp x) ; raw string to pass in the HTTP POST data
      (member-eq x *known-models*) ; known models
      ))

;; Recognizes a (duplicate-free) list of recommendation models.
(defund model-namesp (models)
  (declare (xargs :guard t))
  (if (atom models)
      (null models)
    (and (model-namep (first models))
         ;; (not (member-equal (first models) (rest models))) ;; todo: add back?
         (model-namesp (rest models)))))

(defun model-to-string (model)
  (declare (xargs :guard (model-namep model)))
  (if (stringp model)
      model
    ;; must be a keyword indicating a known model:
    (let ((res (assoc-eq model *known-models-and-strings*)))
      (if res
          (cdr res)
        (er hard? 'model-to-string "Unknown :model: ~x0." model)))))

(defun model-to-nice-string (model)
  (declare (xargs :guard (model-namep model)
                  :guard-hints (("Goal" :in-theory (enable model-namep member-equal)))))
  (if (stringp model)
      model
    ;; must be a keyword indicating a known model:
    (acl2::string-downcase-gen (symbol-name model))))

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

(defund pre-commandsp (pre-commands)
  (declare (xargs :guard t))
  (true-listp pre-commands))

(defund rec-typep (type)
  (declare (xargs :guard t))
  (member-eq type *all-rec-types*))

(defthm rec-typep-forward-to-symbolp
  (implies (rec-typep type)
           (symbolp type))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rec-typep member-equal))))

(defund rec-type-listp (types)
  (declare (xargs :guard t))
  (if (not (consp types))
      (null types)
    (and (rec-typep (first types))
         (rec-type-listp (rest types)))))

(defthm rec-type-listp-forward-to-symbol-listp
  (implies (rec-type-listp types)
           (symbol-listp types))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rec-type-listp))))

(defund include-book-formp (form)
  (declare (xargs :guard t))
  (and (consp form)
       (true-listp form)
       (eq 'include-book (car form))
       (stringp (cadr form))
       ;; todo: what else?
       ))

(defund include-book-form-listp (forms)
  (declare (xargs :guard t))
  (if (atom forms)
      (null forms)
    (and (include-book-formp (first forms))
         (include-book-form-listp (rest forms)))))

(local
 (defthm include-book-form-listp-forward-to-true-listp
   (implies (include-book-form-listp forms)
            (true-listp forms))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable include-book-form-listp)))))

(defthm include-book-form-listp-of-union-equal
  (implies (and (include-book-form-listp info1)
                (include-book-form-listp info2))
           (include-book-form-listp (union-equal info1 info2)))
  :hints (("Goal" :in-theory (enable include-book-form-listp union-equal))))

(defund include-book-infop (info)
  (declare (xargs :guard t))
  (or (eq :builtin info)
      (include-book-form-listp info)))

(local
 (defthm true-listp-when-include-book-infop
   (implies (include-book-infop info)
            (equal (true-listp info)
                   (not (equal :builtin info))))
   :hints (("Goal" :in-theory (enable include-book-infop)))))

(defund include-book-info-listp (infos)
  (declare (xargs :guard t))
  (if (atom infos)
      (null infos)
    (and (include-book-infop (first infos))
         (include-book-info-listp (rest infos)))))

(local
 (defthm include-book-info-listp-forward-to-true-listp
   (implies (include-book-info-listp infos)
            (true-listp infos))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable include-book-info-listp)))))

(defund book-mapp (book-map)
  (declare (xargs :guard t))
  (and (symbol-alistp book-map)
       (include-book-info-listp (strip-cdrs book-map))))

(local
 (defthm book-mapp-forward-to-alistp
   (implies (book-mapp book-map)
            (alistp book-map))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable book-mapp)))))

(defthm book-mapp-of-pairlis$
  (implies (and (symbol-listp keys)
                (include-book-info-listp vals))
           (book-mapp (pairlis$ keys vals)))
  :hints (("Goal" :in-theory (enable book-mapp include-book-info-listp))))

(local
 (defthm include-book-infop-of-lookup-equal
   (implies (book-mapp book-map)
            (include-book-infop (acl2::lookup-equal key book-map)))
   :hints (("Goal" :in-theory (enable book-mapp acl2::lookup-equal assoc-equal include-book-info-listp)))))

(local
 (defthm symbol-listp-of-strip-cars-when-book-mapp
   (implies (book-mapp book-map)
            (symbol-listp (strip-cars book-map)))
   :hints (("Goal" :in-theory (enable book-mapp)))))

;; todo: strengthen
(defund recommendationp (rec)
  (declare (xargs :guard t))
  (and (true-listp rec)
       (= 5 (len rec))
       (let ((name (nth 0 rec))
             (type (nth 1 rec))
             ;; (object (nth 2 rec))
             (confidence-percent (nth 3 rec))
             (book-map (nth 4 rec)))
         (and (stringp name)
              (rec-typep type)
              ;; object
              (confidence-percentp confidence-percent)
              (book-mapp book-map)))))

(local
 (defthm recommendationp-forward-to-true-listp
   (implies (recommendationp rec)
            (true-listp rec))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable recommendationp)))))

(local
 (defthm true-listp-when-recommendationp
   (implies (recommendationp rec)
            (true-listp rec))
   :hints (("Goal" :in-theory (enable recommendationp)))))

(local
 (defthm stringp-of-nth-0-when-recommendationp
   (implies (recommendationp rec)
            (stringp (nth 0 rec)))
   :hints (("Goal" :in-theory (enable recommendationp)))))

(local
 (defthm rec-typep-of-nth-1-when-recommendationp
   (implies (recommendationp rec)
            (rec-typep (nth 1 rec)))
   :hints (("Goal" :in-theory (enable recommendationp)))))

(local
 (defthm rationalp-of-nth-3-when-recommendationp
   (implies (recommendationp rec)
            (rationalp (nth 3 rec)))
   :hints (("Goal" :in-theory (enable recommendationp)))))

(local
 (defthm confidence-percentp-of-nth-3-when-recommendationp
   (implies (recommendationp rec)
            (confidence-percentp (nth 3 rec)))
   :hints (("Goal" :in-theory (enable recommendationp)))))

(local
 (defthm book-mapp-of-nth-4-when-recommendationp
   (implies (recommendationp rec)
            (book-mapp (nth 4 rec)))
   :hints (("Goal" :in-theory (enable recommendationp)))))

;; (local
;;  (defthm true-listp-of-nth-6-when-recommendationp
;;    (implies (recommendationp rec)
;;             (true-listp (nth 6 rec)))
;;    :hints (("Goal" :in-theory (enable recommendationp)))))

;; (local
;;  (defthm rec-sourcesp-of-nth-6-when-recommendationp
;;    (implies (recommendationp rec)
;;             (rec-sourcesp (nth 6 rec)))
;;    :hints (("Goal" :in-theory (enable recommendationp)))))

(defund make-rec (name type object confidence-percent book-map)
  (declare (xargs :guard (and (stringp name)
                              (rec-typep type)
                              ;; object
                              (confidence-percentp confidence-percent)
                              (book-mapp book-map))))
  (list name type object confidence-percent book-map))

(defthm recommendationp-of-make-rec
  (equal (recommendationp (make-rec name type object confidence-percent book-map))
         (and (stringp name)
              (rec-typep type)
              ;; object
              (confidence-percentp confidence-percent)
              (book-mapp book-map)))
  :hints (("Goal" :in-theory (enable make-rec recommendationp))))

(defun show-recommendation (rec)
  (declare (xargs :guard (recommendationp rec)))
  (let* ((name (nth 0 rec))
         (type (nth 1 rec))
         (object (nth 2 rec))
         (confidence-percent (nth 3 rec))
         ;; (book-map (car (nth 4 rec)))
         )
    (cw "~s0: Try ~x1 with ~x2 (conf: ~x3%).~%" name type object (floor confidence-percent 1))))

(defund recommendation-listp (recs)
  (declare (xargs :guard t))
  (if (atom recs)
      (null recs)
    (and (recommendationp (first recs))
         (recommendation-listp (rest recs)))))

(local
 (defthm recommendation-listp-forward-to-true-listp
   (implies (recommendation-listp recs)
            (true-listp recs))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable recommendation-listp)))))

(defthm recommendation-listp-of-remove-equal
  (implies (recommendation-listp recs)
           (recommendation-listp (remove-equal rec recs)))
  :hints (("Goal" :in-theory (enable recommendation-listp))))

(defthm recommendation-listp-of-revappend
  (implies (and (recommendation-listp recs1)
                (recommendation-listp recs2))
           (recommendation-listp (revappend recs1 recs2)))
  :hints (("Goal" :in-theory (enable recommendation-listp revappend))))

(defthm recommendation-listp-of-cdr
  (implies (recommendation-listp recs)
           (recommendation-listp (cdr recs)))
  :hints (("Goal" :in-theory (enable recommendation-listp))))

(defun show-recommendations-aux (recs)
  (declare (xargs :guard (recommendation-listp recs)
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp recs)
      nil
    (prog2$ (show-recommendation (first recs))
            (show-recommendations-aux (rest recs)))))

;; Returns state.
(defun show-recommendations (recs state)
  (declare (xargs :guard (recommendation-listp recs)
                  :stobjs state))
  (let ((state (acl2::widen-margins state)))
    (progn$ (show-recommendations-aux recs)
            (let ((state (acl2::unwiden-margins state)))
              state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rec-confidence> (rec1 rec2)
  (declare (xargs :guard (and (recommendationp rec1)
                              (recommendationp rec2))))
  (> (nth 3 rec1) (nth 3 rec2)))

(acl2::defmergesort merge-recs-by-confidence merge-sort-recs-by-confidence rec-confidence> recommendationp :extra-theorems nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: strengthen?
(defund successful-recommendationp (rec)
  (declare (xargs :guard t))
  (and (true-listp rec)
       (= 7 (len rec))
       (let ((name (nth 0 rec))
             (type (nth 1 rec))
             ;; (object (nth 2 rec))
             ;; this (possibly) gets populated when we try the rec:
             (pre-commands (nth 3 rec))
             ;; (theorem-body (nth 4 rec))
             ;; (theorem-hints (nth 5 rec))
             (theorem-otf-flg (nth 6 rec)))
         (and (stringp name)
              (rec-typep type)
              ;; object
              (pre-commandsp pre-commands)
              ;; theorem-body is an untranslated term
              ;; theorem-hints
              (booleanp theorem-otf-flg)))))

(defund successful-recommendationp-name (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 0 rec))

(defund successful-recommendationp-type (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 1 rec))

(defund successful-recommendationp-object (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :guard-hints (("Goal" :in-theory (enable successful-recommendationp)))))
  (nth 2 rec))

(local
 (defthm pre-commandsp-of-nth-3-when-successful-recommendationp
   (implies (successful-recommendationp rec)
            (pre-commandsp (nth 3 rec)))
   :hints (("Goal" :in-theory (enable successful-recommendationp)))))

(defund make-successful-rec (name type object pre-commands theorem-body theorem-hints theorem-otf-flg)
  (declare (xargs :guard (and (stringp name)
                              (rec-typep type)
                              ;; object
                              (pre-commandsp pre-commands)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg))))
  (list name type object pre-commands theorem-body theorem-hints theorem-otf-flg))

(defthm successful-recommendationp-of-make-successful-rec
  (equal (successful-recommendationp (make-successful-rec name type object pre-commands theorem-body theorem-hints theorem-otf-flg))
         (and (stringp name)
              (rec-typep type)
              ;; object
              (pre-commandsp pre-commands)
              ;; theorem-body
              ;; theorem-hints
              (booleanp theorem-otf-flg)))
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
  (let* (;; (type (nth 1 rec))
         ;; (object (nth 2 rec))
         (pre-commands (nth 3 rec)))
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
  (let* ( ;;(type (nth 1 rec))
         ;; (object (nth 2 rec))
         (pre-commands (nth 3 rec)))
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
  (let* (;; (name (nth 0 rec))
         (type (nth 1 rec))
         (object (nth 2 rec))
         (pre-commands (nth 3 rec))
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
           (name (nth 0 rec)))
      (progn$ (show-successful-recommendation rec)
              (cw " (~S0)~%" name)
              ;; todo: drop the sources:
              ;; (and (< 1 (len sources))
              ;;      (cw "~x0" sources))
              ;;(cw ": ")
              (show-successful-recommendations-aux (rest recs))))))

;; Returns state.
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

(defund round-to-hundredths (x)
  (declare (xargs :guard (rationalp x)))
  (/ (floor (* x 100) 1)
     100))

(defthm confidence-percentp-of-round-to-hundredths
  (implies (confidence-percentp x)
           (confidence-percentp (round-to-hundredths x)))
  :hints (("Goal" :in-theory (enable confidence-percentp round-to-hundredths))))

(local
 (defthm confidence-percentp-of-*-of-100
   (implies (and (<= 0 x)
                 (<= x 1)
                 (rationalp x))
            (confidence-percentp (* 100 x)))
   :hints (("Goal" :in-theory (enable confidence-percentp)))))

;; Returns (mv erp parsed-recommendation state) where parsed-recommendation may be :none.
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
          (if (stringp erp)
              (cw "WARNING: When parsing book map: ~s0.~%" erp)
            (cw "WARNING: When parsing book map: ~x0.~%" erp))
          (mv nil ; supressing this error for now
              :none state))
         ((when (or (not (rationalp confidence))
                    (< confidence 0)
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
         ((mv erp parsed-object state) (acl2::read-string-as-single-item object "ACL2" state))
         ((when erp)
          (er hard? 'parse-recommendation "Error (~x0) parsing recommended action: ~x1." erp object)
          (mv :parse-error nil state))
         (name (concatenate 'string (model-to-nice-string source) (acl2::nat-to-string rec-num)))
         )
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

;; TODO: Think about THM vs DEFTHM
;; (defun make-thm-to-attempt (body hints otf-flg)
;;   `(thm ,body
;;         ,@(and hints `(:hints ,hints))
;;         ,@(and otf-flg `(:otf-flg .otf-flg))))

;; Returns (mv provedp state).  Does not propagate any errors back.
(defund prove$-no-error (ctx term hints otf-flg step-limit state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (erp provedp state)
    ;; TODO: Drop the :time-limit once :step-limit can interrupt subsumption:
    (acl2::prove$ term :hints hints :otf-flg otf-flg :step-limit step-limit :time-limit 5)
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
    (acl2::prove$+ term :hints hints :otf-flg otf-flg :step-limit step-limit :time-limit 5 :print nil)
    (if erp
        (prog2$ (cw "Syntax error in prove$ call (made by ~x0).~%" ctx)
                (mv nil nil state))
      (mv provedp failure-info state))))

;; See :doc lemma-instance
(defund symbol-that-can-be-usedp (sym wrld)
  (declare (xargs :guard (and (symbolp sym)
                              (plist-worldp wrld))))
  (or (acl2::defined-functionp sym wrld)
      (acl2::defthm-or-defaxiom-symbolp sym wrld)))

;; Calls prove$ on FORMULA after submitting INCLUDE-BOOK-FORM, which is undone after the prove$.
;; Returns (mv erp provedp state).  If NAME-TO-CHECK is non-nil, we require it to be something
;; that can be enabled/disabled after including the book, or else we don't call prove$.
(defun prove$-with-include-book (ctx
                                 formula
                                 include-book-form
                                 name-to-check ; we ensure this exists after the include-book (nil means nothing to check)
                                 check-kind ; :enable or :use
                                 book-to-avoid-absolute-path ; immediately fail if the include-book causes this book to be brought in (nil means nothing to check)
                                 ;; args to prove$:
                                 hints otf-flg step-limit
                                 state)
  (declare (xargs :stobjs state
                  :guard (and (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              ;; todo: add to this
                              )
                  :mode :program))
  (revert-world ;; ensures the include-book gets undone
   (b* (        ;; Try to include the recommended book:
        ((mv erp state) (acl2::submit-event-helper include-book-form nil nil state))
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
        ;; Check that we didn't bring in the book-to-avoid:
        ((when (member-equal book-to-avoid-absolute-path (acl2::included-books-in-world (w state))))
         (cw "NOTE: Avoiding include-book, ~x0, that would bring in the book-to-avoid.~%" include-book-form)
         (mv nil nil state))
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
                                      book-to-avoid-absolute-path
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
                                    book-to-avoid-absolute-path
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
                                     book-to-avoid-absolute-path
                                     ;; args to prove$:
                                     hints otf-flg step-limit
                                     state))))

(defun cw-failure-message (snippet failure-info)
  (if (eq failure-info :step-limit-reached) ; update this is other kinds of failure-info become supported
      (cw "fail (~s0: step limit reached)~%" snippet)
    (cw "fail (~s0)~%" snippet)))

(defun cw-success-message (rec)
  (declare (xargs :guard (successful-recommendationp rec)
                  :mode :program))
  (progn$ (cw "SUCCESS: ")
          (show-successful-recommendation rec)
          (cw "~%")))

;; Returns (mv erp successp state).
;; TODO: Skip if library already included
;; TODO: Skip later add-library recs if they are included by this one (though I suppose they might work only without the rest of what we get here).
;; TODO: Try any upcoming enable or use-lemma recs that (may) need this library:
(defun try-add-library (include-book-form book-to-avoid-absolute-path theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :stobjs state
                  :guard (and (consp include-book-form)
                              (eq 'include-book (car include-book-form))
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :mode :program)
           (ignore theorem-name) ; todo: use to make a suggestion
           )
  (b* (;; TODO: Give up here if the include-book-form corresponds to the book-to-avoid-absolute-path.
       ((when (eq 'acl2::other include-book-form)) ; todo: can this happen, or could it be (include-book other)?
        (and (acl2::print-level-at-least-tp print) (cw "skip (can't include catch-all library ~x0)~%" include-book-form))
        (mv nil nil state))
       ((when (not (consp include-book-form)))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ill-formed library recommendation: ~x0)~%" include-book-form))
        (mv nil nil state))
       ((mv erp provedp state)
        (prove$-with-include-book 'try-add-library theorem-body include-book-form nil nil book-to-avoid-absolute-path theorem-hints theorem-otf-flg step-limit state))
       ((when erp) (mv erp nil state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-library
                                 include-book-form
                                 (list include-book-form)
                                 theorem-body theorem-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print) (if provedp (cw-success-message rec) (cw "fail (library didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

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

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Don't try a hyp that is already present, or contradicts ones already present
(defun try-add-hyp (hyp theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and (pseudo-termp hyp)
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hint
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* ((translatablep (acl2::translatable-termp hyp (w state)))
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
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (acl2::submit-event-helper
       ;;                  ;; TODO: Add the hyp more nicely:
       ;;                  (make-thm-to-attempt `(implies ,hyp ,theorem-body) theorem-hints theorem-otf-flg)
       ;;                  t nil state))
       (new-theorem-body `(implies ,hyp ,theorem-body)) ; todo: merge hyp in better
       ((mv provedp failure-info state) (prove$-no-error-with-failure-info
                                         'try-add-hyp
                                         new-theorem-body
                                         theorem-hints
                                         theorem-otf-flg
                                         step-limit
                                         state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-hyp
                                 hyp
                                 nil ; no pre-commands ; todo update this once we use the book map
                                 new-theorem-body
                                 theorem-hints
                                 theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp
                   (cw-success-message rec)
                 (let ((translated-hyp (acl2::translate-term hyp 'try-add-hyp (w state))))
                   (cw-failure-message (fms-to-string-one-line "adding hyp ~x0 didn't help" (acons #\0 translated-hyp nil)) failure-info))))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Avoid theory-invariant violations from enabling.
(defun try-add-enable-hint (rule     ; the rule to try enabling
                            book-map ; info on where the rule may be found
                            book-to-avoid-absolute-path
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            step-limit
                            rec
                            print
                            state)
  (declare (xargs :guard (and (symbolp rule)
                              (book-mapp book-map)
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :stobjs state :mode :program))
  (b* (((when (eq rule 'acl2::other)) ;; "Other" is a catch-all for low-frequency classes
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling catch-all: ~x0)~%" rule))
        (mv nil nil state))
       ((when (keywordp rule))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling unsupported item: ~x0)~%" rule)) ; this can come from a ruleset of (:rules-of-class :type-prescription :here)
        (mv nil nil state))
       ((when (not (symbolp rule)))
        (and (acl2::print-level-at-least-tp print) (cw "skip (Unsupported item: ~x0)~%" rule)) ; todo: handle runes like (:TYPE-PRESCRIPTION A14 . 1)
        (mv nil nil state))
       (wrld (w state))
       (rule (handle-macro-alias rule wrld)) ; TODO: Handle the case of a macro-alias we don't know about
       )
    (if (function-symbolp rule wrld)
        ;; It's a function in the current world:
        (b* ((fn rule)
             ((when (not (acl2::logicp fn wrld)))
              (and (acl2::print-level-at-least-tp print) (cw "skip (Can't enable ~x0. Not in :logic mode.)~%" fn))
              (mv nil nil state))
             ((when (not (and
                          ;; (acl2::defined-functionp fn wrld) ;todo
                          )))
              (and (acl2::print-level-at-least-tp print) (cw "skip (Can't enable ~x0. No body.)~%" fn))
              (mv nil nil state))
             ;; TODO: Consider whether to enable, say the :type-prescription rule
             (rune `(:definition ,fn))
             ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
             ((when (acl2::enabled-runep rune (acl2::ens-maybe-brr state) (w state)))
              (and (acl2::print-level-at-least-tp print) (cw "skip (~x0 is already enabled.)~%" fn))
              (mv nil nil state))
             ;; FN exists and just needs to be enabled:
             (new-hints (acl2::enable-runes-in-hints theorem-hints (list fn))) ;; todo: ensure this is nice
             ((mv provedp state)
              (prove$-no-error 'try-add-enable-hint
                               theorem-body
                               new-hints
                               theorem-otf-flg
                               step-limit
                               state))
             ((when (not provedp))
              (and (acl2::print-level-at-least-tp print) (cw "fail (enabling function ~x0 didn't help)~%" fn))
              (mv nil nil state))
             ;; We change the rec type to ensure duplicates get removed:
             (rec (make-successful-rec (nth 0 rec)
                                       :add-enable-hint
                                       (nth 2 rec)
                                       nil
                                       theorem-body new-hints theorem-otf-flg))
             (- (and (acl2::print-level-at-least-tp print)
                     (cw-success-message rec))))
          (mv nil rec state))
      (if (not (eq :no-body (getpropc rule 'acl2::theorem :no-body wrld))) ;todo: how to just check if the property is set?
          ;; It's a theorem in the current world:
          (b* ( ;; TODO: Consider whether to enable, say the :type-prescription rule
               (rune `(:rewrite ,rule))
               ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
               ((when (acl2::enabled-runep rune (acl2::ens-maybe-brr state) (w state)))
                (and (acl2::print-level-at-least-tp print) (cw "skip (~x0 is already enabled.)~%" rule))
                (mv nil nil state))
               ;; RULE exists and just needs to be enabled:
               (new-hints (acl2::enable-runes-in-hints theorem-hints (list rule))) ;; todo: ensure this is nice
               ((mv provedp state)
                (prove$-no-error 'try-add-enable-hint
                                 theorem-body
                                 new-hints
                                 theorem-otf-flg
                                 step-limit
                                 state))
               ((when (not provedp))
                (and (acl2::print-level-at-least-tp print) (cw "fail (enabling rule ~x0 didn't help)~%" rule))
                (mv nil nil state))
               ;; We change the rec type to ensure duplicates get removed:
               (rec (make-successful-rec (nth 0 rec)
                                         :add-enable-hint
                                         (nth 2 rec)
                                         nil
                                         theorem-body new-hints theorem-otf-flg))
               (- (and (acl2::print-level-at-least-tp print)
                       (cw-success-message rec))))
            (mv nil rec state))
        ;; RULE is not currently known, so try to find where it is defined:
        (b* ((book-map-keys (strip-cars book-map))
             ((when (not (equal book-map-keys (list rule))))
              (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil rule)
              (mv :bad-book-map nil state))
             (include-book-info (acl2::lookup-eq rule book-map))
             ((when (eq :builtin include-book-info))
              (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" rule)
              (mv :bad-book-info nil state))
             ;; todo: check for empty books-to-try (here and elsewhere?)
             (include-books-to-try include-book-info) ; rename for clarity
             (num-include-books-to-try-orig (len include-books-to-try))
             ;; (- (and (< 1 num-include-books-to-try)
             ;;         (cw "NOTE: There are ~x0 books that might contain ~x1: ~X23~%" num-include-books-to-try rule include-books-to-try nil)))
             (include-books-to-try (if (< 3 num-include-books-to-try-orig)
                                       (take 3 include-books-to-try)
                                     include-books-to-try))
             ;; todo: ensure this is nice:
             (new-hints (acl2::enable-runes-in-hints theorem-hints (list rule))))
          ;; Not built-in, so we'll have to try finding the rule in a book:
          ;; TODO: Would be nice to not bother if it is a definition that we don't have.
          (b* (;; TODO: If, after including the book, the name to enable is a function, enabling it seems unlikely to help given that it didn't appear in the original proof.
               ;; TODO: Try to get a good variety of books here, if there are too many to try them all:
               ((mv erp successful-include-book-form-or-nil state)
                (try-prove$-with-include-books 'try-add-enable-hint theorem-body include-books-to-try rule :enable book-to-avoid-absolute-path new-hints theorem-otf-flg *step-limit* state))
               ((when erp) (mv erp nil state))
               ;; todo: clarify whether we even found an include-book that works
               ((when (not successful-include-book-form-or-nil))
                (and (acl2::print-level-at-least-tp print)
                     (if (< 3 num-include-books-to-try-orig)
                         ;; todo: try more if we didn't find it?:
                         (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" (len include-books-to-try) num-include-books-to-try-orig rule)
                       (cw "fail (enabling ~x0 didn't help)~%" rule)))
                (mv nil nil state))
               (successful-include-book-form successful-include-book-form-or-nil) ; rename for clarity
               ;; We proved it with an include-book and an enable hint.  Now
               ;; try again but without the enable hint (maybe the include-book is enough):
               ((mv erp provedp-with-no-hint state)
                (prove$-with-include-book 'try-add-enable-hint ; todo: the redoes the include-book
                                          theorem-body
                                          successful-include-book-form
                                          nil ; name-to-check (no need to check this again)
                                          :enable
                                          book-to-avoid-absolute-path
                                          ;; args to prove$:
                                          theorem-hints ; original hints, not new-hints
                                          theorem-otf-flg
                                          step-limit ; or base this on how many steps were taken when it succeeded
                                          state))
               ((when erp) (mv erp nil state))
               ;; todo: we could even try to see if a smaller library would work
               (rec (if provedp-with-no-hint
                        ;; Turn the rec into an :add-library, because the library is what mattered:
                        (make-successful-rec (nth 0 rec) ;name (ok to keep the same name, i guess)
                                             :add-library ;; Change the rec to :add-library since the hint didn't matter!
                                             successful-include-book-form
                                             (list successful-include-book-form) ; pre-commands
                                             theorem-body
                                             theorem-hints ; original hints, no new enable
                                             theorem-otf-flg)
                      (make-successful-rec (nth 0 rec) ;name (ok to keep the same name, i guess)
                                           :add-enable-hint
                                           (nth 2 rec)
                                           (list successful-include-book-form) ; pre-commands
                                           theorem-body
                                           new-hints
                                           theorem-otf-flg)))
               (- (and (acl2::print-level-at-least-tp print)
                       (cw-success-message rec))))
            (mv nil
                rec
                state)))))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-disable-hint (rule theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and (symbolp rule)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
                              (recommendationp rec)
                              ;; print
                              )
                  :stobjs state
                  :mode :program))
  (b* (((when (eq rule 'acl2::other)) ;; "Other" is a catch-all for low-frequency classes
        (and (acl2::print-level-at-least-tp print) (cw "skip (Not disabling catch-all: ~x0)~%" rule))
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
       (new-hints (acl2::disable-runes-in-hints theorem-hints (list rule)))
       ((mv provedp state) (prove$-no-error 'try-add-disable-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-disable-hint
                                 rule
                                 nil
                                 theorem-body new-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (disable didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: Do we need to guess a substitution for the :use hint?  Then change the rec before returning...
(defun try-add-use-hint (item book-map book-to-avoid-absolute-path theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (book-mapp book-map)
                          (or (null book-to-avoid-absolute-path)
                              (stringp book-to-avoid-absolute-path))
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq item 'acl2::other))
        (and (acl2::print-level-at-least-tp print) (cw "skip (skipping catch-all: ~x0)~%" item))
        (mv nil nil state))
       ((when (not (symbolp item))) ; for now
        (and (acl2::print-level-at-least-tp print) (cw "skip (unexpected object for :add-use-hint: ~x0)~%" item)) ; todo: add support for other lemma-instances
        (mv nil nil state)))
    (if (symbol-that-can-be-usedp item (w state)) ; todo: what if it's defined but can't be :used?
        (b* (                                     ;; todo: ensure this is nice:
             ;; todo: also disable the item, if appropriate
             (new-hints (cons `("Goal" :use ,item) theorem-hints))
             ((mv provedp state) (prove$-no-error 'try-add-use-hint
                                                  theorem-body
                                                  new-hints
                                                  theorem-otf-flg
                                                  step-limit
                                                  state))
             (rec (make-successful-rec (nth 0 rec)
                                       :add-use-hint
                                       item
                                       nil
                                       theorem-body new-hints theorem-otf-flg))
             (- (and (acl2::print-level-at-least-tp print)
                     (if provedp (cw-success-message rec) (cw "fail (:use ~x0 didn't help)~%" item)))))
          (mv nil (if provedp rec nil) state))
      ;; ITEM is not in the current world, so try to find where it is defined:
      (b* ((book-map-keys (strip-cars book-map))
           ((when (not (equal book-map-keys (list item))))
            (cw "error (Bad book map, ~X01, for ~x2).~%" book-map nil item)
            (mv :bad-book-map nil state))
           (include-book-info (acl2::lookup-eq item book-map))
           ((when (eq :builtin include-book-info))
            (cw "error (~x0 does not seem to be built-in, contrary to the book-map).~%" item)
            (mv :bad-book-info nil state))
           (include-books-to-try include-book-info) ; rename for clarity
           ;; TODO: Filter out include-books that are known to clash with this tool?
           (num-include-books-to-try-orig (len include-books-to-try))
           ;; (- (and (< 1 num-include-books-to-try)
           ;;         (cw "NOTE: There are ~x0 books that might contain ~x1: ~X23~%" num-include-books-to-try item include-books-to-try nil)))
           (include-books-to-try (if (< 3 num-include-books-to-try-orig)
                                     (take 3 include-books-to-try)
                                   include-books-to-try))
           ;; todo: ensure this is nice:
           (new-hints ;; todo: ensure this is nice:
            ;; todo: also disable the item, if appropriate
            (cons `("Goal" :use ,item) theorem-hints))
           ;; TODO: Would be nice to not bother if it is a definition that we don't have.
           ;; TODO: For each of these, if it works, maybe just try the include-book without the enable:
           ;; TODO: If, after including the book, the name to enable is a function, enabling it seems unlikely to help given that it didn't appear in the original proof.
           ((mv erp successful-include-book-form-or-nil state)
            (try-prove$-with-include-books 'try-add-use-hint theorem-body include-books-to-try item :use book-to-avoid-absolute-path new-hints theorem-otf-flg *step-limit* state))
           ((when erp) (mv erp nil state))
           ((when (not successful-include-book-form-or-nil))
            (and (acl2::print-level-at-least-tp print)
                 (if (< 3 num-include-books-to-try-orig)
                     ;; todo: try more if we didn't find it?:
                     (cw "fail (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" (len include-books-to-try) num-include-books-to-try-orig item)
                   (cw "fail (using ~x0 didn't help)~%" item)))
            (mv nil nil state))
           (successful-include-book-form successful-include-book-form-or-nil) ; rename for clarity
           ;; We proved it with an include-book and a :use hint.  Now
           ;; try again but without the :use hint (maybe the include-book is enough):
           ((mv erp provedp-with-no-hint state)
            (prove$-with-include-book 'try-add-use-hint ; todo: the redoes the include-book
                                      theorem-body
                                      successful-include-book-form
                                      nil ; name-to-check (no need to check this again)
                                      :use
                                      book-to-avoid-absolute-path
                                      ;; args to prove$:
                                      theorem-hints ; original hints, not new-hints
                                      theorem-otf-flg
                                      step-limit ; or base this on how many steps were taken when it succeeded
                                      state))
           ((when erp) (mv erp nil state))
           ;; todo: we could even try to see if a smaller library would work
           (rec (if provedp-with-no-hint
                    (make-successful-rec (nth 0 rec) ;name
                                         :add-library ;; Change the rec to :add-library since the hint didn't matter!
                                         successful-include-book-form
                                         (list successful-include-book-form) ; pre-commands
                                         theorem-body
                                         theorem-hints
                                         theorem-otf-flg)
                  (make-successful-rec (nth 0 rec) ;name
                                       :add-use-hint
                                       item
                                       (list successful-include-book-form) ; pre-commands
                                       theorem-body
                                       new-hints
                                       theorem-otf-flg)))
           (- (and (acl2::print-level-at-least-tp print)
                   (cw-success-message rec))))
        (mv nil
            rec
            state)))))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-expand-hint (item ; the thing to expand
                            theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'acl2::other item))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring recommendation to expand \"Other\")~%"))
        (mv nil nil state))
       ((when (symbolp item)) ; todo: eventually remove this case
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring illegal recommendation to expand a symbol)~%"))
        (mv nil nil state))
       ;; todo: can it be a single term?:
       ((when (not (acl2::translatable-term-listp item (w state))))
        (and (acl2::print-level-at-least-tp print) (cw "fail (term not all translatable: ~x0)~%" item)) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; todo: ensure this is nice:
       (new-hints (cons `("Goal" :expand ,item) theorem-hints))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (acl2::submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :expand ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-no-error 'try-add-expand-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-expand-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:expand hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-by-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'acl2::other item))
        (and (acl2::print-level-at-least-tp print) (cw "fail (ignoring :by hint with catch-all \"Other\")~%"))
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
       (new-hints (cons `("Goal" :by ,item) theorem-hints))
       ((mv provedp failure-info state)
        (prove$-no-error-with-failure-info 'try-add-by-hint
                                           theorem-body
                                           new-hints
                                           theorem-otf-flg
                                           step-limit
                                           state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-by-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw-failure-message ":by hint didn't help" failure-info)))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-cases-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state
                  :mode :program)
           (ignore theorem-name))
  (b* (((when (not (acl2::translatable-term-listp item (w state))))
        (and (acl2::print-level-at-least-tp print) (cw "fail (terms not all translatable: ~x0)~%" item)) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; todo: ensure this is nice:
       (new-hints (cons `("Goal" :cases ,item) theorem-hints))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (acl2::submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :cases ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-no-error 'try-add-cases-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-cases-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:cases hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-nonlinearp-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (not (booleanp item)))
        (and print (cw "WARNING: Invalid value for :nonlinearp: ~x0.~%" item))
        (mv nil nil state) ; or we could return erp=t here
        )
       ;; todo: ensure this is nice:
       (new-hints (cons `("Goal" :nonlinearp ,item) theorem-hints))
       ((mv provedp state) (prove$-no-error 'try-add-nonlinearp-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-nonlinearp-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:nonlinearp hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-add-do-not-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state :mode :program)
           (ignore theorem-name))
  (b* ( ;; Can't easily check the :do-not hint syntactically...
       ;; todo: ensure this is nice:
       (new-hints (cons `("Goal" :do-not ,item) theorem-hints))
       ((mv provedp state) (prove$-no-error 'try-add-do-not-hint
                                            theorem-body
                                            new-hints
                                            theorem-otf-flg
                                            step-limit
                                            state))
       (rec (make-successful-rec (nth 0 rec)
                                 :add-do-not-hint
                                 item
                                 nil
                                 theorem-body new-hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw "fail (:do-not hint didn't help)~%")))))
    (mv nil (if provedp rec nil) state)))

;; Returns (mv erp maybe-successful-rec state).
;; TODO: We need more than a symbol
(defun try-add-induct-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and ;; (symbolp item)
                          (symbolp theorem-name)
                          ;; theorem-body is an untranslated term
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (or (eq nil step-limit)
                              (natp step-limit))
                          (recommendationp rec)
                          ;; print
                          )
                  :stobjs state :mode :program)
           (ignore theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec))
  (if (symbolp item)
      ;; TODO: Try looking for calls of the given symbol in the theorem (maybe just with arguments that are vars?):
      (prog2$ (and (acl2::print-level-at-least-tp print) (cw "skip (need arguments of ~x0 to create :induct hint)~%" item))
              (mv nil nil state))
    ;; TODO: Flesh this out when ready:
    (mv :unsupported-induct-hint nil state)))

;; Returns (mv erp maybe-successful-rec state).
(defun try-exact-hints (hints theorem-body theorem-otf-flg step-limit rec print state)
  (declare (xargs :guard (and (true-listp hints)
                              ;; theorem-body is an untranslated term
                              (booleanp theorem-otf-flg)
                              (or (eq nil step-limit)
                                  (natp step-limit))
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
                                           step-limit
                                           state))
       (rec (make-successful-rec (nth 0 rec)
                                 :exact-hints
                                 hints
                                 nil
                                 theorem-body hints theorem-otf-flg))
       (- (and (acl2::print-level-at-least-tp print)
               (if provedp (cw-success-message rec) (cw-failure-message ":hints didn't help" failure-info)))))
    (mv nil (if provedp rec nil) state)))

;; Tries to find rec(s) which, together with the supplied THEOREM-HINTS, suffices to prove the theorem.
;; Tries each of the RECS in turn until MAX-WINS successful ones are found or there are none left.
;; Returns (mv erp successful-recs state)
(defun try-recommendations (recs
                            book-to-avoid-absolute-path
                            theorem-name ; may be :thm
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            step-limit
                            max-wins
                            print
                            successful-recs
                            state)
  (declare (xargs :guard (and (recommendation-listp recs)
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (or (null max-wins)
                                  (natp max-wins))
                              (acl2::print-levelp print)
                              (true-listp successful-recs))
                  :mode :program
                  :stobjs state))
  (if (or (endp recs)
          (and max-wins
               (<= max-wins (len successful-recs))))
      (mv nil (reverse successful-recs) state)
    (b* ((rec (first recs))
         (name (nth 0 rec))
         (type (nth 1 rec))
         (object (nth 2 rec))
         ;; (confidence-percent (nth 3 rec))
         (book-map (nth 4 rec))
         (- (and (acl2::print-level-at-least-tp print) (cw "~s0: " name)))
         ((mv & ; erp ; for now, we ignore errors and just continue
              maybe-successful-rec ; may be fleshed out (pre-commands, hints, etc.)
              state)
          (case type
            ;; TODO: Pass the book-map and the book-to-avoid-absolute-path to all who can use it:
            (:add-by-hint (try-add-by-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-cases-hint (try-add-cases-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-disable-hint (try-add-disable-hint object theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-do-not-hint (try-add-do-not-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-enable-hint (try-add-enable-hint object book-map book-to-avoid-absolute-path theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-expand-hint (try-add-expand-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-hyp (try-add-hyp object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-induct-hint (try-add-induct-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-library (try-add-library object book-to-avoid-absolute-path theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-nonlinearp-hint (try-add-nonlinearp-hint object theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            (:add-use-hint (try-add-use-hint object book-map book-to-avoid-absolute-path theorem-name theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            ;; same as for try-add-enable-hint above:
            (:use-lemma (try-add-enable-hint object book-map book-to-avoid-absolute-path theorem-body theorem-hints theorem-otf-flg step-limit rec print state))
            ;; Hints not from ML:
            (:exact-hints (try-exact-hints object theorem-body theorem-otf-flg step-limit rec print state))
            (t (prog2$ (cw "WARNING: UNHANDLED rec type ~x0.~%" type)
                       (mv t nil state))))))
      (try-recommendations (rest recs)
                           book-to-avoid-absolute-path
                           theorem-name theorem-body theorem-hints theorem-otf-flg step-limit max-wins print
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
    (cons (make-rec (concatenate 'string "enable" (acl2::nat-to-string num))
                    :add-enable-hint
                    (first names) ; the name to enable
                    0             ; confidence percentage (TODO: allow unknown)
                    nil ; book map ; todo: indicate that the name must be present?
                    )
          (make-enable-recs-aux (rest names) (+ 1 num)))))

(local
 (defthm recommendation-listp-of-make-enable-recs-aux
   (implies (symbol-listp names)
            (recommendation-listp (make-enable-recs-aux names num)))
   :hints (("Goal" :in-theory (enable recommendation-listp)))))

;; TODO: Don't even make recs for things that are enabled?  Well, we handle that elsewhere.
;; TODO: Put in macro-aliases, like append, when possible.  What if there are multiple macro-aliases for a function?  Prefer ones that appear in the untranslated formula?
;; Returns a list of recs, which should contain no duplicates.
(defun make-enable-recs (formula wrld)
  (declare (xargs :guard (and ;; formula is an untranslated term
                              (plist-worldp wrld))
                  :mode :program ; because of acl2::translate-term
                  ))
  (let* ((translated-formula (acl2::translate-term formula 'make-enable-recs wrld))
         (fns-to-try-enabling (set-difference-eq (acl2::defined-fns-in-term translated-formula wrld)
                                                 ;; Don't bother wasting time with trying to enable implies
                                                 ;; (I suppose we could try it if implies is disabled):
                                                 '(implies))))
    (make-enable-recs-aux fns-to-try-enabling 1)))

;; (local
;;  (defthm recommendation-listp-of-make-enable-recs
;;    (implies (pseudo-termp formula)
;;             (recommendation-listp (make-enable-recs formula wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; not looking at anything but the type and object
;; (defun rec-presentp (type object recs)
;;   (declare (xargs :guard (and (rec-typep type)
;;                               ;; object
;;                               (recommendation-listp recs))
;;                   :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
;;   (if (endp recs)
;;       nil
;;     (let ((rec (first recs)))
;;       (if (and (eq type (nth 1 rec))
;;                (equal object (nth 2 rec)))
;;           t
;;         (rec-presentp type object (rest recs))))))

(mutual-recursion
 ;; Extends ACC with hint-lists from the EVENT.
 (defun hint-lists-from-history-event (event acc)
   (declare (xargs :guard (and ;; event
                           (true-listp acc)
                           )
                   :verify-guards nil ; todo
                   ))
   (if (not (consp event))
       (er hard? 'hint-lists-from-history-event "Unexpected command (not a cons!): ~x0." event)
     (if (eq 'local (acl2::ffn-symb event)) ; (local e1)
         (hint-lists-from-history-event (acl2::farg1 event) acc)
       (if (eq 'encapsulate (acl2::ffn-symb event)) ; (encapsulate <sigs> e1 e2 ...)
           (hint-lists-from-history-events (rest (acl2::fargs event)) acc)
         (if (eq 'progn (acl2::ffn-symb event)) ; (progn e1 e2 ...)
             (hint-lists-from-history-events (acl2::fargs event) acc)
           (if ;; todo: what else can we harvest hints from?
               (not (member-eq (acl2::ffn-symb event) '(defthm defthmd)))
               acc
             (let ((res (assoc-keyword :hints (rest (rest (acl2::fargs event))))))
               (if (not res)
                   acc
                 (let ((hints (cadr res)))
                   (if (member-equal hints acc) ; todo: also look for equivalent recs?
                       acc
                     (cons hints acc)))))))))))

 ;; Extends ACC with hint-lists from the EVENTS.  Hint lists from earlier EVENTS end up deeper in the result,
 ;; which seems good because more recent events are likely to be more relevant (todo: but what about dups).
 (defun hint-lists-from-history-events (events acc)
   (declare (xargs :guard (and (true-listp events)
                               (true-listp acc))))
   (if (endp events)
       acc
     (hint-lists-from-history-events (rest events)
                                     (hint-lists-from-history-event (first events) acc)))))

(defun make-exact-hint-recs (hint-lists base-name num acc)
  (declare (xargs :guard (and (true-listp hint-lists)
                              (stringp base-name)
                              (posp num)
                              (true-listp acc))))
  (if (endp hint-lists)
      (reverse acc)
    (make-exact-hint-recs (rest hint-lists)
                          base-name
                          (+ 1 num)
                          (cons (make-rec (concatenate 'string base-name (acl2::nat-to-string num))
                                          :exact-hints ; new kind of rec, to replace all hints (todo: if the rec is expressible as something simpler, use that)
                                          (first hint-lists)
                                          0 ; confidence percent (TODO: What should we put in here?)
                                          nil ; no book-map (TODO: What about for things inside encapsulates?)
                                          )
                                acc))))

;; Extracts hints from events in the command history.  In the result, hints for more recent events come first and have higher numbers.
;; The result should contain no exact duplicates, but the recs (which are all of type :exact-hints) might effectively duplicate other recommendations.
(defund make-recs-from-history-events (events)
  (make-exact-hint-recs (hint-lists-from-history-events events nil) "history" 1 nil))

;; Returns (mv erp val state).
;; TODO: Try to merge these in with the existing theorem-hints.  Or rely on try-add-enable-hint to do that?  But these are :exact-hints.
(defun make-recs-from-history (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* (((mv erp events state) (acl2::get-command-sequence-fn 1 :max state)) ; todo: how to get events, not commands (e.g., get what make-events expanded to)?
       ((when erp) (mv erp nil state)))
    (mv nil (make-recs-from-history-events events) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; from Matt K:
(defun clausify-term (term wrld)
  (declare (xargs :mode :program))
  (let* ((term (acl2::expand-some-non-rec-fns '(implies) term wrld))
         (term (remove-guard-holders term wrld)))
    (acl2::clausify term nil t (acl2::sr-limit wrld))))

;; compares the type and object fields
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

;; Sends an HTTP POST request containing the POST-DATA to the server at
;; SERVER-URL.  Parses the response as JSON.  Returns (mv erp
;; parsed-json-response state).
(defund post-and-parse-response-as-json (server-url post-data debug state)
  (declare (xargs :guard (and (stringp server-url)
                              (acl2::string-string-alistp post-data)
                              (booleanp debug))
                  :stobjs state))
  (b* ((- (and debug (cw "POST data to be sent: ~X01.~%" post-data nil)))
       ((mv erp post-response state)
        (htclient::post server-url post-data state))
       ((when erp) (mv erp nil state))
       (- (and debug (cw "Raw POST response: ~X01~%" post-response nil)))
       ;; Parse the JSON:
       ((mv erp parsed-json-response) (acl2::parse-string-as-json post-response))
       ((when erp)
        (cw "Error parsing JSON response from ~x0.~%" server-url)
        (mv erp nil state))
       (- (and debug (cw "Parsed POST response: ~X01~%" parsed-json-response nil))))
    (mv nil parsed-json-response state)))

(defund same-recp (rec1 rec2)
  (declare (xargs :guard (and (recommendationp rec1)
                              (recommendationp rec2))))
  (and (equal (nth 1 rec1) (nth 1 rec2))
       (equal (nth 2 rec1) (nth 2 rec2))))

;; Returns a member of RECS that is equivalent to REC, or nil.
(defund find-equivalent-rec (rec recs)
  (declare (xargs :guard (and (recommendationp rec)
                              (recommendation-listp recs))
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp recs)
      nil
    (let ((this-rec (first recs)))
      (if (same-recp rec this-rec)
          this-rec
        (find-equivalent-rec rec (rest recs))))))

(defthm recommendationp-of-find-equivalent-rec
  (implies (and (find-equivalent-rec rec recs)
                (recommendation-listp recs))
           (recommendationp (find-equivalent-rec rec recs)))
  :hints (("Goal" :in-theory (enable find-equivalent-rec recommendation-listp))))

;; for now, if one is :builtin, we just take the other (but should that ever happen?)
(defund combine-include-book-infos (info1 info2)
  (declare (xargs :guard (and (include-book-infop info1)
                              (include-book-infop info2))))
  (if (eq :builtin info1)
      info2
    (if (eq :builtin info2)
        info1
      (union-equal info1 info2))))

(local
 (defthm include-book-infop-of-combine-include-book-infos
   (implies (and (include-book-infop info1)
                 (include-book-infop info2))
            (include-book-infop (combine-include-book-infos info1 info2)))
   :hints (("Goal" :in-theory (enable include-book-infop
                                      combine-include-book-infos)))))

(defund combine-book-maps-aux (keys map1 map2 acc)
  (declare (xargs :guard (and (symbol-listp keys)
                              (book-mapp map1)
                              (book-mapp map2)
                              (alistp acc))))
  (if (endp keys)
      acc
    (let* ((key (first keys))
           (info1 (acl2::lookup-eq key map1))
           (info2 (acl2::lookup-eq key map2))
           (val (if (not info1)
                    info2
                  (if (not info2)
                      info1
                    (combine-include-book-infos info1 info2)))))
      (combine-book-maps-aux (rest keys) map1 map2
                             (acons key
                                    val
                                    acc)))))

(local
 (defthm book-mapp-of-combine-book-maps-aux
   (implies (and (symbol-listp keys)
                 (book-mapp map1)
                 (book-mapp map2)
                 (book-mapp acc))
            (book-mapp (combine-book-maps-aux keys map1 map2 acc)))
   :hints (("Goal" :in-theory (enable combine-book-maps-aux book-mapp include-book-info-listp
                                      ;include-book-infop
                                      )))))

(defund combine-book-maps (map1 map2)
  (declare (xargs :guard (and (book-mapp map1)
                              (book-mapp map2))))
  (combine-book-maps-aux (union-eq (strip-cars map1) (strip-cars map2))
                         map1
                         map2
                         nil))

(local
 (defthm book-mapp-of-combine-book-maps
   (implies (and (book-mapp map1)
                 (book-mapp map2))
            (book-mapp (combine-book-maps map1 map2)))
   :hints (("Goal" :in-theory (enable combine-book-maps)))))

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

;; TODO: Think about the order here
(defun merge-rec-lists-into-recs (rec-lists recs)
  (declare (xargs :guard (and (recommendation-list-listp rec-lists)
                              (recommendation-listp recs))
                  :verify-guards nil ; done below
                  :guard-hints (("Goal" :in-theory (enable recommendation-listp)))))
  (if (endp rec-lists)
      recs
    (merge-rec-lists-into-recs (rest rec-lists)
                               (merge-recs-into-recs (reverse (first rec-lists)) recs))))

(defthm recommendation-listp-of-merge-recs-lists-into-recs
  (implies (and (recommendation-list-listp rec-lists)
                (recommendation-listp recs))
           (recommendation-listp (merge-rec-lists-into-recs rec-lists recs))))

(verify-guards merge-rec-lists-into-recs)

;; Returns (mv erp recs state).
(defun get-recs-from-model (model num-recs checkpoint-clauses server-url debug print state)
  (declare (xargs :guard (and (model-namep model)
                              (natp num-recs)
                              (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (stringp server-url)
                              (booleanp debug)
                              (acl2::print-levelp print))
                  :mode :program ; because of make-numbered-checkpoint-entries
                  :stobjs state))
  (b* ((model-string (model-to-string model))
       ;; Send query to server:
       ((mv erp semi-parsed-recommendations state)
        (if (zp num-recs)
            (prog2$ (cw "Not asking server for recommendations since num-recs=0.")
                    (mv nil
                        nil ; empty list of recommendations
                        state))
          (b* ((- (and (acl2::print-level-at-least-tp print)
                       (cw "Asking server for ~x0 recommendations from ~x1 on ~x2 ~s3...~%"
                           num-recs
                           model
                           (len checkpoint-clauses)
                           (if (< 1 (len checkpoint-clauses)) "checkpoints" "checkpoint"))))
               (post-data (acons "use-group" model-string
                                 (acons "n" (acl2::nat-to-string num-recs)
                                        (make-numbered-checkpoint-entries 0 checkpoint-clauses))))
               ((mv erp parsed-response state)
                (post-and-parse-response-as-json server-url post-data debug state))
               ((when erp)
                (er hard? 'advice-fn "Error in HTTP POST: ~@0" erp)
                (mv erp nil state))
               ((when (not (acl2::parsed-json-arrayp parsed-response)))
                (er hard? 'advice-fn "Error: Response from server is not a JSON array: ~x0." parsed-response)
                (mv :bad-server-response nil state)))
            (mv nil (acl2::parsed-json-array->values parsed-response) state))))
       ((when erp) (mv erp nil state))
       (- (and (not (consp semi-parsed-recommendations))
               (cw "~% WARNING: No recommendations returned from server.~%")))
       ;; Parse the individual strings in the recs:
       ((mv erp ml-recommendations state) (parse-recommendations semi-parsed-recommendations model state))
       ((when erp)
        (er hard? 'advice-fn "Error parsing recommendations.")
        (mv erp nil state))
       (- (and debug (cw "Parsed ML recommendations: ~X01~%" ml-recommendations nil))))
    (mv nil ; no error
        ml-recommendations
        state)))

;; Returns (mv erp rec-lists state).
(defun get-recs-from-models-aux (models num-recs-per-model checkpoint-clauses server-url debug print acc state)
  (declare (xargs :guard (and (model-namesp models)
                              (natp num-recs-per-model)
                              (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (stringp server-url)
                              (booleanp debug)
                              (acl2::print-levelp print))
                  :mode :program
                  :stobjs state))
  (if (endp models)
      (mv nil acc state) ; no error
    (b* (((mv erp recs state)
          (get-recs-from-model (first models) num-recs-per-model checkpoint-clauses server-url debug print state))
         ((when erp) (mv erp nil state)))
      (get-recs-from-models-aux (rest models) num-recs-per-model checkpoint-clauses server-url debug print
                                (cons recs acc)
                                state))))

;; Returns (mv erp rec-lists state).
(defun get-recs-from-models (models num-recs-per-model checkpoint-clauses server-url debug print acc state)
  (declare (xargs :guard (and (model-namesp models)
                              (natp num-recs-per-model)
                              (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (booleanp debug)
                              (acl2::print-levelp print))
                  :mode :program
                  :stobjs state))
  (b* ( ;; Get server info:
       ((mv erp server-url state)
        (if (null models)
            (mv nil "NONE" state)
          (if server-url
              (mv nil server-url state)
            (getenv$ "ACL2_ADVICE_SERVER" state))))
       ((when erp) (cw "ERROR getting ACL2_ADVICE_SERVER environment variable.") (mv erp nil state))
       ((when (not (stringp server-url)))
        (er hard? 'advice-fn "Please set the ACL2_ADVICE_SERVER environment variable to the server URL (often ends in '/machine_interface').")
        (mv :no-server nil state)))
    (get-recs-from-models-aux models num-recs-per-model checkpoint-clauses server-url debug print acc state)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp provedp rec checkpoint-clauses state) where if PROVEDP determines whether REC or CHECKPOINTS is meaningful.
(defun try-proof-and-get-checkpoint-clauses (theorem-name
                                             theorem-body
                                             translated-theorem-body
                                             theorem-hints
                                             theorem-otf-flg
                                             step-limit
                                             suppress-trivial-warningp
                                             state)
  (declare (xargs :guard (and (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              (pseudo-termp translated-theorem-body)
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (or (null step-limit)
                                  (natp step-limit))
                              (booleanp suppress-trivial-warningp))
                  :stobjs state
                  :mode :program))
  (b* ( ;; Try the theorem with the given hints (todo: consider also getting rid of any existng hints):
       ((mv provedp state)
        (prove$-no-error 'try-proof-and-get-checkpoints theorem-body theorem-hints theorem-otf-flg step-limit state))
       ;; TODO: What if the step-limit applied?  We may want to see how many steps this attempt uses, to decide how many steps to allow in future attempts.
       ((when provedp)
        ;; The original hints worked!
        (and (not suppress-trivial-warningp)
             (if (not theorem-hints)
                 (cw "WARNING: Proved ~x0 with no hints.~%" theorem-name)
               (cw "WARNING: Proved ~x0 with original hints.~%" theorem-name)))
        (mv nil ; no error
            t   ; proved (with the original hints)
            (make-successful-rec "original" :exact-hints theorem-hints nil theorem-body theorem-hints theorem-otf-flg)
            nil ; checkpoints, meaningless
            state))
       ;; The proof failed, so get the checkpoints:
       (raw-checkpoint-clauses (acl2::checkpoint-list ;-pretty
                                t                     ; todo: consider non-top
                                state))
       ((when (eq :unavailable raw-checkpoint-clauses))
        ;; Can this happen?  :doc Checkpoint-list indicates that :unavailable means the proof succeeded.
        (cw "WARNING: Unavailable checkpoints after failed proof of ~x0.~%" theorem-name)
        (mv :no-checkpoints nil nil nil state))
       ;; Deal with unfortunate case when acl2 decides to backtrack and try induction:
       ;; TODO: Or use :otf-flg to get the real checkpoints?
       (checkpoint-clauses (if (equal raw-checkpoint-clauses '((acl2::<goal>)))
                               (clausify-term translated-theorem-body (w state))
                             raw-checkpoint-clauses))
       ((when (null checkpoint-clauses))
        ;; A step-limit may fire before checkpoints can be generated:
        (cw "WARNING: No checkpoints after failed proof of ~x0 (perhaps a limit fired).~%" theorem-name)
        (mv :no-checkpoints nil nil nil state)))
    (mv nil ; no error
        nil ; didn't prove
        nil ; meaningless
        checkpoint-clauses
        state)))

;; Returns (mv erp successp best-rec state).
(defun get-and-try-advice-for-checkpoints (checkpoint-clauses
                                           theorem-name
                                           theorem-body
                                           theorem-hints
                                           theorem-otf-flg
                                           num-recs-per-model
                                           book-to-avoid-absolute-path
                                           print
                                           server-url
                                           debug
                                           step-limit
                                           disallowed-rec-types ;todo: for this, handle the similar treatment of :use-lemma and :add-enable-hint?
                                           disallowed-rec-sources
                                           max-wins
                                           models
                                           state)
  (declare (xargs :guard (and (acl2::pseudo-term-list-listp checkpoint-clauses)
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
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
                              (or ;; (eq :auto max-wins)
                                  (null max-wins)
                                  (natp max-wins))
                              (rec-type-listp disallowed-rec-types)
                              (subsetp-equal disallowed-rec-sources *extra-rec-sources*)
                              (model-namesp models))
                  :stobjs state
                  :mode :program))
  (b* (;; Get the recommendations:
       ((mv erp ml-recommendation-lists state)
        (get-recs-from-models models num-recs-per-model checkpoint-clauses server-url debug print nil state))
       ;; Removes duplicates:
       (ml-recommendations (merge-rec-lists-into-recs ml-recommendation-lists nil))
       ((when erp) (mv erp nil nil state))
       ;; Sort the whole list by confidence (hope the numbers are comparable):
       (ml-recommendations (merge-sort-recs-by-confidence ml-recommendations))
       ;; Make recs that try enabling each function symbol (todo: should we also look at the checkpoints?):
       (enable-recommendations (if (member-equal :enable disallowed-rec-sources)
                                   nil
                                 ;; todo: translate outside make-enable-recs?:
                                 (make-enable-recs theorem-body (w state))))
       ;; Make recs based on hints given to recent theorems:
       ((mv erp recs-from-history state) (if (member-equal :history disallowed-rec-sources)
                                             (mv nil nil state)
                                           (make-recs-from-history state)))
       ((when erp) (mv erp nil nil state))
       ;; todo: remove duplicate recs from multiple sources:
       ;; TODO: Can any of these 3 lists contain dups?
       (recommendations (merge-recs-into-recs (reverse enable-recommendations)  ; reverse to preserve the order, though it's not very meaningful
                                              (merge-recs-into-recs (reverse recs-from-history) ; reverse to preserve the order
                                                                    ml-recommendations)))
       ;; Remove any recs whose types have been disallowed:
       (rec-count-before-removal (len recommendations))
       (recommendations (remove-disallowed-recs recommendations disallowed-rec-types nil))
       (rec-count-after-removal (len recommendations))
       (- (and (< rec-count-after-removal rec-count-before-removal) ; todo: this doesn't catch disallowed enable or history recs suppresses above
               (acl2::print-level-at-least-tp print)
               (cw "NOTE: Removed ~x0 recommendations of disallowed types." (- rec-count-before-removal rec-count-after-removal))))
       ;; Print the recommendations (for now):
       (state (if (acl2::print-level-at-least-tp print)
                  (prog2$ (cw "~%RECOMMENDATIONS TO TRY:~%")
                          (show-recommendations recommendations state) ; why does this return state?
                          )
                state))
       ;; Try the recommendations:
       (- (and print (cw "~%TRYING RECOMMENDATIONS:~%")))
       (state (acl2::widen-margins state))
       ((mv erp successful-recs state)
        (try-recommendations recommendations book-to-avoid-absolute-path theorem-name theorem-body theorem-hints theorem-otf-flg step-limit max-wins print nil state))
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
       (max-wins-reachedp (and (natp max-wins) (= max-wins num-successful-recs))) ; todo: what if the last win was the last rec (then we didn't stop early)?
       (- (and max-wins-reachedp
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
    (mv nil ; no error
        (posp num-successful-recs) ; whether we succeeded
        (first sorted-successful-recs)
        state)))

;; Tries the theorem with the supplied hints.  If that doesn't prove the theorem, this requests and tries advice.
;; Returns (mv erp successp best-rec state).
(defun get-and-try-advice-for-theorem (theorem-name
                                       theorem-body
                                       translated-theorem-body
                                       theorem-hints
                                       theorem-otf-flg
                                       num-recs-per-model
                                       book-to-avoid-absolute-path
                                       print
                                       server-url
                                       debug
                                       step-limit
                                       disallowed-rec-types
                                       disallowed-rec-sources
                                       max-wins
                                       models
                                       suppress-trivial-warningp
                                       state)
  (declare (xargs :guard (and (symbolp theorem-name)
                              ;; theorem-body is an untranslated term
                              (pseudo-termp translated-theorem-body)
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              (natp num-recs-per-model)
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              (acl2::print-levelp print)
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (booleanp debug)
                              (or (null step-limit)
                                  (natp step-limit))
                              (rec-type-listp disallowed-rec-types)
                              (subsetp-equal disallowed-rec-sources *extra-rec-sources*)
                              (or ;; (eq :auto max-wins)
                               (null max-wins)
                               (natp max-wins))
                              (model-namesp models)
                              (booleanp suppress-trivial-warningp))
                  :stobjs state
                  :mode :program))
  (b* (((mv erp provedp rec checkpoint-clauses state)
        (try-proof-and-get-checkpoint-clauses theorem-name
                                              theorem-body
                                              translated-theorem-body
                                              theorem-hints
                                              theorem-otf-flg
                                              step-limit
                                              suppress-trivial-warningp
                                              state))
       ((when erp) (mv erp nil nil state)))
    (if provedp
        (mv nil ; no error
            t   ; success
            rec
            state)
      ;; Didn't prove using the supplied hints, so try advice:
      (get-and-try-advice-for-checkpoints checkpoint-clauses
                                          theorem-name
                                          theorem-body
                                          theorem-hints
                                          theorem-otf-flg
                                          num-recs-per-model
                                          book-to-avoid-absolute-path
                                          print
                                          server-url
                                          debug
                                          step-limit
                                          disallowed-rec-types
                                          disallowed-rec-sources
                                          max-wins
                                          models
                                          state))))

;; Returns (mv erp event state).
(defun defthm-advice-fn (theorem-name
                         theorem-body ; an untranslated term
                         theorem-hints
                         theorem-otf-flg
                         rule-classes
                         num-recs-per-model
                         print
                         server-url
                         debug
                         step-limit
                         disallowed-rec-types
                         disallowed-rec-sources
                         max-wins
                         models
                         state)
  (declare (xargs :guard (and (symbolp theorem-name)
                              ;; theorem-body
                              ;; theorem-hints
                              (booleanp theorem-otf-flg)
                              ;; rule-classes
                              (natp num-recs-per-model)
                              (acl2::print-levelp print)
                              (or (null server-url) ; get url from environment variable
                                  (stringp server-url))
                              (booleanp debug)
                              (or (eq :auto step-limit) ; means use *step-limit*
                                  (eq nil step-limit) ; means no limit
                                  (natp step-limit))
                              (rec-type-listp disallowed-rec-types)
                              (subsetp-equal disallowed-rec-sources *extra-rec-sources*)
                              (or (eq :auto max-wins)
                                  (null max-wins)
                                  (natp max-wins))
                              (or (eq :all models)
                                  (model-namep models) ; represents a singleton set
                                  (model-namesp models)))
                  :stobjs state
                  :mode :program))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (models (if (eq models :all)
                   *known-models*
                 (if (model-namep models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       (translated-theorem-body (acl2::translate-term theorem-body 'defthm-advice-fn wrld))
       ((mv erp successp best-rec state)
        (get-and-try-advice-for-theorem theorem-name
                                        theorem-body
                                        translated-theorem-body
                                        theorem-hints
                                        theorem-otf-flg
                                        num-recs-per-model
                                        nil ; no book to avoid
                                        print
                                        server-url
                                        debug
                                        step-limit
                                        disallowed-rec-types
                                        disallowed-rec-sources
                                        max-wins
                                        models
                                        nil
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
(defmacro defthm-advice (name
                         body
                         &key
                         (hints 'nil)
                         (otf-flg 'nil)
                         ;; options for the advice:
                         (n '10) ; num-recs-per-model
                         (print 't)
                         (server-url 'nil)
                         (debug 'nil)
                         (step-limit ':auto)
                         (disallowed-rec-types 'nil)
                         (disallowed-rec-sources 'nil)
                         (max-wins ':auto)
                         (models ':all)
                         (rule-classes '(:rewrite))
                         )
  `(acl2::make-event-quiet
    (defthm-advice-fn ',name ',body ',hints ,otf-flg ',rule-classes ,n ,print ,server-url ,debug ,step-limit ',disallowed-rec-types ',disallowed-rec-sources ,max-wins ,models state)))

;; Just a synonym in ACL2 package
(defmacro acl2::defthm-advice (&rest rest) `(defthm-advice ,@rest))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event state).
(defun thm-advice-fn (theorem-body ; an untranslated term
                      theorem-hints
                      theorem-otf-flg
                      num-recs-per-model
                      print
                      server-url
                      debug
                      step-limit
                      disallowed-rec-types
                      disallowed-rec-sources
                      max-wins
                      models
                      state)
  (declare (xargs :guard (and ;; theorem-body
                          ;; theorem-hints
                          (booleanp theorem-otf-flg)
                          (natp num-recs-per-model)
                          (acl2::print-levelp print)
                          (or (null server-url) ; get url from environment variable
                              (stringp server-url))
                          (booleanp debug)
                          (or (eq :auto step-limit)   ; means use *step-limit*
                              (eq nil step-limit)     ; means no limit
                              (natp step-limit))
                          (rec-type-listp disallowed-rec-types)
                          (subsetp-equal disallowed-rec-sources *extra-rec-sources*)
                          (or (eq :auto max-wins)
                              (null max-wins)
                              (natp max-wins))
                          (or (eq :all models)
                              (model-namep models) ; represents a singleton set
                              (model-namesp models)))
                  :stobjs state
                  :mode :program))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (models (if (eq models :all)
                   *known-models*
                 (if (model-namep models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       (translated-theorem-body (acl2::translate-term theorem-body 'defthm-advice-fn wrld))
       ((mv erp successp best-rec state)
        (get-and-try-advice-for-theorem 'the-thm
                                        theorem-body
                                        translated-theorem-body
                                        theorem-hints
                                        theorem-otf-flg
                                        num-recs-per-model
                                        nil ; no book to avoid
                                        print
                                        server-url
                                        debug
                                        step-limit
                                        disallowed-rec-types
                                        disallowed-rec-sources
                                        max-wins
                                        models
                                        nil
                                        state))
       ((when erp) (mv erp nil state)))
    (if successp
        (let ((event (successful-rec-to-thm best-rec)))
          (prog2$ (and print (cw "Submitting:~%~X01~%" event nil)) ; todo: improve indenting when printing
                  (mv nil event state)))
      (mv :no-proof-found nil state))))

(defmacro thm-advice ( ; no name
                      body
                      &key
                      (hints 'nil)
                      (otf-flg 'nil)
                      ;; options for the advice:
                      (n '10) ; num-recs-per-model
                      (print 't)
                      (server-url 'nil)
                      (debug 'nil)
                      (step-limit ':auto)
                      (disallowed-rec-types 'nil)
                      (disallowed-rec-sources 'nil)
                      (max-wins ':auto)
                      (models ':all)
                      ;; no rule-classes
                      )
  `(acl2::make-event-quiet
    (thm-advice-fn ',body ',hints ,otf-flg ,n ,print ,server-url ,debug ,step-limit ',disallowed-rec-types ',disallowed-rec-sources ,max-wins ,models state)))

;; Just a synonym in ACL2 package
(defmacro acl2::thm-advice (&rest rest) `(thm-advice ,@rest))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nil state).
;; TODO: Support getting checkpoints from a defun, but then we'd have no body
;; to fall back on when (equal untranslated-checkpoints '(<goal>)) (see
;; below).
(defun advice-fn (n ; number of recommendations from ML requested
                  print
                  server-url
                  debug
                  step-limit
                  disallowed-rec-types
                  disallowed-rec-sources
                  max-wins
                  models
                  state)
  (declare (xargs :guard (and (natp n)
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url))
                              (acl2::checkpoint-list-guard t ;top-p
                                                     state)
                              (booleanp debug)
                              (or (eq :auto step-limit)
                                  (eq nil step-limit)
                                  (natp step-limit))
                              (rec-type-listp disallowed-rec-types)
                              (subsetp-equal disallowed-rec-sources *extra-rec-sources*)
                              (or (eq :auto max-wins)
                                  (null max-wins)
                                  (natp max-wins))
                              (or (eq :all models)
                                  (model-namep models) ; represents a singleton set
                                  (model-namesp models)))
                  :stobjs state
                  :mode :program ; because we untranslate (for now)
                  ))
  (b* ((wrld (w state))
       ;; Elaborate options:
       (models (if (eq models :all)
                   *known-models*
                 (if (model-namep models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       (step-limit (if (eq :auto step-limit) *step-limit* step-limit))
       (max-wins (if (eq :auto max-wins) (get-advice-option! :max-wins wrld) max-wins))
       ;; Get most recent failed theorem:
       (most-recent-failed-theorem (acl2::most-recent-failed-command acl2::*theorem-event-types* state))
       ((mv theorem-name theorem-body theorem-hints theorem-otf-flg)
        (if (member-eq (car most-recent-failed-theorem) '(thm acl2::rule))
            (mv :thm ; no name
                (cadr most-recent-failed-theorem)
                (cadr (assoc-keyword :hints (cddr most-recent-failed-theorem)))
                (cadr (assoc-keyword :otf-flg (cddr most-recent-failed-theorem))))
          ;; Must be a defthm, etc:
          (mv (cadr most-recent-failed-theorem)
              (caddr most-recent-failed-theorem)
              (cadr (assoc-keyword :hints (cdddr most-recent-failed-theorem)))
              (cadr (assoc-keyword :otf-flg (cdddr most-recent-failed-theorem))))))
       (- (and print (cw "Generating advice for:~%~X01:~%" most-recent-failed-theorem nil)))
       (- (and (acl2::print-level-at-least-tp print) (cw "Original hints were:~%~X01.~%" theorem-hints nil)))
       ;; Get the checkpoints from the failed attempt:
       ;; TODO: Consider trying again with no hints, in case the user gave were wrongheaded.
       (raw-checkpoint-clauses (acl2::checkpoint-list ;-pretty
                                t               ; todo: consider non-top
                                state))
       ((when (eq :unavailable raw-checkpoint-clauses))
        (er hard? 'advice-fn "No checkpoints are available (perhaps the most recent theorem succeeded).")
        (mv :no-checkpoints nil state))
       ;; Deal with unfortunate case when acl2 decides to backtrack and try induction:
       ;; TODO: Or use :otf-flg to get the real checkpoints?
       (checkpoint-clauses (if (equal raw-checkpoint-clauses '((acl2::<goal>)))
                               (clausify-term (acl2::translate-term (acl2::most-recent-failed-theorem-goal state)
                                                                    'advice-fn
                                                                    wrld)
                                              wrld)
                             raw-checkpoint-clauses))
       (- (and (acl2::print-level-at-least-tp print) (cw "Proof checkpoints to use: ~X01.)~%" checkpoint-clauses nil)))
       ((mv erp
            & ;; successp
            & ;; best-rec
            state)
        (get-and-try-advice-for-checkpoints checkpoint-clauses
                                            theorem-name
                                            theorem-body
                                            theorem-hints
                                            theorem-otf-flg
                                            n ; number of recommendations from ML requested
                                            nil ; no book to avoid (TODO: Maybe avoid the last LDed book, in case they are working on it now)
                                            print
                                            server-url
                                            debug
                                            step-limit
                                            disallowed-rec-types
                                            disallowed-rec-sources
                                            max-wins
                                            models
                                            state))
       ((when erp) (mv erp nil state))
       ;; Ensure there are no checkpoints left over from an attempt to use advice, in case the user calls the tool again.
       ;; TODO: Can we restore the old gag state saved?
       ;;(state (f-put-global 'gag-state-saved nil state))

       ;; Try to ensure the checkpoints are restored, in case the tool is run again:
       (state
        (b* ((new-raw-checkpoint-clauses (acl2::checkpoint-list ;-pretty
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
              (cw "WARNING: Tried the theorem again and it worked!")
              state)
             (new-raw-checkpoint-clauses (acl2::checkpoint-list ;-pretty
                                          t ; todo: consider non-top
                                          state))
             ((when (not (equal new-raw-checkpoint-clauses raw-checkpoint-clauses)))
              (acl2::print-level-at-least-tp print)
              (cw "Clearing checkpoints since we failed to restore them.~%")
              (let ((state (f-put-global 'gag-state-saved nil state)))
                state)))
          state)))
       (mv nil ; no error
        '(value-triple :invisible) state)))

;; Generate advice for the most recent failed theorem.
(defmacro advice (&key (n '10) ; num-recs-per-model
                       (print 't)
                       (server-url 'nil)
                       (debug 'nil)
                       (step-limit ':auto)
                       (disallowed-rec-types 'nil)
                       (disallowed-rec-sources 'nil)
                       (max-wins ':auto)
                       (models ':all))
  `(acl2::make-event-quiet (advice-fn ,n ,print ,server-url ,debug ,step-limit ',disallowed-rec-types ',disallowed-rec-sources ,max-wins ,models state)))

;; Just a synonym in ACL2 package
(defmacro acl2::advice (&rest rest) `(advice ,@rest))

;; Example:
;; (acl2s-defaults :set testing-enabled nil) ; turn off testing
;; (thm (equal (- (- x)) x))
;; (advice)
;; (thm (< (mod x 8) 256))
;; (advice)
