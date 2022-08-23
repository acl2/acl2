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
;; - skip add-hyp when the hyp is already there
;; - add-skip hyp when the hyp would contradict the existing assumptions (together satisfiable together)
;; - skip add-hyp when cgen can falsify the theorem even with the hyp
;; - (maybe) skip a hyp that is implied by the existing hyps (low probability of working)
;; - skip add-library when already present
;; - skip :hints that are already present or subsumed by ones already present
;; - (maybe) skip :hints that conflict with ones already present (e.g., :induct, enable vs and explicit disable)
;; - avoid anything except add-hyp when cgen can falsify the theorem (can't possibly fix the problem)
;; - (maybe) try to avoid theory-invariant warnings
;; - (maybe) try to help clean up hyps (e.g., replacing a subsumed hyp when add-hyp strengthens one, maybe using tau)
;; - avoid both add-enable-hint and use-lemma of the same rule
;; - what else?

;; TODO: All a time limit for trying recommendations and keep trying more and
;; more until that limit is reached

;; TODO: Group recommendations that need the same supporting book to be
;; included, to avoid re-including the same book later.

;; TODO: Incorporate cgen to try to see if the theorem is valid or not.

;; TODO: Why does getting advice take ~3 seconds?

;; TODO: Allow doing :rec <n> to try recommendation <n>

;; TODO: Consider trying the advice on the checkpoint(s), not just the goal.

(include-book "kestrel/utilities/checkpoints" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system) ; todo reduce, for nat-to-string
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/hints" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/read-string" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/typed-lists-light/string-list-listp" :dir :system)
(include-book "kestrel/htclient/top" :dir :system)
(include-book "kestrel/json-parser/parse-json" :dir :system)
(include-book "kestrel/big-data/packages" :dir :system) ; try to ensure all packages tha might arise are known
(include-book "std/io/read-string" :dir :system)
(include-book "tools/prove-dollar" :dir :system)

(defconst *step-limit* 100000)

(local (in-theory (disable state-p
                           checkpoint-list-guard)))


;move
(defund name-that-can-be-enabled/disabledp (name wrld)
  (declare (xargs :guard (and ;; (symbolp name)
                          (plist-worldp wrld))))
  (let ((name (if (symbolp name)
                  name
                (if (and (consp name) ; might be (:rewrite foo) or (:rewrite foo . 1)
                         (eq :rewrite (car name))
                         (consp (cdr name))
                         (cadr name)
                         (symbolp (cadr name)))
                    (cadr name)
                  (er hard? 'name-that-can-be-enabled/disabledp "Unknown kind of name: ~x0.")))))
  (or (getpropc name 'unnormalized-body nil wrld)
      (getpropc name 'theorem nil wrld) ;todo: what if it has :rule-classes nil?
      (let ((alist (table-alist 'macro-aliases-table wrld)))
        (and (alistp alist) ; should always be true
             (assoc-eq name alist))))))

;move
(defthm parsed-json-object-pairsp-forward-to-alistp
  (implies (parsed-json-object-pairsp pairs)
           (alistp pairs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp))))

;; Recognize a list of parsed json-arrays.
(defun parsed-json-array-listp (x)
  (declare (xargs :guard t))
  (if (not (consp x))
      (null x)
    (and (parsed-json-arrayp (first x))
         (parsed-json-array-listp (rest x)))))

;move
(defund parsed-json-array->values (array)
  (declare (xargs :guard (parsed-json-arrayp array)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-arrayp)))))
  (cadr array) ; strip the :array
  )

;move
(defund parsed-json-object->pairs (object)
  (declare (xargs :guard (parsed-json-objectp object)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-objectp)))))
  (cadr object) ; strip the :object
  )

(defthm alistp-of-parsed-json-object->pairs
  (implies (and (state-p state)
                (parsed-json-objectp book-map))
           (alistp (parsed-json-object->pairs book-map)))
  :hints (("Goal" :in-theory (enable parsed-json-object->pairs
                                     parsed-json-objectp))))

;; Returns (mv erp lists)
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
  (declare (xargs :mode :program))
  (if (endp checkpoints)
      nil
    (acons (concatenate 'string "checkpoint_" (nat-to-string current-number))
           (fms-to-string "~X01" (acons #\0  (first checkpoints) (acons #\1 nil nil)))
           (make-numbered-checkpoint-entries (+ 1 current-number) (rest checkpoints)))))

(defun show-recommendation (rec num)
  (declare (xargs :guard (posp num)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-objectp)))))
  (if (not (parsed-json-objectp rec))
      (er hard? 'show-recommendation "Bad rec: ~x0." rec)
    (let* ((dict (cadr rec)) ; strip the :object
           (type (lookup-equal "type" dict))
           (object (lookup-equal "object" dict))
           (confidence (lookup-equal "confidence" dict))
           (confidence-percent (floor (* (rfix confidence) 100) 1)))
      (cw "~c0 Try ~s1 with ~s2 (conf: ~x3%).~%" (cons num 2) type object confidence-percent))))

(defun show-recommendations-aux (recs num)
  (declare (xargs :guard (and (parsed-json-valuesp recs)
                              (posp num))
                  :guard-hints (("Goal" :in-theory (enable parsed-json-valuesp)))))
  (if (endp recs)
      nil
    (prog2$ (show-recommendation (first recs) num)
            (show-recommendations-aux (rest recs) (+ 1 num)))))

(defun widen-margins (state)
  (declare (xargs :stobjs state
                  :mode :program ; todo
                  ))
  (let* ((old-fmt-hard-right-margin (f-get-global 'fmt-hard-right-margin state))
         (old-fmt-soft-right-margin (f-get-global 'fmt-soft-right-margin state))
         ;; save the old values for later restoration:
         (state (f-put-global 'old-fmt-hard-right-margin old-fmt-hard-right-margin state))
         (state (f-put-global 'old-fmt-soft-right-margin old-fmt-soft-right-margin state))
         ;; Change the margins
         (state (set-fmt-hard-right-margin 210 state))
         (state (set-fmt-soft-right-margin 200 state)))
    state))

(defun unwiden-margins (state)
  (declare (xargs :stobjs state
                  :mode :program ; todo
                  ))
  ;; Restore the margins:
  (let* ((state (set-fmt-hard-right-margin (f-get-global 'old-fmt-hard-right-margin state) state))
         (state (set-fmt-soft-right-margin (f-get-global 'old-fmt-soft-right-margin state) state)))
    state))

;; Returns state
;; TODO: Redo to handle parsed recs
;; TODO: Add ability to show only the ones that helped
(defun show-recommendations (recs state)
  (declare (xargs :guard (parsed-json-valuesp recs)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-arrayp)))
                  :verify-guards nil ; todo
                  :mode :program ;todo
                  :stobjs state))
  (let ((state (widen-margins state)))
    (progn$ (cw "~%RECOMMENDATIONS:~%")
            (show-recommendations-aux recs 1) ;; strip the :array
            (let ((state (unwiden-margins state)))
              state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; Returns (mv erp form state).
(defun parse-include-book (string state)
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
(defun parse-book-map-info-lists (lists acc state)
  (declare (xargs :guard (and (string-list-listp lists)
                              (true-listp acc))
                  :stobjs state))
  (if (endp lists)
      (mv nil (reverse acc) state)
    (b* (((mv erp list state) (parse-book-map-info-list (first lists) nil state))
         ((when erp) (mv erp nil state))
         ((when (and (member-eq :builtin list)
                     (not (= 1 (len list)))))
          (er hard? 'parse-book-map-info-lists "Bad book-map-info: ~x0, which parsed to ~x1." (first lists) list)
          (mv t nil state))
         (list (if (member-eq :builtin list)
                   :builtin
                 list)))
      (parse-book-map-info-lists (rest lists) (cons list acc) state))))

(defthm true-listp-of-mv-nth-1-of-parse-book-map-info-lists
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (parse-book-map-info-lists lists acc state))))
  :rule-classes :type-prescription)

;; returns (mv erp parsed-book-map state)
(defun parse-book-map (book-map state)
  (declare (xargs :stobjs state
;                  :verify-guards nil ; todo
                  ))
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

;; Returns (mv erp parsed-recommendation state) where parsed-recommendation may be :none.
(defun parse-recommendation (rec state)
  (declare (xargs :stobjs state
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
          (cw "WARNING: Bad book map in rec: ~x0.~%" rec)
          (mv nil ; supressing this error for now
              :none state))
         (confidence-percent (floor (* (rfix confidence) 100) 1))
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
          (mv :parse-error nil state)))
      (mv nil ; no error
          (list type-keyword parsed-object confidence-percent book-map)
          state))))

;; Returns (mv erp parsed-recommendations state).
(defun parse-recommendations-aux (recs acc state)
  (declare (xargs :guard (and (parsed-json-valuesp recs)
                              (true-listp acc))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable parsed-json-valuesp)))))
  (if (endp recs)
      (mv nil (reverse acc) state)
    (b* (((mv erp parsed-recommendation state) (parse-recommendation (first recs) state))
         ((when erp) (mv erp nil state)))
      (parse-recommendations-aux (rest recs)
                                 (if (eq :none parsed-recommendation)
                                     acc
                                   (cons parsed-recommendation acc))
                                 state))))

;; Returns (mv erp parsed-recommendations state).
(defun parse-recommendations (recs state)
  (declare (xargs :guard (parsed-json-arrayp recs)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-arrayp)))
                  :verify-guards nil ; todo
                  :stobjs state))
  (parse-recommendations-aux recs nil state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Think about THM vs DEFTHM

(defun make-thm-to-attempt (body hints otf-flg)
  `(thm ,body
        ,@(and hints `(:hints ,hints))
        ,@(and otf-flg `(:otf-flg .otf-flg))))

;; Returns (mv provedp state)
(defmacro prove$-checked (ctx &rest args)
  `(mv-let (erp provedp state)
     (prove$ ,@args)
     (if erp
         (prog2$ (cw "Syntax error in prove$ call (made by ~x0).~%" ,ctx)
                 (mv nil state))
       (mv provedp state))))

;; Calls prove$ but first does an include-book, which is undone after the prove$
;; Returns (mv erp provedp state).
(defun prove$-with-include-book (ctx body include-book-form
                                     name-to-check ; we ensure this exists after the include-book, or nil
                                 ;; args to prove$:
                                 hints otf-flg step-limit
                                 state)
  (declare (xargs :stobjs state :mode :program))
  (revert-world ;; ensures the include-book gets undone
   (b* (;; Try to include the recommended book:
        ((mv erp state) (submit-event-helper include-book-form nil nil state))
        ((when erp) ; can happen if there is a name clash
         (cw "NOTE: Event failed (possible name clash): ~x0.~%" include-book-form)
         (mv nil ; not considering this an error, since if there is a name clash we want to try the other recommendations
             nil state))
        ((when (and name-to-check
                    (not (name-that-can-be-enabled/disabledp name-to-check (w state)))))
         (cw "NOTE: After including ~x0, ~x1 is still not defined.~%" (cadr include-book-form) name-to-check)
         (mv nil ; suppress error
             nil state))
        ;; Now see whether we can prove the theorem using the new include-book:
        ;; ((mv erp ;todo: how to distinguish real errors?
        ;;      state) (submit-event-helper
        ;;                  `(encapsulate ()
        ;;                     (local ,include-book-form)
        ;;                     ,(make-thm-to-attempt theorem-body theorem-hints theorem-otf-flg))
        ;;                  t nil state))
        ;; (provedp (not erp))
        ((mv provedp state) (prove$-checked ctx
                                            body
                                            :hints hints
                                            :otf-flg otf-flg
                                            :step-limit step-limit)))
     (mv nil provedp state))))

;; Try to prove BODY after submitting each of the INCLUDE-BOOK-FORMS (separately).
;; Returns (mv erp successful-include-book-form-or-nil state).
;; TODO: Don't return erp if we will always suppress errors.
(defun try-prove$-with-include-books (ctx
                                      body
                                      include-book-forms
                                      name-to-check
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
          (prove$-with-include-book ctx body
                                    form
                                    name-to-check
                                    ;; args to prove$:
                                    hints otf-flg step-limit
                                    state))
         ;; ((when erp) (mv erp nil state))
         ((when provedp) (mv nil form state)))
      (try-prove$-with-include-books ctx
                                     body
                                     (rest include-book-forms)
                                     name-to-check
                                     ;; args to prove$:
                                     hints otf-flg step-limit
                                     state))))

;; Returns (mv erp successp state).
;; TODO: Skip if library already included
;; TODO: Skip later add-library recs if they are included by this one (though I suppose they might work only without the rest of what we get here).
;; TODO: Try any upcoming enable or use-lemma recs that (may) need this library:
(defun try-add-library (include-book-form theorem-name theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name) ; todo: use to make a suggestion
           )
  (if (not (consp include-book-form)) ; can be "Other"
      (prog2$ (cw "FAIL (ill-formed library recommendation: ~x0)~%" include-book-form)
              (mv nil nil state))
    (b* (((mv erp provedp state)
          (prove$-with-include-book 'try-add-library theorem-body include-book-form nil theorem-hints theorem-otf-flg *step-limit* state))
         ((when erp) (mv erp nil state))
         (- (if provedp (cw "SUCCESS: ~x0~%" include-book-form) (cw "FAIL~%"))))
      (mv nil provedp state))))

;; Returns (mv erp successp state).
;; TODO: Don't try a hyp that is already present, or contradicts ones already present
(defun try-add-hyp (hyp theorem-name theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* ((translatablep (translatable-termp hyp (w state)))
       ((when (not translatablep))
        (cw "FAIL (hyp not translatable: ~x0)~%" hyp) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  ;; TODO: Add the hyp more nicely:
       ;;                  (make-thm-to-attempt `(implies ,hyp ,theorem-body) theorem-hints theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-checked 'try-add-hyp
                                           `(implies ,hyp ,theorem-body)
                                           :hints theorem-hints
                                           :otf-flg theorem-otf-flg
                                           :step-limit *step-limit*))
       (- (if provedp (cw "SUCCESS: Add hyp ~x0~%" hyp) (cw "FAIL~%"))))
    (mv nil provedp state)))

;; Returns all disabled runes associate with NAME.
;; Like disabledp but hygienic, also doesn't end in "p" since not a predicate.
(defun disabled-runes (name ens wrld)
  (declare (xargs :mode :program))
  (disabledp-fn name ens wrld))

;; (defun known-namep (sym wrld)
;;   (declare (xargs :guard (and (symbolp sym)
;;                               (plist-worldp wrld))))
;;   (or (function-symbolp sym wrld)
;;        (getprop sym 'theorem nil 'current-acl2-world wrld)))


;; Returns (mv erp successp state).
;; TODO: Avoid theory-invariant violations from enabling.
(defun try-add-enable-hint (rule ; the rule to try enabling
                            book-map ; info on where the rule may be found
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            state)
  (declare (xargs :stobjs state :mode :program))
  (let ((wrld (w state)))
    (if (function-symbolp rule wrld)
        ;; It's a function in the current world:
        (b* ((fn rule)
             ((when (not (logicp fn wrld)))
              (cw "SKIP (Can't enable ~x0. Not in :logic mode.)~%" fn)
              (mv nil nil state))
             ((when (not (and
                              ;; (defined-functionp fn wrld) ;todo
                              )))
              (cw "SKIP (Can't enable ~x0. No body.)~%" fn)
              (mv nil nil state))
             ;; TODO: Consider whether to enable, say the :type-prescription rule
             (rune `(:definition ,fn))
             ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
             ((when (enabled-runep rune (ens-maybe-brr state) (w state)))
              (cw "SKIP (~x0 is already enabled.)~%" fn)
              (mv nil nil state))
             ;; FN exists and just needs to be enabled:
             (new-hints (enable-runes-in-hints theorem-hints (list fn))) ;; todo: ensure this is nice
             ((mv provedp state)
              (prove$-checked 'try-add-enable-hint
                              theorem-body
                              :hints new-hints
                              :otf-flg theorem-otf-flg
                              :step-limit *step-limit*))
             (- (if provedp (cw "SUCCESS: Enable ~x0~%" fn) (cw "FAIL~%"))))
          (mv nil provedp state))
      (if (not (eq :no-body (getpropc rule 'theorem :no-body wrld))) ;todo: how to just check if the property is set?
          ;; It's a theorem in the current world:
        (b* (;; TODO: Consider whether to enable, say the :type-prescription rule
             (rune `(:rewrite ,rule))
             ;; Rule already enabled, so don't bother (TODO: I suppose if the :hints disable it, we could reverse that):
             ((when (enabled-runep rune (ens-maybe-brr state) (w state)))
              (cw "SKIP (~x0 is already enabled.)~%" rule)
              (mv nil nil state))
             ;; RULE exists and just needs to be enabled:
             (new-hints (enable-runes-in-hints theorem-hints (list rule))) ;; todo: ensure this is nice
             ((mv provedp state)
              (prove$-checked 'try-add-enable-hint
                              theorem-body
                              :hints new-hints
                              :otf-flg theorem-otf-flg
                              :step-limit *step-limit*))
             (- (if provedp (cw "SUCCESS: Enable ~x0~%" rule) (cw "FAIL~%"))))
          (mv nil provedp state))
        ;; RULE is not currently known, so try to find where it is defined:
        (b* ((book-map-keys (strip-cars book-map))
             ((when (not (equal book-map-keys (list rule))))
              (cw "WARNING: Bad book map, ~X01, for ~x2.~%" book-map nil rule)
              (mv :bad-book-map nil state))
             (books-to-try (lookup-eq rule book-map))
             ((when (eq :builtin books-to-try))
              (er hard? 'try-add-enable-hint "~x0 does not seem to be built-in, contrary to the book-map.")
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
          (b* (;; TODO: For each of these, if it works, maybe just try the include-book without the enable:
               ;; TODO: If, after including the book, the name to enable is a function, enabling it seems unlikely to help given that it didn't appear in the original proof.
               ((mv erp successful-include-book-form-or-nil state)
                (try-prove$-with-include-books 'try-add-enable-hint theorem-body books-to-try rule new-hints theorem-otf-flg *step-limit* state))
               ((when erp) (mv erp nil state))
               (provedp (if successful-include-book-form-or-nil t nil))
               (- (if provedp
                      (cw "SUCCESS: Include ~x0 and enable ~x1.~%" successful-include-book-form-or-nil rule)
                    (if (< 3 num-books-to-try-orig)
                        ;; todo: try more if we didn't find it?:
                        (cw "FAIL (Note: We only tried ~x0 of the ~x1 books that might contain ~x2)~%" (len books-to-try) num-books-to-try-orig rule)
                      (cw "FAIL~%")))))
            (mv nil provedp state)))))))

;; Returns (mv erp successp state).
(defun try-add-disable-hint (rule theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((when (eq rule 'other)) ;; "Other" is a catch-all for low-frequency classes
        (cw "SKIP (Not disabling catch-all: ~x0)~%" rule)
        (mv nil nil state))
       ((when (not (name-that-can-be-enabled/disabledp rule (w state))))
        (cw "SKIP (Not disabling unknown name: ~x0)~%" rule) ;; For now, we don't try to including the book that brings in the thing to disable!
        (mv nil nil state))
       ((when (disabledp-fn rule (ens-maybe-brr state) (w state)))
        (cw "SKIP (Not disabling since already disabled: ~x0)~%" rule)
        (mv nil nil state))
       ((mv provedp state) (prove$-checked 'try-add-disable-hint
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           :hints (disable-runes-in-hints theorem-hints (list rule))
                                           :otf-flg theorem-otf-flg
                                           :step-limit *step-limit*))
       (- (if provedp (cw "SUCCESS: Disable ~x0~%" rule) (cw "FAIL~%"))))
    (mv nil provedp state)))

;; Returns (mv erp successp state).
;; TODO: Do we need to guess a substitution for the :use hint?
(defun try-add-use-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq item 'other))
        (cw "SKIP (Unknown name: ~x0)~%" item)
        (mv nil nil state))
       ((when (not (or (getpropc item 'unnormalized-body nil (w state))
                       (getpropc item 'theorem nil (w state)))))
        (cw "FAIL (Unknown name: ~x0)~%" item) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :use ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-checked 'try-add-use-hint
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           :hints (cons `("Goal" :use ,item) theorem-hints)
                                           :otf-flg theorem-otf-flg
                                           :step-limit *step-limit*))
       (- (if provedp (cw "SUCCESS: Add :use hint ~x0~%" item) (cw "FAIL~%"))))
    (mv nil provedp state)))

;; Returns (mv erp successp state).
(defun try-add-expand-hint (item ; the thing to expand
                            theorem-name theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (eq 'other item))
        (cw "FAIL (ignoring recommendation to expand \"Other\")~%")
        (mv nil nil state))
       ((when (symbolp item)) ; todo: eventually remove this case
        (cw "FAIL (ignoring illegal recommendation to expand a symbol)~%")
        (mv nil nil state))
       ;; todo: can it be a single term?:
       ((when (not (translatable-term-listp item (w state))))
        (cw "FAIL (term not all translatable: ~x0)~%" item) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :expand ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-checked 'try-add-expand-hint
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           :hints (cons `("Goal" :expand ,item) theorem-hints)
                                           :otf-flg theorem-otf-flg
                                           :step-limit *step-limit*))
       (- (if provedp (cw "SUCCESS: Add :expand hint ~x0~%" item) (cw "FAIL~%"))))
    (mv nil provedp state)))

;; Returns (mv erp successp state).
(defun try-add-cases-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name))
  (b* (((when (not (translatable-term-listp item (w state))))
        (cw "FAIL (terms not all translatable: ~x0)~%" item) ;; TTODO: Include any necessary books first
        (mv nil nil state))
       ;; Now see whether we can prove the theorem using the new hyp:
       ;; ((mv erp state) (submit-event-helper
       ;;                  (make-thm-to-attempt theorem-body
       ;;                                       ;; todo: ensure this is nice:
       ;;                                       (cons `("Goal" :cases ,item)
       ;;                                             theorem-hints)
       ;;                                       theorem-otf-flg)
       ;;                  t nil state))
       ((mv provedp state) (prove$-checked 'try-add-cases-hint
                                           theorem-body
                                           ;; todo: ensure this is nice:
                                           :hints (cons `("Goal" :cases ,item) theorem-hints)
                                           :otf-flg theorem-otf-flg
                                           :step-limit *step-limit*))
       (- (if provedp (cw "SUCCESS: Add :cases hint ~x0~%" item) (cw "FAIL~%"))))
    (mv nil provedp state)))

;; Returns (mv erp successp state).
;; TODO: We need more than a symbol
(defun try-add-induct-hint (item theorem-name theorem-body theorem-hints theorem-otf-flg state)
  (declare (xargs :stobjs state :mode :program)
           (ignore theorem-name theorem-body theorem-hints theorem-otf-flg))
  (if (symbolp item)
      (prog2$ (cw "FAIL (need arguments of ~x0 to create :induct hint)~%" item)
              (mv nil nil state))
    ;; TODO: Flesh this out when ready:
    (mv :unsupported-induct-hint nil state)))

;; Returns (mv erp result-bools state)
(defun try-recommendations (recs
                            theorem-name ; may be :thm
                            theorem-body
                            theorem-hints
                            theorem-otf-flg
                            rec-num
                            result-bools-acc
                            state)
  (declare (xargs :stobjs state :mode :program))
  (if (endp recs)
      (mv nil (reverse result-bools-acc) state)
    (b* ((rec (first recs))
         (type (car rec))
         (object (cadr rec))
         ;; (confidence-percent (caddr rec))
         (book-map (cadddr rec))
         (- (cw "~x0: " rec-num)))
      (mv-let (erp successp state)
        (case type
          ;; TODO: Pass the book-map to all who can use it:
          (:add-library (try-add-library object theorem-name theorem-body theorem-hints theorem-otf-flg state))
          (:add-hyp (try-add-hyp object theorem-name theorem-body theorem-hints theorem-otf-flg state))
          (:add-enable-hint (try-add-enable-hint object book-map theorem-body theorem-hints theorem-otf-flg state))
          (:add-disable-hint (try-add-disable-hint object theorem-body theorem-hints theorem-otf-flg state))
          (:add-use-hint (try-add-use-hint object theorem-name theorem-body theorem-hints theorem-otf-flg state))
          (:add-expand-hint (try-add-expand-hint object theorem-name theorem-body theorem-hints theorem-otf-flg state))
          (:add-cases-hint (try-add-cases-hint object theorem-name theorem-body theorem-hints theorem-otf-flg state))
          (:add-induct-hint (try-add-induct-hint object theorem-name theorem-body theorem-hints theorem-otf-flg state))
          ;; same as for try-add-enable-hint above:
          (:use-lemma (try-add-enable-hint object book-map theorem-body theorem-hints theorem-otf-flg state))
          (t (prog2$ (cw "UNHANDLED rec type ~x0.~%" type)
                     (mv t nil state))))
        (if erp
            (mv erp nil state)
          (try-recommendations (rest recs) theorem-name theorem-body theorem-hints theorem-otf-flg (+ 1 rec-num)
                               (cons successp result-bools-acc)
                               state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp nil state).
;; TODO: Support getting checkpoints from a defun, but then we'd have no body
;; to fall back on when (equal untranslated-checkpoints '(<goal>)) (see
;; below).
(defun advice-fn (n ; number of recommendations requested
                  verbose
                  server-url
                  debug
                  state)
  (declare (xargs :guard (and (natp n)
                              (booleanp verbose)
                              (checkpoint-list-guard t ;top-p
                                                     state)
                              (booleanp debug))
                  :stobjs state
                  :mode :program ; because we untranslate (for now)
                  ))
  (b* (((mv erp server-url state) (if server-url (mv nil server-url state) (getenv$ "ACL2_ADVICE_SERVER" state)))
       ((when erp) (cw "ERROR getting ACL2_ADVICE_SERVER environment variable.") (mv erp nil state))
       ((when (not (stringp server-url)))
        (er hard? 'advice-fn "Please set the ACL2_ADVICE_SERVER environment variable to the server URL (often ends in '/machine_interface').")
        (mv :no-server nil state))
       (most-recent-failed-theorem (most-recent-failed-command *theorem-event-types* state))
       (- (cw "Generating advice for:~%~X01:~%" most-recent-failed-theorem nil))
       (most-recent-failed-theorem-goal (most-recent-failed-theorem-goal state))
       (untranslated-checkpoints (checkpoint-list-pretty t ; todo: consider non-top
                                                         state))
       ((when (eq :unavailable untranslated-checkpoints))
        (er hard? 'advice-fn "No checkpoints are available (perhaps the most recent theorem succeeded).")
        (mv :no-checkpoints nil state))
       ;; Deal with unfortunate case when acl2 decides to backtrack and try induction:
       (untranslated-checkpoints (if (equal untranslated-checkpoints '(<goal>))
                                     (list most-recent-failed-theorem-goal) ; todo: flatten ANDs in this?
                                   untranslated-checkpoints))
       ;; ;; todo: eventually, don't do this:
       ;; (untranslated-checkpoints (untranslate-list-list translated-checkpoints
       ;;                                                  t ; iff-flg ; todo: think about this
       ;;                                                  (w state)))
       (- (and verbose
               (cw "Checkpoints in query: ~X01.)~%" untranslated-checkpoints nil)))
       ;; (printed-checkpoints (fms-to-string "~X01" (acons #\0 untranslated-checkpoints
       ;;                                                   (acons #\1 nil nil))))
       (post-data (acons "n" (nat-to-string n)
                         (make-numbered-checkpoint-entries 0 untranslated-checkpoints)))
       ;; (- (cw "POST data to be sent: ~X01.~%" post-data nil))
       (- (cw "Asking server for recommendations on ~x0 ~s1...~%"
              (len untranslated-checkpoints)
              (if (< 1 (len untranslated-checkpoints)) "checkpoints" "checkpoint")))
       ((mv erp post-response state) (htclient::post server-url post-data state))
       ((when erp)
        (er hard? 'advice-fn "Error in HTTP POST: ~@0" erp)
        (mv erp nil state))
       (- (and debug (cw "Raw JSON POST response: ~X01~%" post-response nil)))
       ;; (- (cw "Info returned from recommendation server: ~X01~%" post-response nil))
       ((mv erp parsed-json) (parse-string-as-json post-response))
       (semi-parsed-recommendations (parsed-json-array->values parsed-json))
       (- (and debug (cw "After JSON parsing: ~X01~%" semi-parsed-recommendations nil)))
       ((when erp)
        (er hard? 'advice-fn "Error parsing JSON.")
        (mv erp nil state))
       ;; (- (cw "Parsed info returned from recommendation server: ~X01~%" parsed-recommendations nil))
       ((mv erp parsed-recommendations state) (parse-recommendations semi-parsed-recommendations state))
       ((when erp)
        (er hard? 'advice-fn "Error parsing recommendations.")
        (mv erp nil state))
       (- (and debug (cw "Parsed recommendations: ~X01~%" parsed-recommendations nil)))
       (state (show-recommendations semi-parsed-recommendations state))
       (- (cw "~%TRYING RECOMMENDATIONS:~%"))
       ((mv name body hints otf-flg)
        (if (member-eq (car most-recent-failed-theorem) '(thm rule))
            (mv :thm ; no name
                (cadr most-recent-failed-theorem)
                (assoc-eq :hints (cddr most-recent-failed-theorem))
                (assoc-eq :otf-flg (cddr most-recent-failed-theorem)))
          ;; Must be a defthm, etc:
          (mv (cadr most-recent-failed-theorem)
              (caddr most-recent-failed-theorem)
              (assoc-eq :hints (cdddr most-recent-failed-theorem))
              (assoc-eq :otf-flg (cdddr most-recent-failed-theorem)))))
       (state (widen-margins state))
       ((mv erp
            & ; result-bools ; todo: use
            state) (try-recommendations parsed-recommendations name body hints otf-flg 1 nil state))
       (state (unwiden-margins state))
       ((when erp)
        (er hard? 'advice-fn "Error trying recommendations.")
        (mv erp nil state)))
    (mv nil ;(erp-nil)
        '(value-triple :invisible) state)))

(defmacro advice (&key (n '10) (verbose 'nil) (server-url 'nil) (debug 'nil))
  `(make-event-quiet (advice-fn ,n ,verbose ,server-url ,debug state)))

;; Example:
;; (acl2s-defaults :set testing-enabled nil) ; turn off testing
;; (thm (equal (- (- x)) x))
;; (advice)
;; (thm (< (mod x 8) 256))
;; (advice)
