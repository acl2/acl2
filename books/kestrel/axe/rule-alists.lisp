; Rule-alists: databases of rules used by Axe
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-axe-rules") ; todo: reduce?
(include-book "stored-rules")
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system) ; move this book
(local (include-book "kestrel/sequences/defforall" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(in-theory (disable fgetprop)) ;move

;; Rule-alists are structures that index rules by the top function symbol of their LHSes.
;; TODO: Consider using a property list world to make the lookups faster.

;; A rule-alist is a database of rules used by Axe.  It is a list of entries,
;; where each entry maps a function symbol to a list of stored-rules that can
;; rewrite calls of that function.  (Every Axe rules must have a topmost function
;; symbol that can be used as a key for this alist; that is, the LHS of a rule
;; can't be a constant or a variable.)
(defund rule-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let* ((entry (car alist))) ; (fn . stored-rules)
      (and (consp entry)
           (let ((fn (car entry))
                 (stored-rules (cdr entry)))
             (and (symbolp fn)
                  (stored-axe-rule-listp stored-rules)))
           (rule-alistp (cdr alist))))))

;really of acons?
(defthm rule-alistp-of-cons-of-cons
  (equal (rule-alistp (cons (cons key val) alist))
         (and (rule-alistp alist)
              (true-listp val)
              (symbolp key)
              (stored-axe-rule-listp val)))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal rule-alistp))))

(defthm rule-alistp-of-acons
  (implies (and (symbolp fn)
                (stored-axe-rule-listp stored-rules)
                (rule-alistp rule-alist))
           (rule-alistp (acons fn stored-rules rule-alist)))
  :hints (("Goal" :in-theory (enable rule-alistp acons))))

;rename
;disable outside of axe, or make a :forward-chaining rule
(local
  (defthmd rule-alistp-means-alistp
    (implies (rule-alistp alist)
             (alistp alist))
    :rule-classes ((:rewrite :backchain-limit-lst 1))
    :hints (("Goal" :in-theory (enable rule-alistp)))))

;rename
;disable outside of axe, or make a :forward-chaining rule
(defthm rule-alistp-means-symbol-alistp
  (implies (rule-alistp alist)
           (symbol-alistp alist))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints (("Goal" :in-theory (enable rule-alistp))))

;; todo: why is this about the -aux function?
(defthm rule-alistp-of-uniquify-alist-eq-aux
  (implies (and (rule-alistp alist)
                (rule-alistp acc))
           (rule-alistp (uniquify-alist-eq-aux alist acc)))
  :hints (("Goal" :in-theory (enable rule-alistp acons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The empty rule-alist is just an empty alist.
(defun empty-rule-alist () (declare (xargs :guard t)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline get-rules-for-fn (fn rule-alist)
  (declare (xargs :guard (and (symbolp fn)
                              (rule-alistp rule-alist))))
  (lookup-eq fn rule-alist))

;; (defthmd true-listp-of-get-rules-for-fn-when-rule-alistp
;;   (implies (rule-alistp alist)
;;            (true-listp (get-rules-for-fn key alist)))
;;   :hints (("Goal" :in-theory (enable get-rules-for-fn lookup-equal assoc-equal rule-alistp))))

(defthm stored-axe-rule-listp-of-get-rules-for-fn
  (implies (rule-alistp alist)
           (stored-axe-rule-listp (get-rules-for-fn key alist)))
  :hints (("Goal" :in-theory (enable get-rules-for-fn lookup-equal assoc-equal rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund count-rules-in-rule-alist-aux (rule-alist sum)
  (declare (xargs :guard (and (rule-alistp rule-alist)
                              (natp sum))
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rule-alist)
      sum
    (let* ((entry (first rule-alist))
           (stored-rules (cdr entry)))
      (count-rules-in-rule-alist-aux (rest rule-alist) (+ (len stored-rules) sum)))))

(defund count-rules-in-rule-alist (rule-alist)
  (declare (xargs :guard (rule-alistp rule-alist)))
  (count-rules-in-rule-alist-aux rule-alist 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check whether RULE-ALIST contains a rule named RULE-SYMBOL.
(defund rule-alist-containsp (rule-alist rule-symbol)
  (declare (xargs :guard (and (rule-alistp rule-alist)
                              (symbolp rule-symbol))
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rule-alist)
      nil
    (let* ((entry (first rule-alist))
           (stored-rules (cdr entry)))
      (or (rule-is-presentp rule-symbol stored-rules)
          (rule-alist-containsp (rest rule-alist) rule-symbol)))))

;; test: (equal (rule-alist-containsp (make-rule-alist '(car-cons cdr-cons) state) 'car-cons) t)
;; test: (equal (rule-alist-containsp (make-rule-alist '(car-cons cdr-cons) state) 'blah) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prints a message for all of the RULES not in the RULE-ALIST.
;; Return value is meaningless.
(defund print-missing-rules (rules rule-alist)
  (declare (xargs :guard (and (rule-alistp rule-alist)
                              (symbol-listp rules))
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rules)
      nil
    (b* ((rule (first rules))
         (presentp (rule-alist-containsp rule-alist rule))
         (- (and (not presentp)
                 (cw "(NOTE: Rule ~x0 is not (yet) in the rule-alist.)~%" rule))))
      (print-missing-rules (rest rules) rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
;; Returns a list of rule-names.
(defund rules-from-rule-alist (alist)
  (declare (xargs :guard (rule-alistp alist)
                  :verify-guards nil ;done below
                  ))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           ;; (fn (car entry))
           (stored-rules (cdr entry)))
      (union-eq (stored-rule-names stored-rules)
                (rules-from-rule-alist (rest alist))))))

(defthm symbol-listp-of-rules-from-rule-alist
  (implies (rule-alistp alist)
           (symbol-listp (rules-from-rule-alist alist)))
  :hints (("Goal" :in-theory (enable rules-from-rule-alist
                                     rule-alistp))))

(verify-guards rules-from-rule-alist
  :hints (("Goal" :in-theory (enable rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adds the AXE-RULES to the RULE-ALIST, perhaps removing duplicates among the rules for the relevant functions (if REMOVE-DUPLICATE-RULESP is non-nil).
;; The alist returned may have many entries for each function symbol, but we remove the shadowed entries in the caller.
;; If REMOVE-DUPLICATE-RULESP is non-nil we ensure that two rules with the same name are never added (we don't check for rules that are the same except for the name).
;; todo: might be faster to do duplicate checking at the end (or while sorting!)...
;; todo: optimize by using a property-list world?
(defund extend-unprioritized-rule-alist (axe-rules remove-duplicate-rulesp rule-alist)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (rule-alistp rule-alist))
                  :guard-hints (("Goal" :expand ((axe-rule-listp axe-rules)
                                                 (axe-rulep (car axe-rules)))))))
  (if (endp axe-rules)
      rule-alist
    (let* ((rule (first axe-rules))
           (lhs (rule-lhs rule))
           (fn (ffn-symb lhs))
           (stored-rules-for-fn (get-rules-for-fn fn rule-alist)) ;may be slow?
           (new-stored-rules-for-fn (if (and remove-duplicate-rulesp
                                             (rule-is-presentp (rule-symbol rule) stored-rules-for-fn))
                                        stored-rules-for-fn ; already there
                                      ;; not already there (or we are not checking):
                                      ;; todo: could use priorities and insert the rule in sorted order (faster to merge sort at the end?)
                                      (cons (make-stored-rule (fargs lhs) (rule-hyps rule) (rule-symbol rule) (rule-rhs rule))
                                            stored-rules-for-fn)))
           (rule-alist (acons-fast ;-unique       ;;now we uniquify the alist at the end
                         fn new-stored-rules-for-fn rule-alist)))
      (extend-unprioritized-rule-alist (rest axe-rules) remove-duplicate-rulesp rule-alist))))

(local
 (defthm symbol-alistp-of-extend-unprioritized-rule-alist
   (implies (and (symbol-alistp acc)
                 (axe-rule-listp axe-rules))
            (symbol-alistp (extend-unprioritized-rule-alist axe-rules remove-duplicate-rulesp acc)))
   :hints (("Goal" :in-theory (enable extend-unprioritized-rule-alist axe-rulep ;yuck
                                      )))))

(local
 (defthm rule-alistp-of-extend-unprioritized-rule-alist
   (implies (and (rule-alistp acc)
                 (axe-rule-listp axe-rules))
            (rule-alistp (extend-unprioritized-rule-alist axe-rules remove-duplicate-rulesp acc)))
   :hints (("Goal"
            :induct t
            :expand ((axe-rulep (car axe-rules))
                     (axe-rule-listp axe-rules))
            :in-theory (enable rule-alistp extend-unprioritized-rule-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Would it make sense to sort the fns also (e.g., by frequency of occurrence)?
(defund sort-rules-for-each-function-symbol-by-priority (rule-alist priorities)
  (declare (xargs :guard (and (alistp priorities)
                              (rule-alistp rule-alist))
                  :verify-guards nil ;done below
                  ))
  (if (endp rule-alist)
      nil
    (let* ((entry (first rule-alist))
           (fn (car entry))
           (stored-rules (cdr entry)))
      (acons fn
             ;; TODO: Perhaps optimize if none of the rules have priorities (but that might change existing orderings)?:
             (merge-sort-by-rule-priority stored-rules priorities) ; todo: make this more stable (e.g., by sorting by rule name when the priorities are tied)
             (sort-rules-for-each-function-symbol-by-priority (rest rule-alist) priorities)))))

(local
 (defthm alistp-of-sort-rules-for-each-function-symbol-by-priority
   (implies (alistp rule-alist)
            (alistp (sort-rules-for-each-function-symbol-by-priority rule-alist priorities)))
   :hints (("Goal" :in-theory (enable  sort-rules-for-each-function-symbol-by-priority)))))

(verify-guards sort-rules-for-each-function-symbol-by-priority
  :hints (("Goal" :in-theory (enable rule-alistp rule-alistp-means-alistp))))

(local
 (defthm rule-alistp-of-sort-rules-for-each-function-symbol-by-priority
   (implies (rule-alistp rule-alist)
            (rule-alistp (sort-rules-for-each-function-symbol-by-priority rule-alist priorities)))
   :hints (("Goal" :in-theory (enable sort-rules-for-each-function-symbol-by-priority
                                      rule-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;speed this up when just adding a few rules?
(defund extend-rule-alist (axe-rules remove-duplicate-rulesp priorities rule-alist)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              ; (booleanp remove-duplicate-rulesp)
                              (alistp priorities)
                              (rule-alistp rule-alist))))
  (let* ((rule-alist (extend-unprioritized-rule-alist axe-rules remove-duplicate-rulesp rule-alist))
         (rule-alist (uniquify-alist-eq rule-alist))
         (rule-alist (if priorities
                         (sort-rules-for-each-function-symbol-by-priority rule-alist priorities)
                       ;; todo: continue sorting by name in this case, for predictability:
                       rule-alist)))
    rule-alist))

(defthm rule-alistp-of-extend-rule-alist
  (implies (and (rule-alistp rule-alist)
                (alistp priorities)
                (axe-rule-listp axe-rules))
           (rule-alistp (extend-rule-alist axe-rules remove-duplicate-rulesp priorities rule-alist)))
  :hints (("Goal" :in-theory (enable extend-rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a rule-alist from the given AXE-RULES (note that these are full axe-rules,
;; not rule-names).  TODO: Might be faster to first sort the rules by head
;; symbol, then remove dups, then use the fact that rules for the same symbol
;; are grouped together.
(defund make-rule-alist-simple (axe-rules remove-duplicate-rulesp priorities)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (alistp priorities))))
  (extend-rule-alist axe-rules remove-duplicate-rulesp priorities (empty-rule-alist)))

(defthm rule-alistp-of-make-rule-alist-simple
  (implies (and (axe-rule-listp axe-rules)
                (alistp priorities))
           (rule-alistp (make-rule-alist-simple axe-rules remove-duplicate-rulesp priorities)))
  :hints (("Goal" :in-theory (enable make-rule-alist-simple))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a rule-alist from the given RULE-NAMES, using priority information from WRLD.
;; Returns (mv erp rule-alist).
;todo: optimize this routine to not make the axe-rules first
;; Warning: If any of these rules have :rule-classes nil, ACL2 won't allow us to use them.
(defund make-rule-alist (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (b* (((mv erp axe-rules) (make-axe-rules rule-names wrld))
       ((when erp) (mv erp nil))
       (priorities (table-alist 'axe-rule-priorities-table wrld))
       )
    (if (not (alistp priorities))
        (prog2$ (er hard? 'make-rule-alist "Ill-formed priorities table.")
                (mv :bad-priorities-table nil))
      (mv (erp-nil)
          (make-rule-alist-simple axe-rules t priorities)))))

(defthm rule-alistp-of-mv-nth-1-of-make-rule-alist
  (implies (symbol-listp rule-names)
           (rule-alistp (mv-nth 1 (make-rule-alist rule-names wrld))))
  :hints (("Goal" :in-theory (enable make-rule-alist axe-rule-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a rule-alist.  Can throw an error but doesn't return erp.
(defund make-rule-alist! (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp rule-alist)
    (make-rule-alist rule-names wrld)
    (if erp
        (er hard? 'make-rule-alist! "Error making rule alist.")
      rule-alist)))

(defthm rule-alistp-of-make-rule-alist!
  (implies (symbol-listp rule-names)
           (rule-alistp (make-rule-alist! rule-names wrld)))
  :hints (("Goal" :in-theory (enable make-rule-alist!))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-alist).
(defund add-to-rule-alist (rule-names rule-alist wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (rule-alistp rule-alist)
                              (ilks-plist-worldp wrld))))
  (b* (((mv erp axe-rules) (make-axe-rules rule-names wrld))
       ((when erp) (mv erp nil))
       (priorities (table-alist 'axe-rule-priorities-table wrld)))
    (if (not (alistp priorities))
        (prog2$ (er hard? 'add-to-rule-alist "Ill-formed priorities table.")
                (mv :bad-priorities-table nil))
      (mv (erp-nil)
          (extend-rule-alist axe-rules t priorities rule-alist)))))

(defthm rule-alistp-of-mv-nth-1-of-add-to-rule-alist
  (implies (and (symbol-listp rule-names)
                (rule-alistp rule-alist)
                (ilks-plist-worldp wrld))
           (rule-alistp (mv-nth 1 (add-to-rule-alist rule-names rule-alist wrld))))
  :hints (("Goal" :in-theory (enable add-to-rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the rule-alist.  Does not return erp.
(defund add-to-rule-alist! (rule-names rule-alist wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (rule-alistp rule-alist)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp rule-alist)
    (add-to-rule-alist rule-names rule-alist wrld)
    (if erp
        (er hard? 'add-to-rule-alist! "Error adding to rule alist.")
      rule-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This takes axe-rules, not names, and is for the unusual case when the AXE-RULES do not correspond to theorems in the world.
;todo: would prefer to just pass in named formulas here, instead of axe-rules.
(defund extend-rule-alist2 (axe-rules rule-alist wrld)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (rule-alistp rule-alist)
                              (plist-worldp wrld))))
  (let ((priorities (table-alist 'axe-rule-priorities-table wrld)))
    (if (not (alistp priorities))
        (er hard? 'extend-rule-alist2 "Ill-formed priorities table.")
      (extend-rule-alist axe-rules t priorities rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Optimize to not re-cons if not needed.
(defund remove-from-rule-alist (rule-names rule-alist)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (rule-alistp rule-alist))
                  :verify-guards nil ;done below
                  ))
  (if (endp rule-alist)
      nil
    (let* ((entry (car rule-alist))
           (fn (car entry))
           (stored-rules (cdr entry)))
      (acons fn
             (remove-from-stored-rules rule-names stored-rules)
             (remove-from-rule-alist rule-names (rest rule-alist))))))

(defthm rule-alistp-of-remove-from-rule-alist
  (implies (rule-alistp rule-alist)
           (rule-alistp (remove-from-rule-alist rule-names rule-alist)))
  :hints (("Goal" :in-theory (enable remove-from-rule-alist rule-alistp))))

(verify-guards remove-from-rule-alist
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp
                                     stored-axe-rulep
                                     rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Begin material about rule-alist-lists

;;;
;;; all-rule-alistp
;;;

(defforall-simple rule-alistp) ; todo: simplify? ; todo: switch to a rule-alist-listp?
(verify-guards all-rule-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rule-alistsp (rule-alists)
  (declare (xargs :guard t))
  (if (not (consp rule-alists))
      (null rule-alists)
    (and (rule-alistp (first rule-alists))
         (rule-alistsp (rest rule-alists)))))

(defthm rule-alistp-of-car-when-rule-alistsp
  (implies (rule-alistsp rule-alists)
           (rule-alistp (car rule-alists)))
  :hints (("Goal" :in-theory (enable rule-alistsp))))

(defthm rule-alistsp-of-cdr-when-rule-alistsp
  (implies (rule-alistsp rule-alists)
           (rule-alistsp (cdr rule-alists)))
  :hints (("Goal" :in-theory (enable rule-alistsp))))

(defthm rule-alistsp-forward-to-true-listp
  (implies (rule-alistsp rule-alists)
           (true-listp rule-alists))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable rule-alistsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of rule-names.
(defund rules-from-rule-alists (alists)
  (declare (xargs :guard (and (all-rule-alistp alists)
                              (true-listp alists))))
  (if (endp alists)
      nil
    (union-eq (rules-from-rule-alist (first alists))
              (rules-from-rule-alists (rest alists)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only used in once, in equivalence checker.
(defund make-rule-alists-simple (rule-sets remove-duplicate-rulesp priorities)
  (declare (xargs :guard (and (axe-rule-setsp rule-sets)
                              (alistp priorities)
                              (booleanp remove-duplicate-rulesp))))
  (if (endp rule-sets)
      nil
    (cons (make-rule-alist-simple (first rule-sets) remove-duplicate-rulesp priorities)
          (make-rule-alists-simple (rest rule-sets) remove-duplicate-rulesp priorities))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-alists).
(defund make-rule-alists (rule-name-lists wrld)
  (declare (xargs :guard (and (symbol-list-listp rule-name-lists)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-name-lists)
      (mv (erp-nil) nil)
    (b* (((mv erp rule-alist)
          (make-rule-alist (first rule-name-lists) wrld))
         ((when erp) (mv erp nil))
         ((mv erp rule-alists)
          (make-rule-alists (rest rule-name-lists) wrld))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons rule-alist rule-alists)))))

(defthm true-listp-of-mv-nth-1-of-make-rule-alists
  (true-listp (mv-nth 1 (make-rule-alists rule-name-lists wrld)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable make-rule-alists))))

(defthm all-rule-alistp-of-mv-nth-1-of-make-rule-alists
  (implies (symbol-list-listp rule-name-lists)
           (all-rule-alistp (mv-nth 1 (make-rule-alists rule-name-lists wrld))))
  :hints (("Goal" :in-theory (enable make-rule-alists))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: would prefer to just pass in named formulas here
(defund extend-rule-alists2 (axe-rules rule-alists wrld)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (all-rule-alistp rule-alists)
                              (true-listp rule-alists)
                              (plist-worldp wrld))))
  (if (endp rule-alists)
      nil
    (cons (extend-rule-alist2 axe-rules (first rule-alists) wrld)
          (extend-rule-alists2 axe-rules (rest rule-alists) wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-alists).
(defund add-to-rule-alists (rule-names rule-alists wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (all-rule-alistp rule-alists)
                              (true-listp rule-alists)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-alists)
      (mv (erp-nil) nil)
    (b* (((mv erp rule-alist)
          (add-to-rule-alist rule-names (first rule-alists) wrld))
         ((when erp) (mv erp nil))
         ((mv erp rule-alists)
          (add-to-rule-alists rule-names (rest rule-alists) wrld))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons rule-alist rule-alists)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-from-rule-alists (rule-names rule-alists)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (all-rule-alistp rule-alists)
                              (true-listp rule-alists))))
  (if (endp rule-alists)
      nil
    (cons (remove-from-rule-alist rule-names (first rule-alists))
          (remove-from-rule-alists rule-names (rest rule-alists)))))

(defthm symbol-listp-of-rules-from-rule-alists
  (implies (all-rule-alistp alists)
           (symbol-listp (rules-from-rule-alists alists)))
  :hints (("Goal" :in-theory (enable rules-from-rule-alists))))
