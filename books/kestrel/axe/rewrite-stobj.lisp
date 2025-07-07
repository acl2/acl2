; A stobj to gather data structures used in rewriting
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "interpreted-function-alistp")
(include-book "rule-alists")

;; Note that none of the information in the rewrite-stobj changes during
;; rewriting, so the stobj does not have to be returned by the functions in the
;; main rewriter clique.

;; See also rewrite-stobj2.lisp, for a stobj that includes fields that do change.

(defund normalize-xors-optionp (n)
  (declare (xargs :guard t))
  ;; coerce to boolean (allows us to use MBT):
  (if (member-eq n '(t nil :compact)) t nil))

; todo: eventually remove?
(defthm normalize-xors-optionp-when-booleanp
  (implies (booleanp x)
           (normalize-xors-optionp x))
  :hints (("Goal" :in-theory (enable normalize-xors-optionp booleanp))))

;; TODO: Consider adding more things to this?
(defstobj+ rewrite-stobj
  ;; Functions that are known to be boolean in the current world:
  (known-booleans :type (satisfies symbol-listp) :initially nil)
  ;; Names of rules we are monitoring:
  (monitored-symbols :type (satisfies symbol-listp) :initially nil)
  ;; Functions for which we suppress the warning about an unevaluated ground application:
  (no-warn-ground-functions :type (satisfies symbol-listp) :initially nil)
  ;; How much to print while rewriting:
  (print :type (satisfies print-levelp) :initially nil)
  ;; Whether to use our special-purpose code to normalize nests of XORs:
  (normalize-xors :type (satisfies normalize-xors-optionp) :initially nil)
  ;; Definitions of functions not built into the evaluator:
  ;; TODO: Require this alist to be complete?
  (interpreted-function-alist :type (satisfies interpreted-function-alistp) :initially nil)
  ;; Rules to be applied when rewriting, analogous to a rule-alist:
  (rule-db :type (hash-table eq 1024 (satisfies stored-axe-rule-listp)) :initially nil) ; size=1024 is just a hint
  ;; Functions to elide when printing failure info for monitored rules (e.g.,
  ;; when printing the refined-assumption-alist, which can include large
  ;; terms):
  (fns-to-elide :type (satisfies symbol-listp) :initially nil)
  :inline t
  ;; Changes the names to be get-XXX and put-XXX:
  :renaming ((known-booleans get-known-booleans)
             (update-known-booleans put-known-booleans)
             (monitored-symbols get-monitored-symbols)
             (no-warn-ground-functions get-no-warn-ground-functions)
             (update-monitored-symbols put-monitored-symbols)
             (update-no-warn-ground-functions put-no-warn-ground-functions)
             (common-lisp::printp printp) ; can we avoid having defstobj define printp, which just calls print-levelp?
             (common-lisp::print get-print)
             (common-lisp::update-print put-print)
             (normalize-xors get-normalize-xors)
             (update-normalize-xors put-normalize-xors)
             (interpreted-function-alistp interpreted-function-alist-fieldp) ; since interpreted-function-alistp is already used!  can we suppress the recognizer in this case?
             (interpreted-function-alist get-interpreted-function-alist)
             (update-interpreted-function-alist put-interpreted-function-alist)
             ;; (rule-alistp rule-alist-fieldp) ; since rule-alistp is already used!  can we suppress the recognizer in this case?
             ;; (rule-db get-rule-db)
             ;; (update-rule-db put-rule-db)
             (fns-to-elide get-fns-to-elide)
             (update-fns-to-elide put-fns-to-elide)))

(in-theory (disable rule-db-get rule-db-put rule-db-clear)) ; todo: defstobj+ should do this

;; todo defstobj+ should do this
(local
  (defthm rule-dbp-of-cons-of-cons
    (equal (rule-dbp (cons (cons k v) rule-db))
           (and (stored-axe-rule-listp v)
                (rule-dbp rule-db)))
    :hints (("Goal" :in-theory (enable rule-dbp)))))

;; todo defstobj+ should do this
(local
  (defthm rewrite-stobjp-of-rule-db-put
    (implies (and (symbolp k)
                  (stored-axe-rule-listp v)
                  (rewrite-stobjp rewrite-stobj))
             (rewrite-stobjp (rule-db-put k v rewrite-stobj)))
    :hints (("Goal" :in-theory (enable rule-db-put rewrite-stobjp)))))

(local
  (defthm rewrite-stobjp-of-rule-db-clear
    (implies (rewrite-stobjp rewrite-stobj)
             (rewrite-stobjp (rule-db-clear rewrite-stobj)))
    :hints (("Goal" :in-theory (enable rule-db-clear rewrite-stobjp)))))

;todo: auto-generate
(defthm get-normalize-xors-of-rule-db-put
  (equal (get-normalize-xors (rule-db-put k v rewrite-stob))
         (get-normalize-xors rewrite-stob))
  :hints (("Goal" :in-theory (enable rule-db-put get-normalize-xors))))

;todo: auto-generate
(defthm get-normalize-xors-of-rule-db-clear
  (equal (get-normalize-xors (rule-db-clear rewrite-stob))
         (get-normalize-xors rewrite-stob))
  :hints (("Goal" :in-theory (enable rule-db-clear get-normalize-xors))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In case we turn off tau.
(defthm true-listp-of-get-monitored-symbols
  (implies (rewrite-stobjp rewrite-stobj)
           (true-listp (get-monitored-symbols rewrite-stobj)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rewrite-stobjp get-monitored-symbols))))

;; In case we turn off tau.
(defthm true-listp-of-get-no-warn-ground-functions
  (implies (rewrite-stobjp rewrite-stobj)
           (true-listp (get-no-warn-ground-functions rewrite-stobj)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable rewrite-stobjp get-no-warn-ground-functions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthm stored-axe-rule-listp-of-cdr-of-hons-assoc-equal
    (implies (rule-dbp rule-db)
             (stored-axe-rule-listp (cdr (hons-assoc-equal fn rule-db))))
    :hints (("Goal" :in-theory (enable rule-dbp hons-assoc-equal)))))

(defthm stored-axe-rule-listp-of-rule-db-get
  (implies (rewrite-stobjp rewrite-stobj)
           (stored-axe-rule-listp (rule-db-get fn rewrite-stobj)))
  :hints (("Goal" :in-theory (enable rewrite-stobjp rule-db-get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund load-rule-db-aux (rule-alist rewrite-stobj)
  (declare (xargs :guard (rule-alistp rule-alist)
                  :stobjs rewrite-stobj
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rule-alist)
      rewrite-stobj
    (let* ((entry (first rule-alist))
           (fn (car entry))
           (stored-rules (cdr entry))
           (rewrite-stobj (rule-db-put fn stored-rules rewrite-stobj)))
      (load-rule-db-aux (rest rule-alist) rewrite-stobj))))

(local
  (defthm rewrite-stobjp-of-load-rule-db-aux
    (implies (and (rule-alistp rule-alist)
                  (rewrite-stobjp rewrite-stobj))
             (rewrite-stobjp (load-rule-db-aux rule-alist rewrite-stobj)))
    :hints (("Goal" :in-theory (enable load-rule-db-aux rule-alistp)))))

(local
  (defthm get-normalize-xors-of-load-rule-db-aux
    (equal (get-normalize-xors (load-rule-db-aux rule-alist rewrite-stob))
           (get-normalize-xors rewrite-stob))
    :hints (("Goal" :in-theory (enable  load-rule-db-aux)))))

;; Loads the RULE-ALIST into the rule-db hash table in stobj.
;; The clearing may not always be needed.
(defund load-rule-db (rule-alist rewrite-stobj)
  (declare (xargs :guard (rule-alistp rule-alist)
                  :stobjs rewrite-stobj))
  (let* ((rewrite-stobj (rule-db-clear rewrite-stobj))
         (rewrite-stobj (load-rule-db-aux rule-alist rewrite-stobj)))
    rewrite-stobj))

(defthm rewrite-stobjp-of-load-rule-db
  (implies (and (rule-alistp rule-alist)
                (rewrite-stobjp rewrite-stobj))
           (rewrite-stobjp (load-rule-db rule-alist rewrite-stobj)))
  :hints (("Goal" :in-theory (enable load-rule-db))))

(defthm get-normalize-xors-of-load-rule-db
  (equal (get-normalize-xors (load-rule-db rule-alist rewrite-stob))
         (get-normalize-xors rewrite-stob))
  :hints (("Goal" :in-theory (enable load-rule-db))))
