; Limiting how many times a rule can fire
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

;; We could use a property list world for this, or a hash table, or a
;; fast-alist, but note that the limits alist is usually very small.

(include-book "stored-rules")
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/alists-light/acons-unique" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable assoc-equal)))

(local
 (defthm all-integerp-of-strip-cdrs-of-acons-unique
   (implies (and (all-integerp (strip-cdrs alist))
                 (integerp val))
            (all-integerp (strip-cdrs (acons-unique key val alist))))
   :hints (("Goal" :in-theory (enable acons-unique)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The rule-limits is an alist from rule names (symbols) to the number of
;; remaining tries allowed for each (natural numbers).  Usually LIMITS will be
;; nil, or at least a very small alist.
(defund rule-limitsp (limits)
  (declare (xargs :guard t))
  (and (symbol-alistp limits)
       ;; may go negative if we exhaust the limit when relieving hyps and then decrement once more:
       (all-integerp (strip-cdrs limits))))

(local
 (defthm rule-limitsp-forward-to-alistp
   (implies (rule-limitsp limits)
            (alistp limits))
   :hints (("Goal" :in-theory (enable rule-limitsp)))))

(local
 (defthmd integerp-of-cdr-of-assoc-equal-when-rule-limitsp
   (implies (and (rule-limitsp limits)
                 (assoc-equal rule limits))
            (integerp (cdr (assoc-equal rule limits))))
   :hints (("Goal" :in-theory (enable rule-limitsp assoc-equal)))))

(local
 (defthmd integerp-of-cdr-of-assoc-equal-when-rule-limitsp-type
   (implies (and (rule-limitsp limits)
                 (assoc-equal rule limits))
            (integerp (cdr (assoc-equal rule limits))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable rule-limitsp assoc-equal)))))

(local
 (defthm rule-limitsp-of-acons-unique
   (implies (and (rule-limitsp alist)
                 (symbolp key)
                 (integerp val))
            (rule-limitsp (acons-unique key val alist)))
   :hints (("Goal" :in-theory (enable acons-unique rule-limitsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check whether we can no longer apply the given STORED-RULE.
(defund limit-reachedp (stored-rule limits print)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep
                                                           integerp-of-cdr-of-assoc-equal-when-rule-limitsp-type
                                                           )))))
  (let* ((rule-symbol (stored-rule-symbol stored-rule))
         (res (assoc-eq rule-symbol limits)))
    (if (not res)
        nil ;limit not reached since there is no limit for this rule
      (let ((limit (cdr res)))
        (if (<= (the integer limit) 0) ; could even make it a fixnum...
            (prog2$ (and print (cw "(NOTE: Limit reached for rule ~x0.)~%" rule-symbol))
                    t)
          nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Decrements the limit for the supplied STORED-RULE by 1.
;; TODO: This repeats some work done in limit-reachedp.  But this may be called
;; much less often than limit-reachedp, since most rules have no limits.
(defund decrement-rule-limit (stored-rule limits)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep
                                                           rule-limitsp)))))
  (let* ((rule-symbol (stored-rule-symbol stored-rule))
         (res (assoc-eq rule-symbol limits)))
    (if (not res)
        limits ; no limit for this rule
      (let ((limit (cdr res)))
        ;; We use acons-unique here, to keep the LIMITS from growing.  Note
        ;; that limit-reachedp may be called many times, so we want to keep the
        ;; LIMITS small.
        (acons-unique-eq rule-symbol (+ -1 (the integer limit)) limits)))))

(defthm rule-limitsp-of-decrement-rule-limit
  (implies (and (rule-limitsp limits)
                ;; (not (limit-reachedp stored-rule limits))
                (stored-axe-rulep stored-rule))
           (rule-limitsp (decrement-rule-limit stored-rule limits)))
  :hints (("Goal" :in-theory (enable decrement-rule-limit
                                     integerp-of-cdr-of-assoc-equal-when-rule-limitsp-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extend LIMITS by adding the given LIMIT for all of the given RULE-NAMES.
(defund add-limit-for-rules (rule-names limit limits)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (natp limit)
                              (rule-limitsp limits))
                  :verify-guards nil ; done below
                  ))
  (if (endp rule-names)
      limits
    (add-limit-for-rules (rest rule-names) limit (acons-unique-eq (first rule-names) limit limits))))

(defthm rule-limitsp-of-add-limit-for-rules
  (implies (and (symbol-listp rule-names)
                (natp limit)
                (rule-limitsp limits))
           (rule-limitsp (add-limit-for-rules rule-names limit limits)))
  :hints (("Goal" :in-theory (enable add-limit-for-rules rule-limitsp))))

(verify-guards add-limit-for-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund limit-for-rule (rule-name limits)
  (declare (xargs :guard (and (symbolp rule-name)
                              (rule-limitsp limits))))
  (cdr (assoc-eq rule-name limits)))
