; Limiting how many times a rule can fire
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
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
(include-book "kestrel/alists-light/acons-unique" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(local (in-theory (disable assoc-equal natp)))

(local
 (defthm nat-listp-of-strip-cdrs-of-acons-unique
   (implies (and (nat-listp (strip-cdrs alist))
                 (natp val))
            (nat-listp (strip-cdrs (acons-unique key val alist))))
   :hints (("Goal" :in-theory (enable acons-unique)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A rule-limits is an alist from rule names (symbols) to the number of
;; remaining tries allowed for each (natural numbers).  Usually LIMITS will be
;; nil, or at least a very small alist, since usually few rules are limited
;; and acons-unique-eq keeps the alist small.
(defund rule-limitsp (limits)
  (declare (xargs :guard t))
  (and (symbol-alistp limits)
       (no-duplicatesp-eq (strip-cars limits))
       (nat-listp (strip-cdrs limits))))

(local
 (defthm rule-limitsp-forward-to-alistp
   (implies (rule-limitsp limits)
            (alistp limits))
   :hints (("Goal" :in-theory (enable rule-limitsp)))))

(local
 (defthmd natp-of-cdr-of-assoc-equal-when-rule-limitsp
   (implies (and (rule-limitsp limits)
                 (assoc-equal rule limits))
            (natp (cdr (assoc-equal rule limits))))
   :hints (("Goal" :in-theory (enable rule-limitsp assoc-equal)))))

(local
 (defthmd natp-of-cdr-of-assoc-equal-when-rule-limitsp-type
   (implies (and (rule-limitsp limits)
                 (assoc-equal rule limits))
            (natp (cdr (assoc-equal rule limits))))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable rule-limitsp assoc-equal)))))

;move
(local
 (defthm member-equal-of-strip-cars-of-acons-unique
   (iff (member-equal key (strip-cars (acons-unique key2 val alist)))
        (or (member-equal key (strip-cars alist))
            (equal key key2)))
   :hints (("Goal" :in-theory (enable acons-unique)))))

(local
 (defthm rule-limitsp-of-acons-unique
   (implies (and (rule-limitsp alist)
                 (symbolp key)
                 (natp val))
            (rule-limitsp (acons-unique key val alist)))
   :hints (("Goal" :in-theory (enable acons-unique rule-limitsp)))))

(defthm rule-limitsp-of-cons
  (equal (rule-limitsp (cons pair limits))
         (and (consp pair)
              (symbolp (car pair))
              (not (member-equal (car pair) (strip-cars limits)))
              (natp (cdr pair))
              (rule-limitsp limits)))
   :hints (("Goal" :in-theory (enable rule-limitsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns t, ni, or :not-yet.
;; This part is not inlined but is only called if there are limits.
;; TODO: Optimize (avoid the assoc-eq by just walking down the list)
(defund limit-reached-aux (stored-rule limits print)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits)
                              limits ; may not be needed
                              )
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep
                                                           natp-of-cdr-of-assoc-equal-when-rule-limitsp-type
                                                           )))))
  (let* ((rule-symbol (stored-rule-symbol stored-rule))
         (res (assoc-eq rule-symbol limits)))
    (if (not res)
        nil ;  no limit for this rule
      (let ((limit (cdr res)))
        (if (= 0 (the (integer 0 *) limit)) ; todo: make it a fixnum
            (prog2$ (and print (cw "(NOTE: Limit reached for rule ~x0.)~%" rule-symbol))
                    ;; we have reached the limit (no rule applications left):
                    t)
          ;; There is a limit, but we have not reached it:
          :not-yet)))))

;; Checks whether the limit is reached (0 rule applications left).
;; Returns one of the following:
;;   nil      -- no limit for this rule
;;   :not-yet -- there is a limit for this rule, but we have not reached it
;;   t        -- the limit has been reached
(defund-inline limit-reached (stored-rule limits print)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits))))
  (and limits
       (limit-reached-aux stored-rule limits print)))

;; The print arg is logically irrelevant.
(defthm limit-reached-normalize-print-arg
  (implies (syntaxp (not (equal *nil* print))) ; prevents loops
           (equal (limit-reached stored-rule limits print)
                  (limit-reached stored-rule limits nil)))
  :hints (("Goal" :in-theory (enable limit-reached limit-reached-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Decrements the limit for the supplied STORED-RULE by 1.
;; TODO: This repeats some work done in limit-reached.  But this may be called
;; much less often than limit-reached, since most rules have no limits.
;; TODO: Optimize: avoid 2 list walks Optimize (avoid assoc-eq followed bt acons-unique-eq).
(defund decrement-rule-limit (stored-rule limits)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule)
                              (rule-limitsp limits)
                              ;; can't decrement if no limit or limit already reached:
                              (equal (limit-reached stored-rule limits nil) :not-yet))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep
                                                           rule-limitsp
                                                           integerp-when-natp
                                                           limit-reached
                                                           limit-reached-aux)))))
  (let* ((rule-symbol (stored-rule-symbol stored-rule))
         (res (assoc-eq rule-symbol limits)))
    (let ((limit (cdr res))) ; we know res is a cons, due to the guard
      ;; We use acons-unique here, to keep the LIMITS from growing.  Note
      ;; that limit-reached may be called many times, so we want to keep the
      ;; LIMITS small.
      (acons-unique-eq rule-symbol (+ -1 (the (integer 1 *) limit)) limits))))

(defthm rule-limitsp-of-decrement-rule-limit
  (implies (and (rule-limitsp limits)
                ;; (not (limit-reached stored-rule limits))
                (stored-axe-rulep stored-rule)
                (equal (limit-reached stored-rule limits nil) :not-yet))
           (rule-limitsp (decrement-rule-limit stored-rule limits)))
  :hints (("Goal" :in-theory (enable decrement-rule-limit
                                     natp-of-cdr-of-assoc-equal-when-rule-limitsp-type
                                     limit-reached
                                     limit-reached-aux))))

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
  :hints (("Goal" :in-theory (enable add-limit-for-rules rule-limitsp no-duplicatesp-equal-of-strip-cars-of-acons-unique))))

(verify-guards add-limit-for-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Can help determine how many times a rule fired, if we also know the initial
;; limit for the rule.
;; restrict to the case where we know there is an entry in the alist?
(defund limit-for-rule (rule-name limits)
  (declare (xargs :guard (and (symbolp rule-name)
                              (rule-limitsp limits))))
  (cdr (assoc-eq rule-name limits)))

(defthm natp-of-limit-for-rule
  (implies (and (rule-limitsp limits)
                ;; not nil:
                (limit-for-rule rule-name limits))
           (natp (limit-for-rule rule-name limits)))
  :hints (("Goal" :in-theory (enable limit-for-rule rule-limitsp))))
