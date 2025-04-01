; The "stored form" of Axe's rewrite rules
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

(include-book "axe-rules")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/split-list-fast-defs" :dir :system)
(local (include-book "kestrel/utilities/split-list-fast" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; Stored-rules are what is stored in rule-alists / rule-dbs.

;; todo: the guards of these should be stored-axe-rulep:

;; See also axe-rulep.  A stored rule has the form (lhs-args hyps rule-symbol
;; . rhs).  The top function symbol of the LHS is not stored.
(defund stored-axe-rulep (item)
  (declare (xargs :guard t))
  (and (<= 3 (len item)) ;the final cdr is the rhs
       (let ((lhs-args (first ;stored-rule-lhs-args
                         item))
             (hyps (second ;stored-rule-hyps
                     item))
             (rhs (cdddr ;stored-rule-rhs
                    item))
             (rule-symbol (third ;stored-rule-symbol
                            item)))
         (and (pseudo-term-listp lhs-args) ;should be lambda-free
              (axe-rule-hyp-listp hyps)
              (bound-vars-suitable-for-hypsp (free-vars-in-terms lhs-args) hyps)
              (pseudo-termp rhs)
              (subsetp-equal (free-vars-in-term rhs)
                             (bound-vars-after-hyps (free-vars-in-terms lhs-args) hyps))
              (symbolp rule-symbol)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline stored-rule-lhs-args (stored-axe-rule)
  (declare (xargs :guard (stored-axe-rulep stored-axe-rule)
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep)))))
  (first stored-axe-rule))

(defund-inline stored-rule-hyps (stored-axe-rule)
  (declare (xargs :guard (stored-axe-rulep stored-axe-rule)
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep)))))
  (second stored-axe-rule))

(defund-inline stored-rule-symbol (stored-axe-rule)
  (declare (xargs :guard (stored-axe-rulep stored-axe-rule)
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep)))))
  (third stored-axe-rule))

(defund-inline stored-rule-rhs (stored-axe-rule)
  (declare (xargs :guard (stored-axe-rulep stored-axe-rule)
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep)))))
  (cdddr stored-axe-rule))

(defthm pseudo-term-listp-of-stored-rule-lhs-args
  (implies (stored-axe-rulep rule)
           (pseudo-term-listp (stored-rule-lhs-args rule)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep stored-rule-lhs-args))))

(defthm axe-rule-hyp-listp-of-stored-rule-hyps
  (implies (stored-axe-rulep rule)
           (axe-rule-hyp-listp (stored-rule-hyps rule)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep stored-rule-hyps))))

(defthm symbolp-of-stored-rule-symbol
  (implies (stored-axe-rulep item)
           (symbolp (stored-rule-symbol item)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep stored-rule-symbol))))

(defthm pseudo-termp-of-stored-rule-rhs
  (implies (stored-axe-rulep item)
           (pseudo-termp (stored-rule-rhs item)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep stored-rule-rhs))))

(defthm bound-vars-suitable-for-hypsp-of-var-in-terms-of-stored-rule-lhs-args-and-stored-rule-hyps
  (implies (stored-axe-rulep stored-rule)
           (bound-vars-suitable-for-hypsp (free-vars-in-terms (stored-rule-lhs-args stored-rule))
                                          (stored-rule-hyps stored-rule)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep stored-rule-hyps stored-rule-lhs-args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-stored-rule (lhs-args hyps rule-symbol rhs)
  (declare (xargs :guard (and (pseudo-term-listp lhs-args) ;should be lambda-free
                              (axe-rule-hyp-listp hyps)
                              (pseudo-termp rhs) ;todo: disallow free vars
                              (symbolp rule-symbol))))
  (list* lhs-args ;does not include the leading function symbol (we'll always know it)
         hyps     ;hyps are the next-most-frequenty-accessed part of the rule
         rule-symbol
         rhs))

(defthm stored-axe-rulep-of-make-stored-rule
  (equal (stored-axe-rulep (make-stored-rule lhs-args hyps rule-symbol rhs))
         (and (pseudo-term-listp lhs-args)
              (axe-rule-hyp-listp hyps)
              (bound-vars-suitable-for-hypsp (free-vars-in-terms lhs-args) hyps)
              (pseudo-termp rhs)
              (subsetp-equal (free-vars-in-term rhs)
                             (bound-vars-after-hyps (free-vars-in-terms lhs-args) hyps))
              (symbolp rule-symbol)))
  :hints (("Goal" :in-theory (enable make-stored-rule
                                     stored-axe-rulep
                                     stored-rule-lhs-args
                                     stored-rule-rhs
                                     stored-rule-symbol
                                     stored-rule-hyps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: split out?
;; Recognizes a true-list of stored-axe-rules.
(defund stored-axe-rule-listp (rules)
  (declare (xargs :guard t))
  (if (atom rules)
      (null rules)
    (and (stored-axe-rulep (first rules))
         (stored-axe-rule-listp (rest rules)))))

(defthm stored-axe-rule-listp-forward-to-true-listp
  (implies (stored-axe-rule-listp rules)
           (true-listp rules))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp))))

(defthm stored-axe-rulep-of-car
  (implies (stored-axe-rule-listp rules)
           (equal (stored-axe-rulep (car rules))
                  (consp rules)))
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp))))

(defthm stored-axe-rule-listp-of-cdr
  (implies (stored-axe-rule-listp rules)
           (stored-axe-rule-listp (cdr rules)))
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp))))

(defthm stored-axe-rule-listp-of-cons
  (equal (stored-axe-rule-listp (cons rule rules))
         (and (stored-axe-rulep rule)
              (stored-axe-rule-listp rules)))
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: For predictability, we could secondarily sort by name, using symbol<.
(defun higher-priority (stored-rule1 stored-rule2 priorities)
  (declare (xargs :guard (and (stored-axe-rulep stored-rule1)
                              (stored-axe-rulep stored-rule2)
                              (alistp priorities))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rulep)))))
  (let* ((rule-symbol1 (stored-rule-symbol stored-rule1))
         (rule-symbol2 (stored-rule-symbol stored-rule2))
         ;;drop the rfixes?
         (priority1 (rfix (lookup-eq rule-symbol1 priorities))) ;fixme non-rational priorities should be errors? or is nil the default?
         (priority2 (rfix (lookup-eq rule-symbol2 priorities))))
    (< priority1 priority2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund merge-by-rule-priority (stored-rules1 stored-rules2 acc priorities)
  (declare (xargs :measure (+ (len stored-rules1) (len stored-rules2))
                  :guard (and (alistp priorities)
                              (stored-axe-rule-listp stored-rules1)
                              (stored-axe-rule-listp stored-rules2)
                              (true-listp acc))))
  ;;null would be faster than atom?  but then this wouldn't terminate?
  (cond ((atom stored-rules1) (revappend acc stored-rules2)) ;fixme use endp? or null (might need to use mbe to put null here)
        ((atom stored-rules2) (revappend acc stored-rules1)) ;fixme use endp? or null (might need to use mbe to put null here)
        ((higher-priority (first stored-rules1) (first stored-rules2) priorities)
         (merge-by-rule-priority (rest stored-rules1)
                                 stored-rules2
                                 (cons (first stored-rules1) acc) ;fixme redoes the "first" from above
                                 priorities))
        (t (merge-by-rule-priority stored-rules1 (rest stored-rules2)
                                   (cons (first stored-rules2) acc) ;fixme redoes the "first" from above
                                   priorities))))

;drop?
(local
  (defthm true-listp-of-merge-by-rule-priority
    (implies (and (true-listp l1)
                  (true-listp l2)
                  (true-listp acc))
             (true-listp (merge-by-rule-priority l1 l2 acc priorities)))
    :hints (("Goal" :in-theory (enable merge-by-rule-priority)))))

(local
  (defthm stored-axe-rule-listp-of-merge-by-rule-priority
    (implies (and (stored-axe-rule-listp l1)
                  (stored-axe-rule-listp l2)
                  (stored-axe-rule-listp acc))
             (stored-axe-rule-listp (merge-by-rule-priority l1 l2 acc priorities)))
    :hints (("Goal" :in-theory (enable merge-by-rule-priority)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: generic theorem saying merge-sort preserves foo-listp?

;todo: use defmergesort?
;; TODO: For stability, consider comparing the rule names if there priorities are the same.
;todo: add stored-rules to the name
(defun merge-sort-by-rule-priority (stored-rules priorities)
  (declare (xargs :measure (len stored-rules)
                  :hints (("Goal" :in-theory (disable len)))
                  :guard (and (alistp priorities)
                              (stored-axe-rule-listp stored-rules))
                  :verify-guards nil ;done below
                  ))
  (if (endp stored-rules) ;combine these first 2 cases?
      stored-rules
    (if (endp (cdr stored-rules))
        stored-rules
      (mv-let (l1 l2)
              (split-list-fast stored-rules)
              (merge-by-rule-priority (merge-sort-by-rule-priority l1 priorities)
                                      (merge-sort-by-rule-priority l2 priorities)
                                      nil
                                      priorities)))))

;; make these local?:
;defforall could do these too?
(local
  (defthm stored-axe-rule-listp-of-mv-nth-0-of-split-list-fast-aux
    (implies (and (stored-axe-rule-listp lst)
                  (stored-axe-rule-listp acc)
                  (<= (len tail) (len lst)))
             (stored-axe-rule-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))))

(local
  (defthm stored-axe-rule-listp-of-mv-nth-0-of-split-list-fast
    (implies (stored-axe-rule-listp lst)
             (stored-axe-rule-listp (mv-nth 0 (split-list-fast lst))))
    :hints (("Goal" :in-theory (enable split-list-fast)))))

(local
  (defthm stored-axe-rule-listp-of-mv-nth-1-of-split-list-fast-aux
    (implies (stored-axe-rule-listp lst)
             (stored-axe-rule-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))))

(local
  (defthm stored-axe-rule-listp-of-mv-nth-1-split-list-fast
    (implies (stored-axe-rule-listp lst)
             (stored-axe-rule-listp (mv-nth 1 (split-list-fast lst))))
    :hints (("Goal" :in-theory (enable split-list-fast)))))

(verify-guards merge-sort-by-rule-priority
  :hints (("Goal" :induct (merge-sort-by-rule-priority stored-rules priorities))))

(defthm stored-axe-rule-listp-of-merge-sort-by-rule-priority
  (implies (stored-axe-rule-listp stored-rules)
           (stored-axe-rule-listp (merge-sort-by-rule-priority stored-rules priorities)))
  :hints (("Goal" :in-theory (enable merge-sort-by-rule-priority))))

;drop?
(defthmd true-listp-of-merge-sort-by-rule-priority
  (implies (true-listp stored-rules)
           (true-listp (merge-sort-by-rule-priority stored-rules priorities)))
  :hints (("Goal" :in-theory (enable merge-sort-by-rule-priority))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename stored-rule-is-presentp?
(defund rule-is-presentp (rule-symbol stored-axe-rules)
  (declare (xargs :guard (and (stored-axe-rule-listp stored-axe-rules)
                              (symbolp rule-symbol))
                  :guard-hints (("Goal" :expand ((stored-axe-rule-listp stored-axe-rules))
                                 :in-theory (enable stored-axe-rule-listp stored-axe-rulep))) ;yuck
                  ))
  (if (endp stored-axe-rules) ;use endp?
      nil
    (let ((stored-axe-rule (first stored-axe-rules)))
      (if (eq rule-symbol (stored-rule-symbol stored-axe-rule))
          t
        (rule-is-presentp rule-symbol (rest stored-axe-rules))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-from-stored-rules (rule-names-to-remove stored-rules)
  (declare (xargs :guard (and (symbol-listp rule-names-to-remove)
                              (stored-axe-rule-listp stored-rules))
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rule-listp stored-axe-rulep)))))
  (if (endp stored-rules)
      nil
    (let ((stored-rule (first stored-rules)))
      (if (member-eq (stored-rule-symbol stored-rule) rule-names-to-remove)
          (remove-from-stored-rules rule-names-to-remove (rest stored-rules))
        (cons stored-rule (remove-from-stored-rules rule-names-to-remove (rest stored-rules)))))))

(defthm stored-axe-rule-listp-of-remove-from-stored-rules
  (implies (stored-axe-rule-listp stored-rules)
           (stored-axe-rule-listp (remove-from-stored-rules rule-names stored-rules)))
  :hints (("Goal" :in-theory (enable remove-from-stored-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun stored-rule-names (stored-rules)
  (declare (xargs :guard (stored-axe-rule-listp stored-rules)
                  :guard-hints (("Goal" :in-theory (enable stored-axe-rule-listp stored-axe-rulep)))))
  (if (endp stored-rules)
      nil
    (cons (stored-rule-symbol (first stored-rules))
          (stored-rule-names (rest stored-rules)))))

(defthm symbol-listp-of-stored-rule-names
  (implies (stored-axe-rule-listp rules)
           (symbol-listp (stored-rule-names rules)))
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp stored-axe-rulep))))
