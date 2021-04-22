; Axe's rewrite rules in stored form
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-rules")
(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/utilities/split-list-fast" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

;;;
;;; stored-rules
;;;

;these are what are stored in rule-alists
(defund make-stored-rule (lhs-args hyps rule-symbol rhs)
  (declare (xargs :guard (and (pseudo-term-listp lhs-args) ;should be lambda-free
                              (axe-rule-hyp-listp hyps)
                              (pseudo-termp rhs) ;todo: disallow free vars
                              (symbolp rule-symbol))))
  (list* lhs-args ;does not include the leading function symbol (we'll always know it)
         hyps     ;hyps are the next-most-frequenty-accessed part of the rule
         rule-symbol
         rhs))

(defund-inline stored-rule-lhs-args (stored-axe-rule)
  (declare (xargs :guard (<= 3 (len stored-axe-rule))))
  (first stored-axe-rule))

(defund-inline stored-rule-hyps (stored-axe-rule)
  (declare (xargs :guard (<= 3 (len stored-axe-rule))))
  (second stored-axe-rule))

(defund-inline stored-rule-symbol (stored-axe-rule)
  (declare (xargs :guard (<= 3 (len stored-axe-rule))))
  (third stored-axe-rule))

(defund-inline stored-rule-rhs (stored-axe-rule)
  (declare (xargs :guard (<= 3 (len stored-axe-rule))))
  (cdddr stored-axe-rule))

;; See also axe-rulep.  A stored rule has the form (lhs-args hyps rule-symbol
;; . rhs).  The top function symbol of the LHS is not stored.
(defund stored-axe-rulep (item)
  (declare (xargs :guard t))
  (and (<= 3 (len item)) ;the final cdr is the rhs
       (let ((lhs-args (stored-rule-lhs-args item))
             (hyps (stored-rule-hyps item))
             (rhs (stored-rule-rhs item))
             (rule-symbol (stored-rule-symbol item)))
         (and (pseudo-term-listp lhs-args) ;should be lambda-free
              (axe-rule-hyp-listp hyps)
              (bound-vars-suitable-for-hypsp (vars-in-terms lhs-args) hyps)
              (pseudo-termp rhs)
              (subsetp-equal (vars-in-term rhs)
                             (bound-vars-after-hyps (vars-in-terms lhs-args) hyps))
              (symbolp rule-symbol)))))

(defthm stored-axe-rulep-of-make-stored-rule
  (equal (stored-axe-rulep (make-stored-rule lhs-args hyps rule-symbol rhs))
         (and (pseudo-term-listp lhs-args)
              (axe-rule-hyp-listp hyps)
              (bound-vars-suitable-for-hypsp (vars-in-terms lhs-args) hyps)
              (pseudo-termp rhs)
              (subsetp-equal (vars-in-term rhs)
                             (bound-vars-after-hyps (vars-in-terms lhs-args) hyps))
              (symbolp rule-symbol)))
  :hints (("Goal" :in-theory (enable make-stored-rule
                                     stored-axe-rulep
                                     stored-rule-lhs-args
                                     stored-rule-rhs
                                     stored-rule-symbol
                                     stored-rule-hyps))))

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
  :hints (("Goal" :in-theory (enable stored-axe-rulep))))

(defthm pseudo-termp-of-stored-rule-rhs
  (implies (stored-axe-rulep item)
           (pseudo-termp (stored-rule-rhs item)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep))))

;;;
;;; all-stored-axe-rulep
;;;

;todo: split out?
(defforall all-stored-axe-rulep (items) (stored-axe-rulep items))
(verify-guards all-stored-axe-rulep)

;; ;fixme the defforall could do this?
;; ;make it an equality?
;; (defthm all-stored-axe-rulep-of-revappend
;;   (implies (and (all-stored-axe-rulep x)
;;                 (all-stored-axe-rulep y))
;;            (all-stored-axe-rulep (revappend x y)))
;;   :hints (("Goal" :in-theory (enable revappend))))

;; TODO: For predictability, we could secondarily sort by name, using symbol-<.
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

(defund merge-by-rule-priority (stored-rules1 stored-rules2 acc priorities)
  (declare (xargs :measure (+ (len stored-rules1) (len stored-rules2))
                  :guard (and (alistp priorities)
                              (all-stored-axe-rulep stored-rules1)
                              (all-stored-axe-rulep stored-rules2)
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

(defthm true-listp-of-merge-by-rule-priority
  (implies (and (true-listp l1)
                (true-listp l2)
                (true-listp acc))
           (true-listp (merge-by-rule-priority l1 l2 acc priorities)))
  :hints (("Goal" :in-theory (enable merge-by-rule-priority))))

;fixme generic theorem saying merge-sort preserves foo-listp?

;todo: use defmergesort?
(defun merge-sort-by-rule-priority (stored-rules priorities)
  (declare (xargs :measure (len stored-rules)
                  :hints (("Goal" :in-theory (e/d () (len))))
                  :guard (and (alistp priorities)
                              (true-listp stored-rules)
                              (all-stored-axe-rulep stored-rules))
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

;defforall could do these too?
(defthm all-stored-axe-rulep-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (all-stored-axe-rulep lst)
                (all-stored-axe-rulep acc)
                (<= (len tail) (len lst)))
           (all-stored-axe-rulep (mv-nth 0 (split-list-fast-aux lst tail acc)))))

(defthm all-stored-axe-rulep-of-mv-nth-0-of-split-list-fast
  (implies (all-stored-axe-rulep lst)
           (all-stored-axe-rulep (mv-nth 0 (split-list-fast lst))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-stored-axe-rulep-of-mv-nth-1-of-split-list-fast-aux
  (implies (all-stored-axe-rulep lst)
           (all-stored-axe-rulep (mv-nth 1 (split-list-fast-aux lst tail acc)))))

(defthm all-stored-axe-rulep-of-mv-nth-1-split-list-fast
  (implies (all-stored-axe-rulep lst)
           (all-stored-axe-rulep (mv-nth 1 (split-list-fast lst))))
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm all-stored-axe-rulep-of-merge-by-rule-priority
  (implies (and (all-stored-axe-rulep l1)
                (all-stored-axe-rulep l2)
                (all-stored-axe-rulep acc))
           (all-stored-axe-rulep (merge-by-rule-priority l1 l2 acc priorities)))
  :hints (("Goal" :in-theory (enable merge-by-rule-priority))))

(verify-guards merge-sort-by-rule-priority
  :hints (("Goal" :induct (merge-sort-by-rule-priority stored-rules priorities))))

(defthm all-stored-axe-rulep-of-merge-sort-by-rule-priority
  (implies (all-stored-axe-rulep stored-rules)
           (all-stored-axe-rulep (merge-sort-by-rule-priority stored-rules priorities)))
  :hints (("Goal" :in-theory (enable merge-sort-by-rule-priority))))

(defthm true-listp-of-merge-sort-by-rule-priority
  (implies (true-listp stored-rules)
           (true-listp (merge-sort-by-rule-priority stored-rules priorities)))
  :hints (("Goal" :in-theory (enable merge-sort-by-rule-priority))))

(defun rule-is-presentp (rule-symbol stored-axe-rules)
  (declare (xargs :guard (and (all-stored-axe-rulep stored-axe-rules)
                              (symbolp rule-symbol)
                              (true-listp stored-axe-rules))
                  :guard-hints (("Goal" :expand ((all-stored-axe-rulep stored-axe-rules))
                                 :in-theory (enable all-stored-axe-rulep stored-axe-rulep))) ;yuck
                  ))
  (if (endp stored-axe-rules) ;use endp?
      nil
    (let ((stored-axe-rule (first stored-axe-rules)))
      (if (eq rule-symbol (stored-rule-symbol stored-axe-rule))
          t
        (rule-is-presentp rule-symbol (rest stored-axe-rules))))))

(defthm bound-vars-suitable-for-hypsp-of-var-in-terms-of-stored-rule-lhs-args-and-stored-rule-hyps
  (implies (stored-axe-rulep stored-rule)
           (bound-vars-suitable-for-hypsp
            (vars-in-terms (stored-rule-lhs-args stored-rule))
            (stored-rule-hyps stored-rule)))
  :hints (("Goal" :in-theory (enable stored-axe-rulep))))
