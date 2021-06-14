; Distinguishing between different ways to represent rule sets
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

(include-book "kestrel/axe/make-axe-rules" :dir :system)
(include-book "kestrel/axe/rule-alists" :dir :system)

;;;
;;; tagged-rule-setp
;;;

(defun tagged-rule-setp (tagged-rule-set)
  (declare (xargs :guard t))
  (and (consp tagged-rule-set)
       (if (eq :rule-names (car tagged-rule-set))
           (symbol-listp (cdr tagged-rule-set))
         (if (eq :rules (car tagged-rule-set))
             (axe-rule-listp (cdr tagged-rule-set))
           (if (eq :rule-alist (car tagged-rule-set))
               (rule-alistp (cdr tagged-rule-set))
             nil)))))
;;;
;;; tagged-rule-setps
;;;

(defund tagged-rule-setsp (tagged-rule-sets)
  (declare (xargs :guard t))
  (if (atom tagged-rule-sets)
      (null tagged-rule-sets)
    (and (tagged-rule-setp (first tagged-rule-sets))
         (tagged-rule-setsp (rest tagged-rule-sets)))))

(defthm tagged-rule-setsp-of-cons
  (equal (tagged-rule-setsp (cons a b))
         (and (tagged-rule-setp a)
              (tagged-rule-setsp b)))
  :hints (("Goal" :in-theory (enable tagged-rule-setsp))))

;; Throws an error if anything is ill-formed, or if rules are supplied in
;; multiple ways.  Returns a boolean indicating whether everything is ok, but
;; the main consideration is whether this throws an error.
(defun ensure-rules-etc-ok (ctx rules rule-alist rule-alists)
  (declare (xargs :guard (symbolp ctx))) ;todo: strengthen
  (b* (((when (not (or (eq :none rules)
                       (symbol-listp rules))))
        (er hard? ctx "ERROR: Bad :rules given!"))
       ((when (not (or (eq :none rule-alist)
                       (rule-alistp rule-alist))))
        (er hard? ctx "ERROR: Bad :rules-alist given!"))
       ((when (not (or (eq :none rule-alists)
                       (and (true-listp rule-alists)
                            (all-rule-alistp rule-alists)))))
        (er hard? ctx "ERROR: Bad :rules-alists given!"))
       (number-of-ways-rules-given (+ (if (eq :none rules) 0 1)
                                      (if (eq :none rule-alist) 0 1)
                                      (if (eq :none rule-alists) 0 1)))
       ((when (equal 0 number-of-ways-rules-given))
        (er hard? ctx "ERROR: No :rules, :rule-alist, or :rule-alists given!") ;todo: make this a warning?
        )
       ((when (< 1 number-of-ways-rules-given)) ;todo: consider combining them
        (er hard? ctx "ERROR: Only one of :rule, :rule-alist, and :rule-alists be given!")
        ))
    t))

;; Only one of RULES/RULE-ALIST/RULE-ALISTS should be a value other than :none
;; Returns (mv erp rule-alists).  At most one of RULES, RULE-ALIST, and
;; RULE-ALISTS should be a value other than :none.
(defun make-tagged-rule-sets (rules rule-alist rule-alists)
  (declare (xargs :guard (and (or (eq :none rules)
                                  (symbol-listp rules))
                              (or (eq :none rule-alist)
                                  (rule-alistp rule-alist))
                              (or (eq :none rule-alists)
                                  (and (true-listp rule-alists)
                                       (all-rule-alistp rule-alists)))
                              (not (and (eq :none rules)
                                        (eq :none rule-alist)
                                        (eq :none rule-alists))))))
  (mv (erp-nil)
      (if (not (eq :none rules))
          (list (cons :rule-names rules)) ; a single rule set
        (if (not (eq :none rule-alist))
            (list (cons :rule-alist rule-alist)) ;just one rule-set
          ;; several rule-alists:
          (cons-onto-all :rule-alist rule-alists)))))
