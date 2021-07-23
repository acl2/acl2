; Elaborating lists of rule names and 0-ary functions
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
(include-book "kestrel/utilities/world" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))

;; ;move
;; (defund defthm-in-worldp (defthm-name wrld)
;;   (declare (xargs :guard (and (symbolp defthm-name)
;;                               (plist-worldp wrld))))
;;   (let ((body (getprop defthm-name 'theorem nil 'current-acl2-world wrld)))
;;     (if body
;;         t
;;       nil)))

;; A rule item is either a symbol (the name of a rule -- i.e., a theorem or
;; function), or a "call" of a 0-ary function that returns a list of rule names
;; (symbols).
(defun rule-itemp (item)
  (declare (xargs :guard t))
  (or (symbolp item)
      (and (true-listp item)
           (= 1 (len item))
           (symbolp (first item)))))

(defun rule-item-listp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (rule-itemp (first items))
         (rule-item-listp (rest items)))))

(defund rule-item-list-listp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (rule-item-listp (first items))
         (rule-item-list-listp (rest items)))))

;;Returns a list of rule-names.  Elaborates a 0-ary function call to the list
;;of symbols it returns.
(defund elaborate-rule-item (item state)
  (declare (xargs :guard (rule-itemp item)
                  :stobjs state))
  (if (consp item)
      (let ((function-name (first item)))
        ;; Must be a "call" of a 0-ary function:
        (if (consp (fn-formals function-name (w state)))
            (er hard? 'elaborate-rule-item "~x0 is not 0-ary." function-name)
          ;; 0-ary function, so evaluate it
          (mv-let (erp rule-names)
            (magic-ev-fncall function-name nil state nil nil)
            (if erp
                (er hard? 'elaborate-rule-item "Error evaluating ~x0." function-name)
              (if (not (symbol-listp rule-names))
                  (er hard? 'elaborate-rule-item "~x0 evaluated to something other than a list of symbols." function-name)
                rule-names)))))
    ;; Must be the name of a rule:
    (if (symbolp item)
        (list item)
      (er hard? 'elaborate-rule-item "Bad rule-item: ~x0." item))))

(defthm symbol-listp-of-elaborate-rule-item
  (symbol-listp (elaborate-rule-item item state))
  :hints (("Goal" :in-theory (enable elaborate-rule-item))))

;;Returns a list of rule-names.
(defund elaborate-rule-items-aux (items acc state)
  (declare (xargs :guard (and (rule-item-listp items)
                              (symbol-listp acc))
                  :stobjs state))
  (if (endp items)
      (reverse acc)
    (elaborate-rule-items-aux (rest items)
                          (append (elaborate-rule-item (first items) state)
                                  acc)
                          state)))

(defthm true-listp-of-elaborate-rule-items-aux
  (implies (true-listp acc)
           (true-listp (elaborate-rule-items-aux items acc state)))
  :hints (("Goal" :in-theory (enable elaborate-rule-items-aux))))

(defthm symbol-listp-of-elaborate-rule-items-aux
  (implies (symbol-listp acc)
           (symbol-listp (elaborate-rule-items-aux items acc state)))
  :hints (("Goal" :in-theory (enable elaborate-rule-items-aux))))

(defund elaborate-rule-items (items state)
  (declare (xargs :guard (rule-item-listp items)
                  :stobjs state))
  (elaborate-rule-items-aux items nil state))

(defthm true-listp-of-elaborate-rule-items
  (true-listp (elaborate-rule-items items state))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable elaborate-rule-items))))

(defthm symbol-listp-of-elaborate-rule-items
  (symbol-listp (elaborate-rule-items items state))
  :hints (("Goal" :in-theory (enable elaborate-rule-items))))

;;Returns a list of rule-names.
(defund elaborate-rule-item-lists (item-lists state)
  (declare (xargs :guard (rule-item-list-listp item-lists)
                  :guard-hints (("Goal" :in-theory (enable rule-item-list-listp)))
                  :stobjs state))
  (if (endp item-lists)
      nil
    (cons (elaborate-rule-items (first item-lists) state)
          (elaborate-rule-item-lists (rest item-lists) state))))

(defthm symbol-list-listp-of-elaborate-rule-item-lists
  (symbol-list-listp (elaborate-rule-item-lists item-lists state))
  :hints (("Goal" :in-theory (enable elaborate-rule-item-lists))))

(defund remove-from-all (rule-lists remove-rules)
  (declare (xargs :guard (and (symbol-list-listp rule-lists)
                              (symbol-listp remove-rules))))
  (if (endp rule-lists)
      nil
    (cons (set-difference-eq (first rule-lists) remove-rules)
          (remove-from-all (rest rule-lists) remove-rules))))
