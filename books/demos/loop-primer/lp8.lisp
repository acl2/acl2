; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; Solutions to Challenge Problems in Loop Primer Section 8

; (certify-book "lp8")
; (ld "~/work/loop-primer/lp8.lisp" :ld-pre-eval-print t)

(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

; All confirming equivalences are :rule-classes nil so I get no interference.

; -----------------------------------------------------------------
; LP8-1
(defun symbol-to-integer-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
      (and (consp (car x))
           (symbolp (caar x))
           (integerp (cdar x))
           (symbol-to-integer-alistp (cdr x)))))

(defun sum-vals (alist)
  (declare (xargs :guard (symbol-to-integer-alistp alist)))
  (loop$ for pair in alist
         sum
         :guard (and (consp pair) (integerp (cdr pair)))
         (cdr pair)))

(defun sum-vals-loop$ (alist)
  (declare (xargs
            :guard (and (true-listp alist)
                        (loop$ for e in alist
                               always
                               (and (consp e)
                                    (symbolp (car e))
                                    (integerp (cdr e)))))))
  (loop$ for pair in alist
         sum
         :guard (and (consp pair) (integerp (cdr pair)))
         (cdr pair)))

(defthm symbol-to-integer-alistp-is-a-loop$
  (equal (symbol-to-integer-alistp x)
         (and (true-listp x)
              (loop$ for e in x
                     always
                     (and (consp e)
                          (symbolp (car e))
                          (integerp (cdr e))))))
  :rule-classes nil)

(defthm sum-vals-loop$-is-sum-vals
  (equal (sum-vals-loop$ alist)
         (sum-vals alist))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP8-2
(defun arglistp1-loop$ (lst)
  (declare (xargs :guard t))
  (and (true-listp lst)
       (loop$ for e in lst always (legal-variablep e))))

(defthm arglistp1-loop$-is-arglistp1
  (equal (arglistp1-loop$ lst)
         (arglistp1 lst))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP8-3
(defun packn1-loop$ (lst)
  (declare (xargs
            :guard
            (and (true-listp lst)
                 (loop$ for e in lst
                        always
                        (or (acl2-numberp e)
                            (symbolp e)
                            (characterp e)
                            (stringp e))))))
  (loop$ for e in lst
         append
         :guard
         (or (acl2-numberp e)
             (symbolp e)
             (characterp e)
             (stringp e))
         (explode-atom e 10)))

(defthm packn1-loop$-is-packn1
  (equal (packn1-loop$ lst)
         (packn1 lst))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP8-4
(defun select-corresponding-element (e lst1 lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2)
                              (not (member nil lst2)))))
  (cond
   ((endp lst1) nil)
   ((endp lst2) nil)
   ((equal e (car lst1)) (car lst2))
   (t (select-corresponding-element e (cdr lst1) (cdr lst2)))))

; (select-corresponding-element 'wednesday
;                               '(sunday monday tuesday wednesday thursday friday saturday)
;                               '(sun    mon    tue     wed       thu      fri    sat))
; ==>
; 'WED

(defun select-corresponding-element-loop$ (e lst1 lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2)
                              (loop$ for b in lst2 always (not (equal nil b))))))
  (loop$ for a in lst1 as b in lst2
         thereis (if (equal e a) b nil)))

(defthm select-corresponding-element-loop$-is-select-corresponding-element
  (implies (and (true-listp lst1)
                (true-listp lst2)
                (not (member nil lst2)))
           (equal (select-corresponding-element-loop$ e lst1 lst2)
                  (select-corresponding-element e lst1 lst2)))
  :rule-classes nil)
; -----------------------------------------------------------------

; LP8-5

(defun same-mod-wildcard (lst1 lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2)
                              (equal (len lst1) (len lst2)))))
  (cond ((endp lst1) t)
        ((or (eq (car lst1) '*)
             (eq (car lst2) '*))
         (same-mod-wildcard (cdr lst1) (cdr lst2)))
        ((equal (car lst1) (car lst2))
         (same-mod-wildcard (cdr lst1) (cdr lst2)))
        (t nil)))

(defun same-mod-wildcard-loop$ (lst1 lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2)
                              (equal (len lst1) (len lst2)))))
  (loop$ for e in lst1
         as  d in lst2
         always 
         (or (eq e '*)
             (eq d '*)
             (equal e d))))

(defthm same-mod-wildcard-loop$-is-same-mod-wildcard
  (implies (and (true-listp lst1)
                (true-listp lst2)
                (equal (len lst1) (len lst2)))
           (equal (same-mod-wildcard-loop$ lst1 lst2)
                  (same-mod-wildcard lst1 lst2)))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP8-6

(defun getprops1-loop$ (alist)
  (declare (xargs :guard (true-list-listp alist)))
  (loop$ for x in alist
         when :guard (true-listp x)
         (not (or (null (cdr x))
                  (eq (car (cdr x)) *acl2-property-unbound*)))
         collect :guard (true-listp x)
         (cons (car x) (cadr x))))

(defthm getprops1-loop$-is-getprops1
  (equal (getprops1-loop$ alist)
         (getprops1 alist))
  :rule-classes nil)

; By the way, since
(defthm true-list-listp-can-be-rewritten
  (equal (true-list-listp alist)
         (and (true-listp alist)
              (loop$ for e in alist always (true-listp e))))
  :rule-classes nil)

; So we could also use

(defun getprops1-loop$-loop$ (alist)
  (declare (xargs :guard (and (true-listp alist)
                              (loop$ for e in alist always (true-listp e)))))
  (loop$ for x in alist
         when :guard (true-listp x)
         (not (or (null (cdr x))
                  (eq (car (cdr x)) *acl2-property-unbound*)))
         collect :guard (true-listp x)
         (cons (car x) (cadr x))))

(defthm getprops1-loop$-loop$-is-getprops1
  (equal (getprops1-loop$-loop$ alist)
         (getprops1 alist))
  :rule-classes nil)

