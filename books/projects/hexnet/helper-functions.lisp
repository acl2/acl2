; Copyright (C) 2018, Regents of the University of Texas
; Written by Ebelechukwu Esimai
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "std/lists/rev" :dir :system)

(defthm subsetp-equal-implies-car-member-equal
  (implies (and (subsetp-equal x y)
                (consp x))
           (member-equal (car x) y)))
(defthm subsetp-equal-remove-equal
  (implies (subsetp-equal x y)
           (subsetp-equal (remove-equal a x) y)))
(defthm subsetp-equal-implies-cadr-member-equal
  (implies (and (subsetp-equal x y)
                (consp x)
                (consp (cdr x)))
           (member-equal (cadr x) y)))
(defthm subsetp-equal-implies-caddr-member-equal
  (implies (and (subsetp-equal x y)
                (consp x)
                (consp (cdr x))
                (consp (cddr x)))
           (member-equal (caddr x) y)))
(defthm assoc-of-append
           (equal (append (append a b) c)
                  (append a (append b c))))
(defthm last-append
           (implies (consp b)
                    (equal (last (append a b))
                           (last b))))

(encapsulate
  ()
  (local
   (include-book "std/lists/sets" :dir :system))
  (local
   (include-book "std/lists/repeat" :dir :system))
  (defthm subsetp-equal-member-equal
  (implies (and (member-equal a x) (subsetp-equal x y))
           (member-equal a y))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary (implies (and (subsetp-equal x y) (member-equal a x))
                                 (member-equal a y)))
   (:rewrite
    :corollary (implies (and (not (member-equal a y)) (subsetp-equal x y))
                        (not (member-equal a x))))
   (:rewrite
    :corollary (implies (and (subsetp-equal x y) (not (member-equal a y)))
                        (not (member-equal a x))))))
  (defthm subsetp-refl (subsetp x x))
  (defthm subsetp-trans
        (implies (and (subsetp x y) (subsetp y z))
                 (subsetp x z)))
  (defthm subsetp-of-cdr (subsetp (cdr x) x))
  (defun set-equiv (x y)
       (declare (xargs :guard (and (true-listp x) (true-listp y))))
       (and (subsetp-equal x y)
            (subsetp-equal y x)))
  (defthm car-last-rev
    (equal (car (last (rev x)))
           (car x))))

(defun update-alist (key datum alist)
   (declare (xargs :guard (alistp alist)))
  (cond
   ((endp alist)   nil)
   ((equal key (caar alist)) (acons key datum (cdr alist)))
   (t (cons (car alist)
	    (update-alist key datum (cdr alist))))))
(defthm symbol-alistp-update-alist
  (implies (symbol-alistp alist)
           (symbol-alistp (update-alist key datum alist)))
  :rule-classes :type-prescription)

(defun flatten-alist (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (symbol-listp (car x))
        (append (car x)
                (flatten-alist (cdr x)))
      nil)))
