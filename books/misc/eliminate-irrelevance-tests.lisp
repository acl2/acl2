; Copyright (C) 2016, ForrestHunt, Inc.
; Matt Kaufmann, October, 2016
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; First example

(encapsulate
  ((p1 () t)
   (my-app1 (x y) t))
  (local (defun p1 () t))
  (local (defun my-app1 (x y) (append x y)))
  (defthm my-app1-def
    (implies (p1)
             (equal (my-app1 x y)
                    (if (consp x)
                        (cons (car x) (my-app1 (cdr x) y))
                      y)))
    :rule-classes ((:definition
                    :controller-alist ((my-app1 t nil))))))

(defun rev1 (x)
  (if (consp x)
      (my-app1 (rev1 (cdr x))
               (cons (car x) nil))
    nil))

(defthm test1
  (implies (and (p1)
                (true-listp x))
           (equal (rev1 (rev1 x)) x)))

; Second example

(encapsulate
  ((p2 () t)
   (my-app2 (x y) t))
  (local (defun p2 () nil))
  (local (defun my-app2 (x y) (append x y)))
  (defthm my-app2-def
    (implies (not (p2))
             (equal (my-app2 x y)
                    (if (consp x)
                        (cons (car x) (my-app2 (cdr x) y))
                      y)))
    :rule-classes ((:definition
                    :controller-alist ((my-app2 t nil))))))

(defun rev2 (x)
  (if (consp x)
      (my-app2 (rev2 (cdr x))
               (cons (car x) nil))
    nil))

(defthm test2
  (implies (and (not (p2))
                (true-listp x))
           (equal (rev2 (rev2 x)) x)))
