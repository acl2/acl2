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

(assert-event ; to be relevant, literal should be (not (p1))
 (equal (assoc-eq 'p1 (global-val 'never-irrelevant-fns-alist (w state)))
        '(p1 . t)))

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
  (local (defun p2 () t))
  (local (defun my-app2 (x y) (append x y)))
  (defthm my-app2-def
    (implies (not (equal (my-app2 x y)
                         (if (consp x)
                             (cons (car x) (my-app2 (cdr x) y))
                           y)))
             (not (p2)))))

(assert-event ; to be relevant, literal should be (not (p2))
 (equal (assoc-eq 'p2 (global-val 'never-irrelevant-fns-alist (w state)))
        '(p2 . t)))

; Third example

(encapsulate
  ((p3 () t)
   (my-app3 (x y) t))
  (local (defun p3 () nil))
  (local (defun my-app3 (x y) (append x y)))
  (defthm my-app3-def
    (implies (not (p3))
             (equal (my-app3 x y)
                    (if (consp x)
                        (cons (car x) (my-app3 (cdr x) y))
                      y)))
    :rule-classes ((:definition
                    :controller-alist ((my-app3 t nil))))))

(assert-event ; to be relevant, literal should be (p3)
 (equal (assoc-eq 'p3 (global-val 'never-irrelevant-fns-alist (w state)))
        '(p3 . nil)))

(defun rev3 (x)
  (if (consp x)
      (my-app3 (rev3 (cdr x))
               (cons (car x) nil))
    nil))

(defthm test3
  (implies (and (not (p3))
                (true-listp x))
           (equal (rev3 (rev3 x)) x)))

; Fourth example

(encapsulate
  ((p4 () t)
   (my-app4 (x y) t))
  (local (defun p4 () t))
  (local (defun my-app4 (x y) (append x y)))
  (defthm my-app4-def
    (implies (not (equal (my-app4 x y)
                         (if (consp x)
                             (cons (car x) (my-app4 (cdr x) y))
                           y)))
             (p4))))

(assert-event ; to be relevant, literal should be (p4)
 (equal (assoc-eq 'p4 (global-val 'never-irrelevant-fns-alist (w state)))
        '(p4 . nil)))
