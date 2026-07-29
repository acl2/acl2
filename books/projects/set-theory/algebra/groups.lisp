; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines notions of group and Abelian group.

(in-package "ZF")

(include-book "projects/set-theory/top" :dir :system)

(defun apply2 (op x y)
  (apply op (cons x y)))

(defun-sk group-identity-p (s op e)
  (forall x
    (implies (in x s)
             (and (equal (apply2 op e x) x)
                  (equal (apply2 op x e) x)))))

(defun-sk group-inverse-p (s op e inv)
  (forall x
    (implies (in x s)
             (and (in (apply inv x) s)
                  (equal (apply2 op x (apply inv x)) e)
                  (equal (apply2 op (apply inv x) x) e)))))

(defun-sk group-associative-p (s op)
  (forall (x y z)
    (implies (and (in x s) (in y s) (in z s))
             (equal (apply2 op (apply2 op x y) z)
                    (apply2 op x (apply2 op y z))))))

(defun groupp (s op e inv)
  (and (equal (domain op) (prod2 s s))
       (subset (image op) s)
       (in e s)
       (group-identity-p s op e)
       (group-associative-p s op)
       (equal (domain inv) s)
       (group-inverse-p s op e inv)))

(defun-sk abelian-p (s op)
  (forall (x y)
    (implies (and (in x s) (in y s))
             (equal (apply2 op x y)
                    (apply2 op y x)))))

(defun abelian-group-p (s op e inv)
  (and (groupp s op e inv)
       (abelian-p s op)))
