; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "prelims")

(defun-sk point-point-separable (x y tp)
  (exists (s1 s2)
    (and (in s1 tp)
         (in s2 tp)
         (in x s1)
         (in y s2)
         (equal (int2 s1 s2) 0))))

(defun-sk hausdorff (tp)
  (forall (x y)
    (implies (and (in x (union tp))
                  (in y (union tp))
                  (not (equal x y)))
             (point-point-separable x y tp)))
  :rewrite :direct)

(defun-sk point-set-separable (x c tp)
  (exists (s1 s2)
    (and (in s1 tp)
         (in s2 tp)
         (in x s1)
         (subset c s2)
         (equal (int2 s1 s2) 0))))

(defun-sk regular (tp)
  (forall (x c)
    (implies (and (in x (union tp))
                  (closed c tp)
                  (not (in x c)))
             (point-set-separable x c tp)))
  :rewrite :direct)
             
(defun-sk set-set-separable (c1 c2 tp)
  (exists (s1 s2)
    (and (in s1 tp)
         (in s2 tp)
         (subset c1 s1)
         (subset c2 s2)
         (equal (int2 s1 s2) 0))))

(defun-sk normal (tp)
  (forall (c1 c2)
    (implies (and (closed c1 tp)
                  (closed c2 tp)
                  (equal (int2 c1 c2) 0))
             (point-set-separable c1 c2 tp)))
  :rewrite :direct)

(in-theory (disable hausdorff regular normal
                    point-point-separable
                    point-set-separable
                    set-set-separable))

