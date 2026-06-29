; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../top")

(defun-sk tpp-int2 (tp)
  (forall (x y)
    (implies (and (in x tp)
                  (in y tp))
             (in (int2 x y) tp)))
  :rewrite :direct)

(defun-sk tpp-union (tp)
  (forall (tp2)
    (implies (subset tp2 tp)
             (in (union tp2) tp)))
  :rewrite :direct)

(defun tpp (tp)
  (and (tpp-int2 tp)
       (tpp-union tp)))

(defthm tpp-forward
  (implies (tpp tp)
           (and (tpp-int2 tp)
                (tpp-union tp)))
  :rule-classes :forward-chaining)

(in-theory (disable tpp-int2 tpp-union tpp))

(defthmz in-0-tp
  (implies (tpp tp)
           (in 0 tp))
  :hints (("Goal"
           :in-theory (enable tpp)
           :use ((:instance tpp-union-necc (tp tp) (tp2 0)))))
  :rule-classes :forward-chaining)

(defthmz in-union-tp-tp
  (implies (tpp tp)
           (in (union tp) tp))
  :hints (("Goal"
           :in-theory (enable tpp)
           :use ((:instance tpp-union-necc (tp tp) (tp2 tp)))))
  :rule-classes :forward-chaining)

(defun closed (s tp)
  (and (subset s (union tp))
       (in (diff (union tp) s)
           tp)))
