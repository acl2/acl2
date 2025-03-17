; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "zify")

(zify identity-fun identity :dom s :ran s :args (s))

(defun iterate (f n)
  (declare (type (integer 0 *) n))
  (if (zp n)
      (identity-fun (domain f))
    (compose f (iterate f (1- n)))))

(defthmz compose-identity-fun-with-fn-equal
  (implies (and (force (funp f))
                (force (subset (codomain f) s)))
           (fn-equal (compose (identity-fun s) f)
                     f))
  :props (zify-prop compose$prop identity-fun$prop)
  :hints (("Goal" :in-theory (e/d (fn-equal)
                                  (fn-equal-implies-in)))))

(defthmz compose-identity-fun
  (implies (and (force (funp f))
                (force (subset (codomain f) s)))
           (equal (compose (identity-fun s) f)
                  f))
  :props (zify-prop compose$prop identity-fun$prop)
  :hints (("Goal" :use compose-identity-fun-with-fn-equal
           :in-theory (e/d (fn-equal-implies-equal)
                           (compose-identity-fun-with-fn-equal)))))

(defthm funp-iterate
  (implies (and (funp f)
                (zify-prop)
                (force (compose$prop))
                (force (identity-fun$prop)))
           (funp (iterate f n))))

(defthmz inverse-identity-fun
  (equal (inverse (identity-fun s))
         (identity-fun s))
  :props (zfc identity-fun$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz codomain-identity-fun
  (equal (codomain (identity-fun s))
         s)
  :props (zfc identity-fun$prop prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable codomain))))

(defthmz subset-codomain-iterate
  (implies (and (funp f)
                (subset (codomain f) (domain f)))
           (subset (codomain (iterate f n))
                   (domain f)))
  :props (zify-prop compose$prop identity-fun$prop)
  :hints (("Goal" :restrict ((subset-transitivity ((y (codomain f))))))))

(defthmz domain-iterate
  (implies (and (funp f)
                (subset (codomain f) (domain f)))
           (equal (domain (iterate f n))
                  (domain f)))
  :props (zify-prop compose$prop identity-fun$prop))

(defthmz iterate-plus
  (implies (and (natp m)
                (natp n)
                (funp f)
                (subset (codomain f) (domain f)))
           (equal (iterate f (+ m n))
                  (compose (iterate f m) (iterate f n))))
  :props (zify-prop compose$prop identity-fun$prop))
