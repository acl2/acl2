; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "zify")

(zify identity-fun identity :dom s :ran s :args (s))

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

(defthmz inverse-identity-fun
  (equal (inverse (identity-fun s))
         (identity-fun s))
  :props (zfc identity-fun$prop prod2$prop inverse$prop)
  :hints (("Goal" :in-theory (enable extensionality-rewrite))))

(defthmz domain-identity-fun
  (equal (domain (identity-fun s))
         s)
  :props (zfc identity-fun$prop prod2$prop domain$prop inverse$prop))

(defthmz codomain-identity-fun
  (equal (codomain (identity-fun s))
         s)
  :props (zfc identity-fun$prop prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable codomain))))
