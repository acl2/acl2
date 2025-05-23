; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "identity") ; includes "zify"

(defun iterate (f n)
  (declare (type (integer 0 *) n))
  (if (zp n)
      (identity-fun (domain f))
    (compose f (iterate f (1- n)))))

(defthmz funp-iterate
  (implies (funp f)
           (funp (iterate f n)))
  :props (zify-prop compose$prop identity-fun$prop))

(defthmz subset-image-iterate
  (implies (and (funp f)
                (subset (image f) (domain f)))
           (subset (image (iterate f n))
                   (domain f)))
  :props (zify-prop compose$prop identity-fun$prop)
  :hints (("Goal" :restrict ((subset-transitivity ((y (image f))))))))

(defthmz domain-iterate
  (implies (and (funp f)
                (subset (image f) (domain f)))
           (equal (domain (iterate f n))
                  (domain f)))
  :props (zify-prop compose$prop identity-fun$prop))

(defthmz iterate-plus
  (implies (and (natp m)
                (natp n)
                (funp f)
                (subset (image f) (domain f)))
           (equal (iterate f (+ m n))
                  (compose (iterate f m) (iterate f n))))
  :props (zify-prop compose$prop identity-fun$prop))
