; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "finite-restrict")
(include-book "../swap")
(include-book "finite-bang")

(defthmz image-compose-backward
  (implies (and (funp f1)
                (funp f2)
                (subset (domain f1) (image f2))
                (in elt (image f1)))
           (in elt (image (compose f1 f2))))
  :hints (("Goal"
           :use ((:instance in-image-rewrite
                            (x elt)
                            (r f1)))
           :restrict ((in-image-suff
                       ((p (cons (apply (inverse f2)
                                        (apply (inverse f1) elt))
                                 elt)))))
           :in-theory (disable in-image-necc)))
  :props (zfc prod2$prop domain$prop compose$prop inverse$prop))

(defthme image-compose
  (implies (and (funp f1)
                (funp f2)
                (subset (domain f1) (image f2)))
           (equal (image (compose f1 f2))
                  (image f1)))
  :props (zfc prod2$prop domain$prop compose$prop inverse$prop))

(defthmz finite!-implies-finite!-inverse
  (implies (and (force (relation-p r))
                (finite! r))
           (finite! (inverse r)))
  :hints (("Goal"
           :expand ((finite! r))
           :restrict ((finite!-suff
                       ((f (compose (swap r)
                                    (finite!-witness r))))))))
  :props (zfns-prop compose$prop swap$prop
;;;<<Prop added by Claude, Opus 6.8 max effort:>>
                    rcompose$prop))

(defthmz finite-implies-finite-inverse
  (implies (and (force (relation-p r))
                (finite r))
           (finite (inverse r)))
  :hints (("Goal" :in-theory (enable finite-is-finite!)))
  :props (zfns-prop compose$prop swap$prop diff$prop restrict$prop
;;;<<Prop added by Claude, Opus 6.8 max effort:>>
                    rcompose$prop))
