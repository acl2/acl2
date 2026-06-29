; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "finite-domain")
(include-book "finite-inverse")

(defthmz finite-implies-finite-image
; Since (image f) = (domain (inverse f)), this follows from finiteness being
; preserved by inverse and domain.
  (implies (and (force (relation-p f))
                (finite f))
           (finite (image f)))
  :hints (("Goal" :in-theory (e/d (finite-implies-finite-domain image)
                                  (domain-inverse))))
  :props (zfns-prop compose$prop diff$prop swap$prop restrict$prop
;;;<<Prop added by Claude, Opus 6.8 max effort:>>
                    rcompose$prop))
