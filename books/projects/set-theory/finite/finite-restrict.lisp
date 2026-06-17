; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")
(include-book "../restrict")

; For :props:
(include-book "../zfns")
(include-book "../phoenix")
(include-book "../identity")

(local (include-book "finite-domain"))

(defthmz finite-restrict
  (implies (and (funp f)
                (finite d))
           (finite (restrict f d)))

; It's perhaps unusual that we need to enable the conditional version (here,
; finite-domain-implies-finite) of a corresponding unconditional enabled rule
; (here, finite-iff-finite-domain).  But the conditional version supports
; backchaining to (finite (domain (restrict f d))), which then permits the
; proof to be completed.

  :hints (("Goal" :in-theory (enable finite-domain-implies-finite)))
  :props (zfns-prop compose$prop phoenix$prop identity-fun$prop
                    diff$prop restrict$prop))
