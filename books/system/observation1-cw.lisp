; Copyright (C) 2019, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; At one time we verified termination and guards of observation1-cw in ACL2
; source file boot-strap-pass-2-a.lisp.  However, that caused an error during
; "make proofs" because a call of all-vars!1 let to a call of executable-tamep
; and then executable-badge, which is illegal to call during the boot-strap.
; So we deal with observation1-cw here.

(verify-termination observation1-cw)
(verify-guards observation1-cw)
