; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "sublis-var")

(verify-termination meta-extract-rw+-term)

(verify-termination meta-extract-contextual-fact)

(verify-termination meta-extract-global-fact+)

