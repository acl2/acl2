; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Note: this book doesn't appear to be used anywhere.  Consider deleting it.
(in-package "ACL2")

(include-book "defset-macros")
(local (include-book "defset-encapsulates"))

(def-set-equiv equal :prove-elem-congruences nil)
