; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date December, 2009)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book checks our world invariants.  Feel free to strengthen those checks
; as we add new ones.  Note that the real checking goes on in the make-event
; form(s) in worldp-check.acl2.

(in-package "ACL2")

(defun check-worldp-check (x)

; Function worldp-check-fn should be defined by the make-event in
; worldp-check.acl2 if and only if chk-pseudo-good-worldp succeeded.

  (worldp-check-fn x))
