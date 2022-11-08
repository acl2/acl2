; The DM (discrete math) package
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defpkg "DM" (append '(local-defun
                       local-defund
                       local-defthm
                       local-defthmd
                       local-in-theory
                       defrule
                       defruled
                       defsection)
                     *acl2-exports*))
