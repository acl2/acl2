; The DM (discrete math) package
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rtl/rel11/portcullis" :dir :system)

(defpkg "DM" (append '(local-defun
                       local-defund
                       local-defthm
                       local-defthmd
                       local-in-theory
                       defrule
                       defruled
                       defsection
                       rtl::fl
                       rtl::cg
                       rtl::congruent
                       x ; for formals, e.g., of rtl::fl
                       )
                     *acl2-exports*))
