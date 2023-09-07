; The DM (discrete math) package
;
; Copyright (C) 2022-2023 Kestrel Institute
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
                       ;; for vars in various theorems:
                       a b c d e f
                       ; g ; name clash (with books/misc/records.lisp) if uncommented
                       h i j k l m n o p q
                       ; r ; name clash (with books/projects/arm/fdiv/quotient.lisp) if uncommented
                       ; s ; name clash (with books/misc/records.lisp) if uncommented
                       ; t ; special symbol, not a variable name
                       u v w x y z
                       pair)
                     *acl2-exports*))
