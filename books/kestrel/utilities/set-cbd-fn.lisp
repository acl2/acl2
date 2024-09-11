; Trying to get set-cbd-fn into :logic mode.
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "state"))
(local (include-book "coerce"))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local (in-theory (disable get-global)))

(verify-termination merge-using-dot-dot (declare (xargs :verify-guards nil))) ; todo: :doc verify-termination should mention this declare trick
(verify-termination our-merge-pathnames)
(verify-termination canonical-dirname!)
(verify-termination maybe-add-separator)
(verify-termination expand-tilde-to-user-home-dir)
(verify-termination set-cbd-fn-dir)
;(verify-termination set-cbd-fn1) ; ack! raw lisp code
;(verify-termination set-cbd-fn)
