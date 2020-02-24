; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-verified-p")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-p 'len (w state)))

(assert! (guard-verified-p 'cons (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards t)) x)
 (assert! (guard-verified-p 'f (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert! (not (guard-verified-p 'f (w state)))))

(must-succeed*
 (defthm th (acl2-numberp (+ (fix x) (fix y))))
 (verify-guards th)
 (assert! (guard-verified-p 'th (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (not (guard-verified-p 'th (w state)))))
