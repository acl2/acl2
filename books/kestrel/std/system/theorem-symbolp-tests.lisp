; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "theorem-symbolp")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (theorem-symbolp 'car-cdr-elim (w state)))

(assert! (not (theorem-symbolp 'cons (w state))))

(assert! (not (theorem-symbolp 'aaaaaaaaa (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (theorem-symbolp 'th (w state))))
