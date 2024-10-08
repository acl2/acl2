; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rawp")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (rawp 'len state))

(assert! (rawp 'fmt-to-comment-window state))

(assert! (rawp 'floor state))

(assert! (rawp 'cw-gstack-fn state))

(assert! (rawp 'certify-book-fn state))

(assert! (rawp 'ev-w state))

(assert! (not (rawp 'cons state)))

(assert! (not (rawp 'parilis$ state)))

(must-succeed*
 (defun f (x) x)
 (assert! (not (rawp 'f state))))
