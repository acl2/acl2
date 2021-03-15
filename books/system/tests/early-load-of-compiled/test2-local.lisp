; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This suffered from the same issue as test2.lisp; see comments there.

; Below, "t2l" comes from the filename.

(in-package "ACL2")
(local (defun t2l-fn (x) x))
(make-event
 `(defconst *t2l-1* ',(make-fast-alist
                       (hons-copy '((3 . 4))))))
(make-event
 `(defconst *t2l-2* ',(make-fast-alist
                       (hons-copy '((3 . 4))))))
