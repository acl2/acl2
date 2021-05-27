; Copyright (C) 2021, ForrestHunt, Inc.
; Matt Kaufmann, May, 2021
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2-PC")

#!acl2
(defconst *c*
  (mv-let (col str)
    (fmt1-to-string "~x0" (list (cons #\0 'abc)) 0)
    (declare (ignore str))
    col))

; Before a bug fix for fmt1-to-string on 5/13/2021, we could prove that *c* = 9
; rather than 3, because the acl2-pc package was used.  From there it was easy
; to prove nil, by combining that result with a proof that *c* = 3 in a book in
; the "ACL2" package.
#!acl2
(thm (equal *c* 3))

#!acl2
(defconst *c2*
  (mv-let (col str)
    (fmt1-to-string "~x0" (list (cons #\0 'abc)) 0
                    :fmt-control-alist '((current-package . "ACL2-PC")))
    (declare (ignore str))
    col))

; This time we get "ACL2::ABC".
#!acl2
(thm (equal *c2* 9))
