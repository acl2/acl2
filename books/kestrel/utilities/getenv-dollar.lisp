; A lightweight book about the built-in function getenv$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "update-acl2-oracle"))
(local (include-book "read-acl2-oracle")) ; todo: without this, the book loads but doesn't certify

(in-theory (disable getenv$))

(local (in-theory (disable w state-p)))

(defthm w-of-mv-nth-2-of-getenv$
  (equal (w (mv-nth 2 (getenv$ str state)))
         (w state))
  :hints (("Goal" :in-theory (e/d (getenv$) (update-acl2-oracle)))))

(defthm state-p1-of-mv-nth-2-of-getenv$
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (getenv$ str state))))
  :hints (("Goal" :in-theory (enable getenv$))))
