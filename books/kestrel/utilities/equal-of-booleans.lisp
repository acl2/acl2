; A lightweight book about the built-in function binary-append.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also equal-of-booleans-rewrite in books/centaur/ubdds/core.lisp (which
;; has a backchain limit of 1).  A backchain-limit of 0 should still let us use
;; booleanp facts known by type-prescription (which should be the common case).
;; We expect IFF to be enabled and so cause a case split.  TODO: Consider using
;; polarities and only doing this in the conclusion of the theorem.
(defthm equal-of-booleans-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (equal x y)
                  (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; Disabled by default
(defthmd equal-of-booleans
  (implies (and (booleanp x)
                (booleanp y))
           (equal (equal x y)
                  (iff x y))))
