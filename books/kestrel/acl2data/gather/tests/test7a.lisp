; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we test the removing runes repeatedly field.

(in-package "ACL2")

(in-theory (disable car-cons))

; Should get same results as with encapsulate in test7b.lisp.
(defthm app-assoc-rewrite
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable car-cons))))
