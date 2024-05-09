; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(in-theory (disable car-cons))

; Variant of test7a that avoids enable.
(defthmd app-assoc-rewrite
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (union-theories '(car-cons)
                                             (current-theory :here)))))

; Variant of test7a that uses e/d.
(defthm app-assoc-rewrite-2
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d (car-cons) ()))))
