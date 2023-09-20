; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arithmetic-5/lib/floor-mod/floor-mod-basic" :dir :system)
(include-book "arithmetic-5/lib/basic-ops/arithmetic-theory" :dir :system)

(defthm foo
  (implies (and (rationalp x)
                (integerp y)
                (rationalp z)
                (not (equal z 0)))
           (equal (mod (* z y) z)
                  0))
  :rule-classes nil)

