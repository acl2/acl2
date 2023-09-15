; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we test the removing runes repeatedly field.

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

(defthm foo
  (implies (integerp x)
           (< (mod x 8) 8)))
