; A lightweight book about the built-in function floor.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "numerator"))

(defthm floor-of-0-arg1
  (equal (floor 0 j)
         0)
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-of-0-arg2
  (equal (floor i 0)
         0)
  :hints (("Goal" :in-theory (enable floor))))

;could be expensive?
(defthm floor-of-1-when-integerp
  (implies (integerp i)
           (equal (floor i 1)
                  i))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-self
  (equal (floor i i)
         (if (equal (fix i) 0)
             0
           1))
  :hints (("Goal" :cases ((acl2-numberp i)))))
