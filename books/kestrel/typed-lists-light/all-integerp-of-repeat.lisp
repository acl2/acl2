; A tiny book that provides the theorem all-integerp-of-repeat.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-integerp")
(include-book "kestrel/lists-light/repeat-def" :dir :system)

(defthm all-integerp-of-repeat
  (implies (integerp x)
           (all-integerp (repeat n x)))
  :hints (("Goal" :in-theory (enable repeat))))
