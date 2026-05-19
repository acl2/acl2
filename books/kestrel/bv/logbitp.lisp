; A book about the the built-in function logbitp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable logbitp))

;rename
(defthm logbitp-when-j-is-not-integerp
  (implies (not (integerp j))
           (not (logbitp i j)))
  :hints (("Goal" :in-theory (enable logbitp))))

;rename
(defthm logbitp-when-i-is-negative
  (implies (and (< i 0)
                (integerp i))
           (equal (logbitp i j)
                  (logbitp 0 j)))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-of-0
  (not (logbitp n 0))
  :hints (("Goal" :in-theory (enable logbitp))))
