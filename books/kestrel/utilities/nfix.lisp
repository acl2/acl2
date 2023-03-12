; A lightweight book about the built-in function nfix
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable nfix))

;; only needed for Axe?
(defthmd natp-of-nfix
  (natp (nfix x)))

(defthm nfix-when-natp
  (implies (natp x)
           (equal (nfix x)
                  x))
  :hints (("Goal" :in-theory (enable nfix))))

(defthm nfix-when-natp-cheap
  (implies (natp x)
           (equal (nfix x)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))
