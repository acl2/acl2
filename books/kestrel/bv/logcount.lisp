; A lightweight book about the built-in function logcount
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/power-of-2p-def" :dir :system)
(local (include-book "kestrel/arithmetic-light/power-of-2p" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/nonnegative-integer-quotient" :dir :system))

(in-theory (disable logcount))

(local (in-theory (disable evenp)))

(defthm logcount-of-nonnegative-integer-quotient-of-2
  (implies (natp i)
           (equal (logcount (nonnegative-integer-quotient i 2))
                  (if (evenp i)
                      (logcount i)
                    (+ -1 (logcount i)))))
  :hints (("Goal" :in-theory (enable logcount))))

(defthm logcount-of-floor-of-2
  (implies (natp i)
           (equal (logcount (floor i 2))
                  (if (evenp i)
                      (logcount i)
                    (+ -1 (logcount i)))))
  :hints (("Goal" :in-theory (enable floor-becomes-nonnegative-integer-quotient))))

(defthm equal-of-0-and-logcount
  (implies (integerp x)
           (equal (equal 0 (logcount x))
                  (or (equal 0 x)
                      (equal -1 x))))
  :hints (("Goal" :in-theory (enable logcount))))

(defthm equal-of-1-and-logcount-when-not-evenp
  (implies (and (not (evenp x))
                (natp x))
           (equal (equal 1 (logcount x))
                  (equal 1 x)))
  :hints (("Goal" :expand (logcount x)
           :in-theory (disable logcount-of-nonnegative-integer-quotient-of-2))))

;; todo: use this to give power-of-2p a fast body
(defthm power-of-2p-redef
  (implies (natp x)
           (equal (power-of-2p x)
                  (equal 1 (logcount x))))
  :hints (("subgoal *1/4" :cases ((power-of-2p x)))
          ("Goal" :in-theory (enable logcount
                                     power-of-2p-when-power-of-2p-of-*-of-1/2
                                     evenp-when-power-of-2p
                                     nonnegative-integer-quotient-becomes-floor
                                     floor-when-evenp))))
