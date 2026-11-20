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

(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))

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

;rename
;; The low bit of an even number is clear.
(defthm logbitp-0-of-times-2
  (implies (integerp x)
           (not (logbitp 0 (* 2 x))))
  :hints (("Goal" :in-theory (enable logbitp oddp))))

;rename
(defthm logbitp-of-double
  (implies (and (natp n)
                (integerp x))
           (equal (logbitp n (* 2 x))
                  (if (equal 0 n)
                      nil
                    (logbitp (+ -1 n) x))))
  :hints (("Goal" :in-theory (e/d (logbitp expt-of-+ floor-normalize-denominator) (floor-of-*-of-/-and-1)))))

;rename
(defthm logbitp-of-shift
  (implies (and (integerp x)
                (integerp n)
                (natp m))
           (equal (logbitp n (* (expt 2 m) x))
                  (if (< (nfix n) m)
                      nil
                    (logbitp (- (nfix n) m) x))))
  :hints (("Goal"           :use (:instance oddp-of-times-expt (m (- m (nfix n))))
           :in-theory (e/d (logbitp expt-of-+ floor-normalize-denominator) (floor-of-*-of-/-and-1 oddp-of-times-expt)))))
