; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmax-nat")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; max {n in Nat | n <= 10}

(defmax-nat max-leq-10 n ()
  (<= n 10))

(defthm max-leq-10.elementp-of-0
  (max-leq-10.elementp 0))

(defthm max-leq-10.uboundp-of-100
  (max-leq-10.uboundp 100)
  :hints (("Goal" :in-theory (enable max-leq-10.uboundp))))

(defthm max-leq-10.existsp-via-0-and-100
  (max-leq-10.existsp)
  :hints (("Goal" :use (:instance max-leq-10.existsp-when-nonempty-and-bounded
                        (n0 0) (n1 100)))))

(defthm max-leq-10.uboundp-of-10
  (max-leq-10.uboundp 10)
  :hints (("Goal" :in-theory (enable max-leq-10.uboundp))))

(defthm max-leq-10-is-10
  (equal (max-leq-10) 10)
  :hints (("Goal"
           :use (:instance max-leq-10.equal-when-member-and-ubound (n 10)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; max {y in Nat | y <= x}, where x in Nat

(defmax-nat max-leq-x y (x)
  (<= y x)
  :guard (natp x))

(defthm max-leq-x.elementp-of-x
  (max-leq-x.elementp x x)
  :hints (("Goal" :in-theory (enable max-leq-x.elementp))))

(defthm max-leq-x.uboundp-of-x
  (implies (natp x)
           (max-leq-x.uboundp x x))
  :hints (("Goal" :in-theory (enable max-leq-x.uboundp max-leq-x.elementp))))

(defthm max-leq-x.existsp-via-x-and-x
  (implies (natp x)
           (max-leq-x.existsp x))
  :hints (("Goal" :use (:instance max-leq-x.existsp-when-nonempty-and-bounded
                        (y0 x) (y1 x)))))

(defthm max-leq-x-is-x
  (implies (natp x)
           (equal (max-leq-x x) x))
  :hints (("Goal"
           :use (:instance max-leq-x.equal-when-member-and-ubound (y x)))))
