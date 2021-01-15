; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmin-int")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; min {i in Int | i >= 10}

(defmin-int min-geq-10 i ()
  (>= i 10))

(defthm min-geq-10.elementp-of-100
  (min-geq-10.elementp 100))

(defthm min-geq-10.lboundp-of-0
  (min-geq-10.lboundp 0)
  :hints (("Goal" :in-theory (enable min-geq-10.lboundp))))

(defthm min-geq-10.existsp-via-100-and-0
  (min-geq-10.existsp)
  :hints (("Goal" :use (:instance min-geq-10.existsp-when-nonempty-and-bounded
                        (i0 100) (i1 0)))))

(defthm min-geq-10.lboundp-of-10
  (min-geq-10.lboundp 10)
  :hints (("Goal" :in-theory (enable min-geq-10.lboundp))))

(defthm min-geq-10-is-10
  (equal (min-geq-10) 10)
  :hints (("Goal"
           :use (:instance min-geq-10.equal-when-member-and-lbound (i 10)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; min {y in Int | y >= x}, where x in Int

(defmin-int min-geq-x y (x)
  (>= y x)
  :guard (integerp x))

(defthm min-geq-x.elementp-of-x
  (min-geq-x.elementp x x)
  :hints (("Goal" :in-theory (enable min-geq-x.elementp))))

(defthm min-geq-x.lboundp-of-x
  (implies (integerp x)
           (min-geq-x.lboundp x x))
  :hints (("Goal" :in-theory (enable min-geq-x.lboundp min-geq-x.elementp))))

(defthm min-geq-x.existsp-via-x-and-x
  (implies (integerp x)
           (min-geq-x.existsp x))
  :hints (("Goal" :use (:instance min-geq-x.existsp-when-nonempty-and-bounded
                        (y0 x) (y1 x)))))

(defthm min-geq-x-is-x
  (implies (integerp x)
           (equal (min-geq-x x) x))
  :hints (("Goal"
           :use (:instance min-geq-x.equal-when-member-and-lbound (y x)))))
