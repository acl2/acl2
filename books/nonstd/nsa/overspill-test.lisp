; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann, May, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "nonstd/nsa/overspill" :dir :system)

(encapsulate
 ((r (k y) t)) ; classical predicate (necessary for overspill)
 (local (defun r (k y) (declare (ignore k y)) t))
 (defthm r-prop
   (and (r 0 z)
        (implies (and (natp j)
                      (standardp j))
                 (r j z)))))

(overspill r)

(defthm r-holds-on-i-large
  (let ((n (r-witness x)))
    (and (natp n)
         (i-large n)
         (implies (and (natp m) (<= m n))
                  (r m x))))
  :hints (("Goal" :use r-overspill))
  :rule-classes nil)
