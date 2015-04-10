; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann in consultation with Cuong Chau, April, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Formalization of the overspill property in ACL2(r)

; cert_param: (uses-acl2r)

(in-package "ACL2")

(encapsulate
 ((true-on-std (n x) t))
 (local (defun true-on-std (n x)
          (declare (ignore n x))
          t))
 (defthm true-on-std-holds-on-standard-natp
   (implies (and (natp n)
                 (standardp n))
            (true-on-std n x))))

(defchoose choose-n-for-not-true-on-std (n) (x)
  (and (natp n)
       (not (true-on-std n x))))

(defun large-n-for-true-on-std-aux (n x)

; Return the first n' reached below n, as we count down, such that (true-on-std
; n' x).

  (cond ((zp n) ; impossible
         0)
        ((true-on-std n x)
         n)
        (t (large-n-for-true-on-std-aux (1- n) x))))

(defun large-n-for-true-on-std (x)
  (let ((n (choose-n-for-not-true-on-std x)))
    (if (not (and (natp n)
                  (not (true-on-std n x))))
        (i-large-integer)
      (large-n-for-true-on-std-aux n x))))

(local
 (defthm large-n-for-true-on-std-aux-makes-true-on-std-true
   (implies (and (natp m)
                 (natp n)
                 (<= m n)
                 (true-on-std m x))
            (and (>= (large-n-for-true-on-std-aux n x)
                     m)
                 (true-on-std (large-n-for-true-on-std-aux n x) x)))
   :rule-classes nil))

(local
 (defthm choose-n-for-not-true-on-std-rewrite
   (implies (and (not (let ((n (choose-n-for-not-true-on-std x)))
                        (and (natp n) (not (true-on-std n x)))))
                 (natp n))
            (true-on-std n x))
   :hints (("Goal" :use choose-n-for-not-true-on-std))))

(local
 (defthm i-large-is-not-standardp
   (implies (natp x)
            (equal (i-large x)
                   (not (standardp x))))
   :hints (("Goal"
            :in-theory (disable standard-constants-are-limited
                                limited-integers-are-standard)
            :use (standard-constants-are-limited
                  limited-integers-are-standard)))))

(local
 (defthm not-standardp-i-large-integer
   (not (standardp (i-large-integer)))
   :hints (("Goal"
            :use
            (i-large-integer-is-large
             (:instance i-large-is-not-standardp
                        (x (i-large-integer))))
            :in-theory (disable i-large-is-not-standardp)))))

(local (in-theory (disable i-large)))

(local
 (defthm one-more-than-large-n-for-true-on-std-aux-makes-true-on-std-false
   (implies (and (natp n)
                 (not (true-on-std n x)))
            (not (true-on-std (1+ (large-n-for-true-on-std-aux n x)) x)))
   :rule-classes nil))

(defthm true-on-std-overspill
  (let ((n (large-n-for-true-on-std x)))
    (and (natp n)
         (i-large n)
         (true-on-std n x)))
  :hints (("Goal"
           :use ((:instance
                  large-n-for-true-on-std-aux-makes-true-on-std-true (m 1)
                  (n (choose-n-for-not-true-on-std x)))
                 (:instance
                  one-more-than-large-n-for-true-on-std-aux-makes-true-on-std-false
                  (n (choose-n-for-not-true-on-std x)))))))
