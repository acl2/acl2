#|

  A Simple Random Number Generator              Version 0.1
  Jared Davis <jared@cs.utexas.edu>          February 25, 2004

  This file is in the public domain.  You can freely use it for any
  purpose without restriction.

  This is just a basic pure multiplicative pseudorandom number gen-
  erator.  *M31* is the 31st mersenne prime, and *P1* is 7^5 which
  is a primitive root of *M31*, ensuring that our period is M31 - 1.
  This idea is described in "Elementary Number Theory and its Appli-
  cations" by Kenneth H. Rosen, Fourth Edition, Addison Wesley 1999,
  in Chapter 10.1, pages 356-358.

  The random number generator uses a stobj, rand, to store the seed.
  You will want to use the following functions:

    (genrandom <max> rand)
       Returns (mv k rand) where 0 <= k < max.

    (update-seed <newseed> rand)
       Manually switch to a new seed.  By default, a large messy num-
       ber will be used.  You probably don't need to change it, but
       it might be good if you want to be able to reproduce your re-
       sults in the future.

  Normally we are not particularly interested in reasoning about ran-
  dom numbers.  However, we can say that the number k generated is an
  an integer, and that 0 <= k < max when max is a positive integer.
  See the theorems genrandom-minimum and genrandom-maximum.

|#

(in-package "ACL2")
(set-verify-guards-eagerness 2)

(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defconst *M31* 2147483647)
(defconst *P1* 16807)

(defstobj rand
  (seed :type integer :initially 1382728371))



(defun getseed (rand)
  (declare (xargs :stobjs (rand)))
  (let ((s (seed rand)))
    (if (and (integerp s) (<= 0 s))
        s
      0)))

(local (defthm getseed-integer
  (and (integerp (getseed rand))
       (<= 0 (getseed rand)))
  :rule-classes :type-prescription))

(in-theory (disable getseed))



(defun genrandom (max rand)
  (declare (xargs :stobjs (rand)
                  :guard (and (integerp max) (> max 0))))
  (let* ((new-seed (mod (* *P1* (getseed rand)) *M31*))
         (rand (update-seed new-seed rand)))
    (mv (mod new-seed max) rand)))

(defthm genrandom-integer
  (implies (integerp max)
           (integerp (car (genrandom max rand)))))

(defthm genrandom-minimum
  (implies (and (integerp max)
                (< 0 max))
           (<= 0 (car (genrandom max rand)))))

(defthm genrandom-maximum
  (implies (and (integerp max)
                (< 0 max))
           (< (car (genrandom max rand)) max)))

(in-theory (disable genrandom))

