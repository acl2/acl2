; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

; The original version of this book, before changing land/lior/lxor, is
; fadd-extra0.lisp.

(in-package "ACL2")

(include-book "fadd-extra0")
(include-book "land")
(include-book "lior")
(include-book "lxor")

(local (in-theory (enable land-is-land0)))
(local (in-theory (enable lior-is-lior0)))
(local (in-theory (enable lxor-is-lxor0)))

(defthmd lior-bits-1
  (equal (lior (bits x (1- n) 0)
               y
               n)
         (lior x y n))
  :hints (("Goal" :use lior0-bits-1)))

(defthmd lior-bits-2
  (equal (lior x
               (bits y (1- n) 0)
               n)
         (lior x y n))
  :hints (("Goal" :use lior0-bits-2)))

(defthmd land-bits-1
  (equal (land (bits x (1- n) 0)
               y
               n)
         (land x y n))
  :hints (("Goal" :use land0-bits-1)))

(defthmd land-bits-2
  (equal (land x
               (bits y (1- n) 0)
               n)
         (land x y n))
  :hints (("Goal" :use land0-bits-2)))

(defthmd lxor-bits-1
  (equal (lxor (bits x (1- n) 0)
               y
               n)
         (lxor x y n))
  :hints (("Goal" :use lxor0-bits-1)))

(defthmd lxor-bits-2
  (equal (lxor x
               (bits y (1- n) 0)
               n)
         (lxor x y n))
  :hints (("Goal" :use lxor0-bits-2)))

(defthmd lior-slice
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior x
                        (- (expt 2 i) (expt 2 j))
                        n)
		  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :use lior0-slice)))

(defthm land-base
  (equal (land x y 1)
         (if (and (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use land0-base))
  :rule-classes nil)

(defthm lior-base
  (equal (lior x y 1)
         (if (or (equal (bitn x 0) 1)
                 (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use lior0-base))
  :rule-classes nil)

(defthm lxor-base
  (equal (lxor x y 1)
         (if (iff (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             0
           1))
  :hints (("Goal" :use lxor0-base))
  :rule-classes nil)

(defthmd prop-as-lxor
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop x y i j)
                  (if (equal (lxor (bits x i j) (bits y i j) (1+ (- i j)))
                             (1- (expt 2 (1+ (- i j)))))
                      1
                    0)))
  :hints (("Goal" :use prop-as-lxor0
           :in-theory (enable log=))))

; new for rel5/:

(defthm half-adder
  (implies (and (bvecp u 1)
                (bvecp v 1))
           (equal (+ u v)
                  (cat (land u v 1) 1 (lxor u v 1) 1)))
  :hints (("Goal" :in-theory (enable bvecp)
           :cases ((and (equal u 0) (equal v 0))
                   (and (equal u 0) (equal v 1))
                   (and (equal u 1) (equal v 0)))))
  :rule-classes ())

(defthm full-adder
  (implies (and (bvecp u 1)
                (bvecp v 1)
                (bvecp w 1))
           (equal (+ u v w)
                  (cat (lior (land u v 1) (lior (land u w 1) (land v w 1) 1) 1) 1
                       (lxor u (lxor v w 1) 1) 1)))
  :hints (("Goal" :in-theory (enable bvecp)
           :cases ((and (equal u 0) (equal v 0) (equal w 0))
                   (and (equal u 0) (equal v 0) (equal w 1))
                   (and (equal u 0) (equal v 1) (equal w 0))
                   (and (equal u 0) (equal v 1) (equal w 1))
                   (and (equal u 1) (equal v 0) (equal w 0))
                   (and (equal u 1) (equal v 0) (equal w 1))
                   (and (equal u 1) (equal v 1) (equal w 0)))))
  :rule-classes ())

(defun rc-carry (x y k)
  (if (zp k)
      0
    (lior (land (bitn x (1- k)) (bitn y (1- k)) 1)
	  (lior (land (bitn x (1- k)) (rc-carry x y (1- k)) 1)
		(land (bitn y (1- k)) (rc-carry x y (1- k)) 1)
		1)
	  1)))

(defun rc-sum (x y k)
  (if (zp k)
      0
    (cat (lxor (bitn x (1- k))
	       (lxor (bitn y (1- k)) (rc-carry x y (1- k)) 1)
	       1)
	 1
	 (rc-sum x y (1- k))
	 (1- k))))

; Start proof of ripple-carry.

(local-defun ripple-carry-prop (x y n)
  (implies (and (natp x)
                (natp y)
                (natp n))
           (equal (+ (bits x (1- n) 0) (bits y (1- n) 0))
                  (cat (rc-carry x y n) 1 (rc-sum x y n) n))))

(local (include-book "top1"))

(local (in-theory (disable land-is-land0)))
(local (in-theory (disable lior-is-lior0)))
(local (in-theory (disable lxor-is-lxor0)))

(defthm bvecp-rc-carry
  (bvecp (rc-carry x y k) 1))

(defthm bvecp-rc-sum
  (bvecp (rc-sum x y k) k))

(local-defthm ripple-carry-prop-base
  (implies (zp n)
           (ripple-carry-prop x y n)))

; Speed things up a lot in main-1 (at least), as found by
; accumulated-persistence.
(local (in-theory (disable bits-tail
                           bvecp-tighten
                           bitn-too-small
                           bits-upper-bound
                           bits-less-than-x-gen
                           bits-less-than-x)))

(local-defthm main-1
  (implies (and (natp k)
                (natp x)
                (natp y)
                (equal (+ (bits x (+ -1 k) 0)
                          (bits y (+ -1 k) 0))
                       (cat (rc-carry x y k)
                            1
                            (rc-sum x y k)
                            k)))
           (equal (+ (bits x k 0)
                     (bits y k 0))
                  (+ (* (expt 2 k)
                        (+ (bitn x k) (bitn y k)))
                     (+ (bits x (1- k) 0)
                        (bits y (1- k) 0)))))
  :hints (("Goal" :use ((:instance bitn-plus-bits
                                   (x x)
                                   (n k)
                                   (m 0))
                        (:instance bitn-plus-bits
                                   (x y)
                                   (n k)
                                   (m 0)))))
  :rule-classes nil)

(local-defthm main-2
  (implies (and (natp k)
                (natp x)
                (natp y)
                (equal (+ (bits x (+ -1 k) 0)
                          (bits y (+ -1 k) 0))
                       (cat (rc-carry x y k)
                            1
                            (rc-sum x y k)
                            k)))
           (equal (+ (bits x k 0)
                     (bits y k 0))
                  (+ (* (expt 2 k)
                        (+ (bitn x k) (bitn y k)))
                     (cat (rc-carry x y k)
                          1
                          (rc-sum x y k)
                          k))))
  :hints (("Goal" :use main-1
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(local-defthm main-3-1
  (implies (and (natp k)
                (natp x)
                (natp y))
           (equal (cat (rc-carry x y k)
                       1
                       (rc-sum x y k)
                       k)
                  (+ (* (expt 2 k)
                        (rc-carry x y k))
                     (rc-sum x y k))))
  :hints (("Goal" :expand ((cat (rc-carry x y k)
                                1
                                (rc-sum x y k)
                                k))))
  :rule-classes nil)

(local-defthm main-3
  (implies (and (natp k)
                (natp x)
                (natp y)
                (equal (+ (bits x (+ -1 k) 0)
                          (bits y (+ -1 k) 0))
                       (cat (rc-carry x y k)
                            1
                            (rc-sum x y k)
                            k)))
           (equal (+ (bits x k 0)
                     (bits y k 0))
                  (+ (* (expt 2 k)
                        (+ (bitn x k)
                           (bitn y k)
                           (rc-carry x y k)))
                     (rc-sum x y k))))
  :hints (("Goal" :use (main-2 main-3-1)
           :in-theory (disable rc-sum rc-carry cat)))
  :rule-classes nil)

(local
 (encapsulate
  ()

  (local-defthm main-4-1
    (implies (and (natp k)
                  (natp x)
                  (natp y)
                  (equal (+ (bits x (+ -1 k) 0)
                            (bits y (+ -1 k) 0))
                         (cat (rc-carry x y k)
                              1
                              (rc-sum x y k)
                              k)))
             (equal (+ (bits x k 0)
                       (bits y k 0))
                    (+ (* (expt 2 k)
                          (let ((u (bitn x k))
                                (v (bitn y k))
                                (w (rc-carry x y k)))
                            (cat (lior (land u v 1)
                                       (lior (land u w 1) (land v w 1) 1)
                                       1)
                                 1
                                 (lxor u (lxor v w 1) 1)
                                 1)))
                       (rc-sum x y k))))
    :hints (("Goal" :use (main-3
                          (:instance full-adder
                                     (u (bitn x k))
                                     (v (bitn y k))
                                     (w (rc-carry x y k))))
             :in-theory (disable rc-sum rc-carry cat)))
    :rule-classes nil)

  (local-defthm main-4-2
    (implies (and (natp k)
                  (natp x)
                  (natp y))
             (equal (cat (rc-carry x y (1+ k))
                         1
                         (bitn (rc-sum x y (1+ k)) k)
                         1)
                    (let ((u (bitn x k))
                          (v (bitn y k))
                          (w (rc-carry x y k)))
                      (cat (lior (land u v 1)
                                 (lior (land u w 1) (land v w 1) 1)
                                 1)
                           1
                           (lxor u (lxor v w 1) 1)
                           1)))))

  (defthm main-4
    (implies (and (natp k)
                  (natp x)
                  (natp y)
                  (equal (+ (bits x (+ -1 k) 0)
                            (bits y (+ -1 k) 0))
                         (cat (rc-carry x y k)
                              1
                              (rc-sum x y k)
                              k)))
             (equal (+ (bits x k 0)
                       (bits y k 0))
                    (+ (* (expt 2 k)
                          (cat (rc-carry x y (1+ k))
                               1
                               (bitn (rc-sum x y (1+ k)) k)
                               1))
                       (rc-sum x y k))))
    :instructions (:promote
                   (:dv 2 1 2 0)
                   (:rewrite main-4-2)
                   :top
                   (:use main-4-1)
                   :split)
    :rule-classes nil)))

(local-defthm main-5
  (implies (and (natp k)
                (natp x)
                (natp y)
                (equal (+ (bits x (+ -1 k) 0)
                          (bits y (+ -1 k) 0))
                       (cat (rc-carry x y k)
                            1
                            (rc-sum x y k)
                            k)))
           (equal (+ (bits x k 0)
                     (bits y k 0))
                  (+ (* (expt 2 (1+ k))
                        (rc-carry x y (1+ k)))
                     (* (expt 2 k)
                        (bitn (rc-sum x y (1+ k)) k))
                     (rc-sum x y k))))
  :hints (("Goal" :use main-4
           :expand ((cat (rc-carry x y (1+ k))
                         1
                         (bitn (rc-sum x y (1+ k)) k)
                         1))
           :in-theory (e/d (bits-tail) (rc-sum rc-carry))))
  :rule-classes nil)

(local
 (encapsulate
  ()

  (local-defthm main-6-1-1
    (implies (and (natp k)
                  (natp x)
                  (natp y))
             (equal (bits (rc-sum x y (1+ k)) (1- k) 0)
                    (rc-sum x y k)))
    :hints (("Goal"
             :expand ((rc-sum x y (1+ k)))
             :in-theory (e/d (cat) (rc-sum)))))

  (local-defthm main-6-1
    (implies (and (natp k)
                  (natp x)
                  (natp y))
             (equal (rc-sum x y (1+ k))
                    (+ (* (expt 2 k)
                          (bitn (rc-sum x y (1+ k)) k))
                       (rc-sum x y k))))
    :hints (("Goal" :use ((:instance bitn-plus-bits
                                     (x (rc-sum x y (1+ k)))
                                     (n k)
                                     (m 0)))
             :expand ((rc-sum x y 0))
             :in-theory (e/d (bits-tail) (rc-sum rc-carry))))
    :rule-classes nil)

  (defthm main-6
    (implies (and (natp k)
                  (natp x)
                  (natp y)
                  (equal (+ (bits x (+ -1 k) 0)
                            (bits y (+ -1 k) 0))
                         (cat (rc-carry x y k)
                              1
                              (rc-sum x y k)
                              k)))
             (equal (+ (bits x k 0)
                       (bits y k 0))
                    (+ (* (expt 2 (1+ k))
                          (rc-carry x y (1+ k)))
                       (rc-sum x y (1+ k)))))
    :hints (("Goal" :use (main-5 main-6-1)
             :in-theory (disable rc-sum rc-carry)))
    :rule-classes nil)))

(local-defthm main
  (implies (and (natp k)
                (natp x)
                (natp y)
                (equal (+ (bits x (+ -1 k) 0)
                          (bits y (+ -1 k) 0))
                       (cat (rc-carry x y k)
                            1
                            (rc-sum x y k)
                            k)))
           (equal (+ (bits x k 0)
                     (bits y k 0))
                  (cat (rc-carry x y (1+ k))
                       1
                       (rc-sum x y (1+ k))
                       (1+ k))))
  :hints (("Goal" :use main-6
           :expand ((cat (rc-carry x y (1+ k))
                         1
                         (rc-sum x y (1+ k))
                         (1+ k)))
           :in-theory (e/d (bits-tail) (rc-sum rc-carry))))
  :rule-classes nil)

(local-defthm ripple-carry-prop-induction-step
  (implies (and (not (zp n))
                (ripple-carry-prop x y (1- n)))
           (ripple-carry-prop x y n))
  :hints (("Goal" :use ((:instance main (k (1- n))))
           :in-theory (disable rc-sum rc-carry cat))))

(local-defthm ripple-carry-prop-proved
  (ripple-carry-prop x y n)
  :hints (("Goal" :induct (rc-sum x y n)
           :in-theory (disable ripple-carry-prop))))

(defthm ripple-carry
  (implies (and (natp x)
                (natp y)
                (natp n))
           (equal (+ (bits x (1- n) 0) (bits y (1- n) 0))
                  (cat (rc-carry x y n) 1 (rc-sum x y n) n)))
  :hints (("Goal" :use ripple-carry-prop-proved
           :in-theory (union-theories '(ripple-carry-prop)
                                      (theory 'ground-zero))))
  :rule-classes ())
