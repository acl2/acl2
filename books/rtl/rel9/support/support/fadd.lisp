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

(in-package "ACL2")

(local (include-book "stick"))
(local (include-book "lop3"))
(local (include-book "add3"))
(local (include-book "bitn"))
(local (include-book "bits"))
(local (include-book "../../arithmetic/top"))

(include-book "rtl") ; need definition of, at least, bitn
(include-book "float")

;;;**********************************************************************
;;;                     GENERATE AND PROPAGATE
;;;**********************************************************************

;;Once the lemmas below are in place, the lemmas BITS-SUM-ORIGINAL,
;;BITS-SUM-SPECIAL-CASE, and BITS-SUM-PLUS-1-ORIGINAL of book "bits" should be
;;deleted.

(defun gen (x y i j)
; generates a carry
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  (bitn x i)
	(gen x y (1- i) j))
    0))

(defun prop (x y i j)
; propagates a carry-in from below
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  0
	(prop x y (1- i) j))
    1))

(local (in-theory (enable bits-n-n-rewrite)))

(encapsulate
 ()

 (local
  (defthm gen-val-lemma-1
    (implies (not (equal (bitn x i) (bitn y i)))
             (equal (< (+ (bits x i j) (bits y i j))
                       (expt 2 (+ 1 i (* -1 j))))
                    (< (+ (bits x (1- i) j)
                          (bits y (1- i) j))
                       (expt 2 (+ i (* -1 j))))))
    :hints (("Goal" :expand ((expt 2 (+ 1 i (* -1 j))))
             :use ((:instance bitn-plus-bits
                              (x x)
                              (n i)
                              (m j))
                   (:instance bitn-plus-bits
                              (x y)
                              (n i)
                              (m j)))))))

 (local
  (defthm gen-val-lemma-2
    (implies (and (equal (bitn x i) 0)
                  (equal (bitn y i) 0))
             (< (+ (bits x i j) (bits y i j))
                (expt 2 (+ 1 i (* -1 j)))))
    :hints (("Goal" :expand ((expt 2 (+ 1 i (* -1 j))))
             :use ((:instance bitn-plus-bits
                              (x x)
                              (n i)
                              (m j))
                   (:instance bitn-plus-bits
                              (x y)
                              (n i)
                              (m j)))))))

 (local
  (defthm gen-val-lemma-3
    (implies (and (integerp j)
                  (<= j i)
                  (equal (bitn x i) 1)
                  (equal (bitn y i) 1))
             (>= (+ (bits x i j) (bits y i j))
                 (expt 2 (+ 1 i (* -1 j)))))
    :hints (("Goal" :expand ((expt 2 (+ 1 i (* -1 j))))
             :use ((:instance bitn-plus-bits
                              (x x)
                              (n i)
                              (m j))
                   (:instance bitn-plus-bits
                              (x y)
                              (n i)
                              (m j)))))))

 (defthmd gen-val
   (implies (and (natp j) (>= i j))
            (equal (gen x y i j)
                   (if (>= (+ (bits x i j) (bits y i j))
                           (expt 2 (1+ (- i j))))
                       1
                     0)))))

(encapsulate
 ()

 (local
  (defthm prop-val-lemma-1
    (implies (and (integerp j)
                  (<= j i)
                  (not (equal (bitn x i) (bitn y i))))
             (equal (equal (+ 1 (bits x i j) (bits y i j))
                           (expt 2 (+ 1 i (* -1 j))))
                    (equal (+ 1 (bits x (1- i) j)
                              (bits y (1- i) j))
                           (expt 2 (+ i (* -1 j))))))
    :hints (("Goal" :expand ((expt 2 (+ 1 i (* -1 j))))
             :use ((:instance bitn-plus-bits
                              (x x)
                              (n i)
                              (m j))
                   (:instance bitn-plus-bits
                              (x y)
                              (n i)
                              (m j)))))))

 (local
  (defthm prop-val-lemma-2
    (implies (and (integerp i)
                  (integerp j)
                  (<= j i)
                  (equal (bitn x i) (bitn y i)))
             (not (equal (+ 1 (bits x i j) (bits y i j))
                         (expt 2 (+ 1 i (* -1 j))))))
    :hints (("Goal" :expand ((expt 2 (+ 1 i (* -1 j))))
             :use ((:instance bitn-plus-bits
                              (x x)
                              (n i)
                              (m j))
                   (:instance bitn-plus-bits
                              (x y)
                              (n i)
                              (m j)))))))

 (defthmd prop-val
   (implies (and (integerp i) (natp j) (>= i j))
            (equal (prop x y i j)
                   (if (= (+ (bits x i j) (bits y i j))
                          (1- (expt 2 (1+ (- i j)))))
                       1
                     0)))))

(local
 (defthmd bits-split-rewrite
   (implies (and (natp i)
                 (natp j)
                 (natp k)
                 (< j k)
                 (<= k i))
            (equal (bits x i j)
                   (+ (* (expt 2 (- k j))
                         (bits x i k))
                      (bits x (1- k) j))))
   :hints (("Goal"
            :in-theory (e/d (cat) (cat-bits-bits))
            :use ((:instance cat-bits-bits
                             (x x)
                             (i i)
                             (j k)
                             (k (1- k))
                             (l j)
                             (m (1+ (- i j)))
                             (n (+ (- j) k))))))))

(local
 (defthm gen-extend-1
   (implies (and (natp j)
                 (integerp k)
                 (> i k)
                 (>= k j)
                 (equal (gen x y i (1+ k)) 1))
            (equal (gen x y i j)
                   (lior0 (gen x y i (1+ k))
                         (land0 (prop x y i (1+ k))
                               (gen x y k j)
                               1)
                         1)))
   :rule-classes ()))

(local
 (defthm gen-extend-2
   (implies (and (> i k)
                 (>= k j)
                 (equal (gen x y i (1+ k)) 0)
                 (equal (prop x y i (1+ k)) 0))
            (equal (gen x y i j)
                   (lior0 (gen x y i (1+ k))
                         (land0 (prop x y i (1+ k))
                               (gen x y k j)
                               1)
                         1)))
   :rule-classes ()))

(local
 (defthmd hack-2
   (implies (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (> i k)
                 (> k j))
            (equal (expt 2 (+ i (* -1 j)))
                   (* (expt 2 (+ i (* -1 k)))
                      (expt 2 (+ k (* -1 j))))))))

(local
 (defthm expt-open-+1
   (implies (force (natp n))
            (equal (expt 2 (1+ n))
                   (* 2 (expt 2 n))))))

(local
 (defthm gen-extend-3-k=j
   (implies (and (integerp i)
                 (> i j)
                 (equal (gen x y i (1+ j)) 0)
                 (equal (prop x y i (1+ j)) 1))
            (equal (gen x y i j)
                   (lior0 (gen x y i (1+ j))
                         (land0 (prop x y i (1+ j))
                               (gen x y j j)
                               1)
                         1)))
   :hints (("Goal" :in-theory (enable bits-split-rewrite hack-2 gen-val prop-val)
            :restrict ((bits-split-rewrite ((x x) (i i) (j j) (k (1+ j)))
                                           ((x y) (i i) (j j) (k (1+ j)))))))
   :rule-classes ()))

(local
 (defthm gen-extend-3-k>j
   (implies (and (integerp i)
                 (integerp k)
                 (> i k)
                 (> k j)
                 (equal (gen x y i (1+ k)) 0)
                 (equal (prop x y i (1+ k)) 1))
            (equal (gen x y i j)
                   (lior0 (gen x y i (1+ k))
                         (land0 (prop x y i (1+ k))
                               (gen x y k j)
                               1)
                         1)))
   :hints (("Goal" :in-theory (enable bits-split-rewrite hack-2 gen-val prop-val)
            :restrict ((bits-split-rewrite ((x x) (i i) (j j) (k (1+ k)))
                                           ((x y) (i i) (j j) (k (1+ k)))))))
   :rule-classes ()))

(local
 (defthm gen-extend-3
   (implies (and (integerp i)
                 (integerp k)
                 (> i k)
                 (>= k j)
                 (equal (gen x y i (1+ k)) 0)
                 (equal (prop x y i (1+ k)) 1))
            (equal (gen x y i j)
                   (lior0 (gen x y i (1+ k))
                         (land0 (prop x y i (1+ k))
                               (gen x y k j)
                               1)
                         1)))
   :hints (("Goal" :use (gen-extend-3-k>j gen-extend-3-k=j)))
   :rule-classes ()))

(local
 (defthm gen-is-0-or-1
   (implies (not (equal (gen x y i k) 0))
            (equal (gen x y i k) 1))
   :hints (("Goal" :in-theory (enable gen-val)))
   :rule-classes ((:forward-chaining :trigger-terms ((gen x y i k))))))

(local
 (defthm prop-is-0-or-1
   (implies (not (equal (prop x y i k) 0))
            (equal (prop x y i k) 1))
   :hints (("Goal" :in-theory (enable prop-val)))
   :rule-classes ((:forward-chaining :trigger-terms ((prop x y i k))))))

(defthmd gen-extend-original
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (lior0 (gen x y i (1+ k))
                        (land0 (gen x y k j)
                              (prop x y i (1+ k))
                              1)
                        1)
                  (gen x y i j)))
  :hints (("Goal" :use (gen-extend-1 gen-extend-2 gen-extend-3))))

(local
 (defthmd bitn-1-iff-at-least-2^n
   (implies (and (integerp n)
                 (bvecp x (1+ n)))
            (equal (bitn x n)
                   (if (< x (expt 2 n))
                       0
                     1)))
   :hints (("Goal" :in-theory (enable bvecp)
            :use ((:instance bitn-plus-bits
                             (x x)
                             (n n)
                             (m 0)))))))

(local
 (defthm bvecp-+
   (implies (and (not (zp k))
                 (equal n (1- k))
                 (bvecp x n)
                 (bvecp y n))
            (bvecp (+ x y) k))
   :hints (("Goal" :in-theory (enable bvecp)
            :expand ((expt 2 k))))))

(local
 (defthm bvecp-+-1
   (implies (and (not (zp k))
                 (equal n (1- k))
                 (bvecp x n)
                 (bvecp y n))
            (bvecp (+ 1 x y) k))
   :hints (("Goal" :in-theory (enable bvecp)
            :expand ((expt 2 k))))))

(local
 (defthmd integerp-expt-2-forced
   (implies (and (force (integerp n))
                 (force (<= 0 n)))
            (and (integerp (expt 2 n))
                 (< 0 (expt 2 n))))
   :rule-classes :type-prescription))

(defthm gen-extend-cor
  (implies (and (natp x)
                (natp y)
                (natp i)
                (natp j)
                (natp k)
                (> i k)
                (>= k j))
           (equal (gen x y i j)
                  (bitn (+ (bits x i (1+ k))
                           (bits y i (1+ k))
                           (gen x y k j))
                        (- i k))))
  :hints (("Goal" :use gen-extend-original
           :in-theory (enable integerp-expt-2-forced bitn-1-iff-at-least-2^n
                              gen-val prop-val)))
  :rule-classes ())

(local
 (defthm prop-extend-1
   (implies (and (integerp j)
                 (integerp k)
                 (> i k)
                 (>= k j)
                 (equal (prop x y i j) 0))
            (equal (prop x y i j)
                   (land0 (prop x y i (1+ k))
                         (prop x y k j)
                         1)))
   :rule-classes nil))

(local
 (defthm prop-extend-2
   (implies (and (integerp i)
                 (integerp j)
                 (> i k)
                 (>= k j)
                 (>= j 0)
                 (equal (prop x y i j) 1))
            (equal (prop x y i j)
                   (land0 (prop x y i (1+ k))
                         (prop x y k j)
                         1)))
   :rule-classes nil))

(defthm prop-extend-original
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (prop x y i j)
                  (land0 (prop x y i (1+ k))
                        (prop x y k j)
                        1)))
  :hints (("Goal" :use (prop-extend-1 prop-extend-2)))
  :rule-classes ())

(defthm gen-special-case-original
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (bitn (+ (bits x i j) (bits y i j)) (- i j)) 0))
           (equal (gen x y i j)
                  (lior0 (bitn x i) (bitn y i) 1)))
  :hints (("Goal" :in-theory (enable gen-val)
           :use ((:instance bitn-plus-bits (x x) (n i) (m j))
                 (:instance bitn-plus-bits (x y) (n i) (m j)))))
  :rule-classes ())

(defthm land0-gen-0
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (land0 (bits x i j) (bits y i j) (1+ (- i j))) 0))
           (equal (gen x y i j) 0))
  :hints (("Goal" :in-theory (enable gen-val)
           :use ((:instance add-2-original
                            (x (bits x i j))
                            (y (bits y i j))
                            (n (1+ (- i j))))))))

(defthmd gen-val-cor1
  (implies (natp j)
           (equal (gen x y i j)
                  (bitn (+ (bits x i j)
                           (bits y i j))
                        (1+ (- i j)))))
  :hints (("Goal" :in-theory (enable bitn-1-iff-at-least-2^n gen-val))))

(defthm bits-sum-original ; from merge.lisp
  (implies (and (integerp x)
                (integerp y)
                )
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bitn (+ (bits x (1- j) 0)
                                    (bits y (1- j) 0))
                                 j))
                        (- i j)
                        0)))
  :rule-classes ())

(local
 (defthm bits-sum-with-gen-normal-case
   (implies (and (integerp x)
                 (integerp y)
                 (integerp j)
                 (< 0 j))
            (equal (bits (+ x y) i j)
                   (bits (+ (bits x i j)
                            (bits y i j)
                            (gen x y (1- j) 0))
                         (- i j) 0)))
   :hints (("Goal" :use bits-sum-original
            :in-theory (e/d (gen-val-cor1)
                            ;; the disables below are optional but they speed up
                            ;; the proof by orders of magnitude
                            (bits-upper-bound
                             bits-less-than-x-gen
                             bits-less-than-x
                             bits-reduce-exactp
                             bits-sum-drop-irrelevant-term-2-of-2
                             bits-tail
                             bits-upper-bound-tighter
                             bits-sum-drop-irrelevant-term-1-of-2
                             bits-split-around-zero))))
   :rule-classes ()))

(defthm bits-sum
  (implies (and (integerp x) (integerp y))
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (gen x y (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-original bits-sum-with-gen-normal-case)))
  :rule-classes ())

(local
 (defthm bits-sum-special-case ; from merge.lisp
   (implies (and (= (bits (+ x y) (1- j) 0) 0)
                 (integerp x)
                 (integerp y)
                 (>= j 0)
                 )
            (equal (bits (+ x y) i j)
                   (bits (+ (bits x i j)
                            (bits y i j)
                            (logior (bitn x (1- j)) (bitn y (1- j))))
                         (- i j) 0)))
   :rule-classes ()))

; Start proof of land-gen-0-cor.

(local
 (defthm binary-land0-is-preserved-by-slice
   (implies (and (equal (binary-land0 x y n) 0)
                 (< i n)
                 (integerp n)
                 (<= 0 j)
                 (equal k (1+ (- i j))))
            (equal (binary-land0 (bits x i j)
                                (bits y i j)
                                k)
                   0))
   :hints (("Goal" :use bits-land0
            :in-theory (disable bits-land0)))))

(local
 (defthm land0-0-implies-gen-0
   (implies (and (equal (land0 x y n) 0)
                 (> n j)
                 (integerp n))
            (equal (gen x y j 0)
                   0))))

(local
 (defthm bvecp-+-bits
   (implies (and (equal (land0 x y n) 0)
                 (> n i)
                 (integerp n)
                 (integerp i)
                 (>= i j)
                 (integerp j)
                 (>= j 0)
                 (equal k (1+ (- i j))))
            (bvecp (+ (bits x i j) (bits y i j))
                   k))
   :hints (("Goal" :use ((:instance add-2-original
                                    (x (bits x i j))
                                    (y (bits y i j))
                                    (n (1+ (- i j)))))))))

(defthm land-gen-0-cor-original
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n i)
                (>= i j)
                (>= j 0)
                (= (land0 x y n) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :hints (("Goal" :use (bits-sum)))
  :rule-classes ())

(defthm bvecp-1-gen
  (bvecp (gen x y i j) 1)
  :hints (("Goal" :in-theory (enable bvecp)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((gen x y i j)))))

(defthm bvecp-1-prop
  (bvecp (prop x y i j) 1)
  :hints (("Goal" :in-theory (enable bvecp)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((prop x y i j)))))

(local
 (defthmd lior0-prop-gen-val-cor1
   (implies (and (integerp x)
                 (integerp y)
                 (integerp j)
                 (< 0 j))
            (equal (lior0 (prop x y (1- j) 0)
                         (gen x y (1- j) 0)
                         1)
                   (bitn (+ 1
                            (bits x (1- j) 0)
                            (bits y (1- j) 0))
                         j)))
   :hints (("Goal" :in-theory (enable prop-val gen-val bitn-1-iff-at-least-2^n
                                      bvecp-1-gen)))))

(defthm bits-sum-plus-1-original
  (implies (and (integerp x)
                (integerp y)
                (natp i)
                (natp j)
                (>= i j)
                (>= j 0))
           (equal (bits (+ 1 x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bitn (+ 1
                                    (bits x (1- j) 0)
                                    (bits y (1- j) 0))
                                 j))
                        (- i j) 0)))
  :rule-classes ())

(local
 (defthm bits-sum-plus-1-with-prop-gen-normal
   (implies (and (integerp x)
                 (integerp y)
                 (integerp i)
                 (integerp j)
                 (>= i j)
                 (> j 0))
            (equal (bits (+ 1 x y) i j)
                   (bits (+ (bits x i j)
                            (bits y i j)
                            (lior0 (prop x y (1- j) 0)
                                  (gen x y (1- j) 0)
                                  1))
                         (- i j) 0)))
   :hints (("Goal" :use bits-sum-plus-1-original
            :in-theory (e/d (lior0-prop-gen-val-cor1)
                            ;; the disables below are optional but they speed up
                            ;; the proof by orders of magnitude
                            (bits-upper-bound
                             bits-less-than-x-gen
                             bits-less-than-x
                             bits-reduce-exactp
                             bits-sum-drop-irrelevant-term-2-of-2
                             bits-tail
                             bits-upper-bound-tighter
                             bits-sum-drop-irrelevant-term-1-of-2
                             bits-split-around-zero))))
   :rule-classes ()))

(defthm bits-sum-plus-1-with-prop-gen-original
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0))
           (equal (bits (+ 1 x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (lior0 (prop x y (1- j) 0)
                                 (gen x y (1- j) 0)
                                 1))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-plus-1-original bits-sum-plus-1-with-prop-gen-normal)
           :in-theory (e/d (lior0-prop-gen-val-cor1)
                           ;; the disables below are optional but they speed up
                           ;; the proof by orders of magnitude
                           (bits-upper-bound
                            bits-less-than-x-gen
                            bits-less-than-x
                            bits-reduce-exactp
                            bits-sum-drop-irrelevant-term-2-of-2
                            bits-tail
                            bits-upper-bound-tighter
                            bits-sum-drop-irrelevant-term-1-of-2
                            bits-split-around-zero))))
  :rule-classes ())

;;;**********************************************************************
;;;                     THREE-INPUT ADDITION
;;;**********************************************************************

(defthm add-3-original
    (implies (and (not (zp n))
		  (bvecp x n)
		  (bvecp y n)
		  (bvecp z n))
	     (equal (+ x y z)
		    (+ (lxor0 x (lxor0 y z n) n)
		       (* 2 (lior0 (land0 x y n)
				  (lior0 (land0 x z n)
					(land0 y z n)
					n)
				  n)))))
  :rule-classes ())

(defthm add-2-original
    (implies (and (not (zp n))
		  (bvecp x n)
		  (bvecp y n))
	     (equal (+ x y)
		    (+ (lxor0 x y n)
		       (* 2 (land0 x y n)))))
  :rule-classes ())


;;;**********************************************************************
;;;                    TRAILING ONE PREDICTION
;;;**********************************************************************

(defthm top-thm-1-original
  (implies (and (natp n)
                (natp k)
                (< k n)
                (integerp a)
                (integerp b))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lnot (lxor0 a b n) n) k 0) 0)))
  :rule-classes ())

(defund sigm-0 (a b c n)
  (if (= c 0)
      (lnot (lxor0 a b n) n)
    (lxor0 a b n)))

(defund kap-0 (a b c n)
  (if (= c 0)
      (* 2 (lior0 a b n))
    (* 2 (land0 a b n))))

(defund tau-0 (a b c n)
  (lnot (lxor0 (sigm-0 a b c n) (kap-0 a b c n) (1+ n)) (1+ n)))

(defthm bvecp-sigm-0
  (bvecp (sigm-0 a b c n) n)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((sigm-0 a b c n)))))

(defthm bvecp-kap-0
  (implies (and (integerp n) (<= 0 n))
           (bvecp (kap-0 a b c n) (1+ n)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((kap-0 a b c n)))))

(defthm bvecp-tau-0
  (bvecp (tau-0 a b c n) (1+ n))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((tau-0 a b c n)))))

(local (include-book "lextra0")) ; for lnot-lxor0

(defthm top-thm-2-old
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
		  (equal (bits (tau-0 a b c n) k 0) 0)))
  :rule-classes ())

(encapsulate ()

(local
 (defthm top-thm-2-0
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n))
            (equal (equal (bits (+ a b) k 0) 0)
                   (equal (bits (lxor0 (lxor0 a b n)
                                      (cat (lior0 a b n) n 0 1)
                                      (1+ n))
                                k 0)
                          0)))
   :hints (("Goal"
            :expand ((:free (x y) (cat x n y 1)))
            :use
            ((:instance top-thm-2-old (c 0))
             (:instance lnot-lxor0
                        (x (lnot (binary-lxor0 (bits a k 0)
                                              (bits b k 0)
                                              (+ 1 k))
                                 (+ 1 k)))
                        (y (* 2
                              (binary-lior0 (bits a (1- k) 0)
                                           (bits b (1- k) 0)
                                           k)))
                        (n (+ 1 k))))
            :in-theory (e/d (tau-0 kap-0 sigm-0 bitn-negative-bit-of-integer)
                            (bitn-known-not-0-replace-with-1))))
   :rule-classes ()))

#|
Proof of top-thm-2-1 from top-thm-2-0:

Case 1: (bitn a 0) = (bitn b 0).  Then (bitn (+ a b 1) 0) = 1 by
top-thm-1, so (bits (+ a b 1) k 0) != 0, by bits-plus-bitn.  We can also use
bits-plus-bitn so that it suffices to show that bit 0 of the outermost lxor0
call is 1, which is clear.

Case 2: Without loss of generality, (bitn a 0) = 0 and (bitn b 0) = 1.  We want
to apply top-thm-2-0 with a replaced by a+1.  Thus it suffices to prove:

(lxor0 (lxor0 a b n)
      (cat (lior0 a b n) n 1 1)
      (1+ n))
=
(lxor0 (lxor0 (1+ a) b n)
      (cat (lior0 (1+ a) b n) n 0 1)
      (1+ n))

The key observation is that for all integers i, (bitn (1+ a) i) = (bitn a i)
if i is positive, and (bitn (1+ a) 0) = 1.  {This follows from the fact that
(bits (1+ a) m 0) = (cat (bits a m 1) m 1 1).}  By lemma
sumbits-badguy-is-correct, it suffices to prove that the nth bit of each of the
two sides above is the same for an arbitrary natp n.  We have rules for bitn of
lxor0, cat, and lior0 that should make this proof pretty automatic.

|# ; |

(local
 (defthm top-thm-2-1-1-1
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n)
                 (equal (bitn a 0) (bitn b 0)))
            (not (equal (bits (+ a b 1) k 0) 0)))
   :hints (("Goal" :use ((:instance bits-plus-bitn
                                    (x (+ a b 1))
                                    (n k)
                                    (m 0))
                         (:instance top-thm-1-original
                                    (k 0)))))
   :rule-classes ()))

(local (in-theory (disable bitn-known-not-0-replace-with-1)))

(local
 (defthm top-thm-2-1-1-2-1
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n)
                 (equal (bitn a 0) (bitn b 0)))
            (not (equal (bitn (bits (lxor0 (lxor0 a b n)
                                          (cat (lior0 a b n) n 1 1)
                                          (1+ n))
                                    k 0)
                              0)
                        0)))
   :hints (("Goal" :use ((:instance bits-plus-bitn
                                    (x a)
                                    (n k)
                                    (m 0))
                         (:instance bits-plus-bitn
                                    (x b)
                                    (n k)
                                    (m 0))
                         (:instance bvecp-1-rewrite
                                    (x (bitn a 0)))
                         (:instance bvecp-1-rewrite
                                    (x (bitn b 0))))))
   :rule-classes ()))

(local
 (defthm top-thm-2-1-1-2
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n)
                 (equal (bitn a 0) (bitn b 0)))
            (not (equal (bits (lxor0 (lxor0 a b n)
                                    (cat (lior0 a b n) n 1 1)
                                    (1+ n))
                              k 0)
                        0)))
   :hints (("Goal" :use top-thm-2-1-1-2-1))
   :rule-classes nil))

(local
 (defthm top-thm-2-1-1
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n)
                 (equal (bitn a 0) (bitn b 0)))
            (equal (equal (bits (+ a b 1) k 0) 0)
                   (equal (bits (lxor0 (lxor0 a b n)
                                      (cat (lior0 a b n) n 1 1)
                                      (1+ n))
                                k 0)
                          0)))
   :hints (("Goal" :use (top-thm-2-1-1-1 top-thm-2-1-1-2)))
   :rule-classes ()))

; Start proof of top-thm-2-1-2-1.

(local
 (encapsulate
  ()

  (local
   (defthm top-thm-2-1-2-2-1-1-1-1
     (implies (and (natp m)
                   (< 0 m)
                   (integerp a)
                   (equal (bitn a 0) 0))
              (equal (land0 1 a m)
                     0))
     :hints (("Goal" :use ((:instance land0-slice (x a) (i 1) (j 0) (n m)))))))

  (local
   (defthm top-thm-2-1-2-2-1-1-1
     (implies (and (natp m)
                   (<= 0 m)
                   (integerp a)
                   (equal (bitn a 0) 0))
              (equal (bits (1+ a) m 0)
                     (cat (bits a m 1) m 1 1)))
     :hints (("Goal" :use ((:instance land-gen-0-cor-original
                                      (x a)
                                      (y 1)
                                      (n (1+ m))
                                      (i m)
                                      (j 0))
                           (:instance bits-plus-bitn
                                      (x a)
                                      (n m)
                                      (m 0)))
              :expand ((cat (bits a m 1) m 1 1))))))

  (defthm top-thm-2-1-2-2-1-1
    (implies (and (natp m)
                  (<= 0 m)
                  (integerp a)
                  (equal (bitn a 0) 0))
             (equal (bitn (bits (1+ a) m 0) m)
                    (bitn (cat (bits a m 1) m 1 1) m)))
    :rule-classes nil)))

(local
 (defthm top-thm-2-1-2-2-1
   (implies (and (natp m)
                 (integerp a)
                 (equal (bitn a 0) 0))
            (equal (bitn (1+ a) m)
                   (if (equal m 0)
                       1
                     (bitn a m))))
   :hints (("Goal" :use top-thm-2-1-2-2-1-1))))

(local
 (defthmd lxor0-lnot-1
   (equal (lxor0 (lnot x n) y n)
          (lnot (lxor0 x y n) n))
   :hints (("Goal" :in-theory (enable lnot-lxor0)))))

(local
 (defthmd lxor0-lnot-2
   (equal (lxor0 y (lnot x n) n)
          (lnot (lxor0 x y n) n))
   :hints (("Goal" :in-theory (enable lnot-lxor0)))))

(local
 (defthm top-thm-2-1-2-2
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n)
                 (equal (bitn a 0) 0)
                 (equal (bitn b 0) 1))
            (equal (lxor0 (lxor0 a b n)
                         (cat (lior0 a b n) n 1 1)
                         (1+ n))
                   (lxor0 (lxor0 (1+ a) b n)
                         (cat (lior0 (1+ a) b n) n 0 1)
                         (1+ n))))
   :hints (("Goal" :use ((:instance sumbits-badguy-is-correct
                                    (x (lxor0 (lxor0 a b n)
                                             (cat (lior0 a b n) n 1 1)
                                             (1+ n)))
                                    (y (lxor0 (lxor0 (1+ a) b n)
                                             (cat (lior0 (1+ a) b n) n 0 1)
                                             (1+ n)))
                                    (k (1+ n))))
            :in-theory (enable lxor0-lnot-1 lxor0-lnot-2)))
   :rule-classes ()))

(local
 (defthm top-thm-2-1-2
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n)
                 (equal (bitn a 0) 0)
                 (equal (bitn b 0) 1))
            (equal (equal (bits (+ a b 1) k 0) 0)
                   (equal (bits (lxor0 (lxor0 a b n)
                                      (cat (lior0 a b n) n 1 1)
                                      (1+ n))
                                k 0)
                          0)))
   :hints (("Goal" :use (top-thm-2-1-2-2
                         (:instance top-thm-2-0
                                    (a (1+ a))))))
   :rule-classes ()))

(local
 (defthm top-thm-2-1
   (implies (and (natp n)
                 (integerp a)
                 (integerp b)
                 (natp k)
                 (< k n))
            (equal (equal (bits (+ a b 1) k 0) 0)
                   (equal (bits (lxor0 (lxor0 a b n)
                                      (cat (lior0 a b n) n 1 1)
                                      (1+ n))
                                k 0)
                          0)))
   :hints (("Goal" :use (top-thm-2-1-1
                         top-thm-2-1-2
                         (:Instance top-thm-2-1-2 (a b) (b a)))
            ;; for efficiency only:
            :in-theory (disable;;bits-cat
                        bits-lxor0 ; important
                        ;;bvecp-tighten
                        bits-tail ; pretty impt
                        power2-integer ; a little impt
                        bits-sum-drop-irrelevant-term-2-of-2 ; barely impt
                        ;;bits-reduce-exactp
                        ;;expo-unique-eric-2
                        ;;bits-split-around-zero
                        )))
   :rule-classes ()))

(defthm top-thm-2-original
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
                  (equal (bits (lxor0 (lxor0 a b n)
                                     (cat (lior0 a b n) n c 1)
                                     (1+ n))
                               k 0)
                         0)))
  :hints (("Goal" :use (top-thm-2-0 top-thm-2-1)
           :in-theory (theory 'ground-zero)))
  :rule-classes nil)

)

(local
 (defthm top-thm-3-lemma
   (implies (and (integerp a) (integerp b) (integerp n))
            (equal (land0 (bits a (1- n) 0)
                         (bits b (1- n) 0)
                         n)
                   (land0 a b n)))
   :hints (("Goal" :use ((:instance land0-ignores-bits
                                    (x a) (y (bits b (1- n) 0)) (n n))
                         (:instance land0-ignores-bits
                                    (x b) (y a) (n n)))))
   :rule-classes nil))

(defthm top-thm-3-original
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lnot (lxor0 (lxor0 a b n)
				           (cat (land0 a b n) n 0 1)
					   (1+ n))
				     (1+ n))
			       k 0)
			 0)))
  :hints (("Goal" :use (top-thm-3-lemma (:instance top-thm-2-old (c 1)))
           :expand ((cat (land0 a b n) n 0 1))
           :in-theory (enable tau-0 kap-0 sigm-0)))
  :rule-classes ())


;;;**********************************************************************
;;;                  LEADING ONE PREDICTION
;;;**********************************************************************

;add in some more theorems about the functions defined below?

(defthm lop-thm-1-original
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (= e (expo a))
		  (< (expo b) e)
		  (= lambda
		     (lior0 (* 2 (mod a (expt 2 e)))
			   (lnot (* 2 b) (1+ e))
			   (1+ e))))
	     (or (= (expo (- a b)) (expo lambda))
		 (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())

(defun lamt-0 (a b e)
  (lxor0 a (lnot b (1+ e)) (1+ e)))

(defun lamg-0 (a b e)
  (land0 a (lnot b (1+ e)) (1+ e)))

(defun lamz-0 (a b e)
  (lnot (lior0 a (lnot b (1+ e)) (1+ e)) (1+ e)))

(defun lam1-0 (a b e)
  (land0 (bits (lamt-0 a b e) e 2)
	(land0 (bits (lamg-0 a b e) (1- e) 1)
	      (lnot (bits (lamz-0 a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam2-0 (a b e)
  (land0 (lnot (bits (lamt-0 a b e) e 2) (1- e))
	(land0 (bits (lamz-0 a b e) (1- e) 1)
	      (lnot (bits (lamz-0 a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam3-0 (a b e)
  (land0 (bits (lamt-0 a b e) e 2)
	(land0 (bits (lamz-0 a b e) (1- e) 1)
	      (lnot (bits (lamg-0 a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam4-0 (a b e)
  (land0 (lnot (bits (lamt-0 a b e) e 2) (1- e))
	(land0 (bits (lamg-0 a b e) (1- e) 1)
	      (lnot (bits (lamg-0 a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam0-0 (a b e)
  (lior0 (lam1-0 a b e)
	(lior0 (lam2-0 a b e)
	      (lior0 (lam3-0 a b e)
		    (lam4-0 a b e)
		    (1- e))
	      (1- e))
	(1- e)))

(defun lamb-0 (a b e)
  (+ (* 2 (lam0-0 a b e))
     (lnot (bitn (lamt-0 a b e) 0) 1)))

(defthm lop-thm-2-original
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (lamb-0 a b e) 0))
		  (or (= (expo (- a b)) (expo (lamb-0 a b e)))
		      (= (expo (- a b)) (1- (expo (lamb-0 a b e)))))))
  :rule-classes ())

; new for rel5:

(defthmd gen-val-cor2
  (implies (and (natp x)
                (natp y)
		(natp i))
           (equal (+ (bits x i 0) (bits y i 0))
		  (+ (* (expt 2 (1+ i)) (gen x y i 0))
		     (bits (+ x y) i 0))))
  :hints (("Goal" :use ((:instance bitn-plus-bits
                                   (x (+ (bits x i 0) (bits y i 0)))
                                   (n (1+ i))
                                   (m 0))
                        (:instance gen-val-cor1
                                   (j 0))))))

(defthm bits-sum-cor-lemma
  (implies (and (integerp x)
                (integerp y)
                (>= i j)
                (>= j 0)
                (= (gen x y i j) 0))
           (equal (bits (+ (bits x i j)
                           (bits y i j))
                        (- i j) 0)
                  (+ (bits x i j)
                     (bits y i j))))
  :hints (("Goal" :use ((:instance bitn-plus-bits
                                   (x (+ (bits x i j) (bits y i j)))
                                   (n (1+ (- i j)))
                                   (m 0))
                        gen-val-cor1)))
  :rule-classes nil)

(defthmd bits-sum-cor
  (implies (and (integerp x)
                (integerp y)
                (>= i j)
                (>= j 0)
                (= (gen x y i j) 0)
                (= (gen x y (1- j) 0) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :hints (("Goal" :use (bits-sum bits-sum-cor-lemma))))
