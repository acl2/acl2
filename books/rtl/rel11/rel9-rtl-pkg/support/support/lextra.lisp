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

(in-package "RTL")

(include-book "land")
(include-book "lior")
(include-book "lxor")
(include-book "cat")
(local (include-book "lextra0"))
(local (include-book "land0"))
(local (include-book "lior0"))
(local (include-book "lxor0"))
(local (include-book "merge2"))

(local (in-theory (current-theory 'lextra0-start)))
(local (in-theory (e/d (land-is-land0 lior-is-lior0 lxor-is-lxor0)
                       (binary-land binary-lior binary-lxor))))

;theorems mixing two or more of the new logical operators.

;BOZO really the -1 and -2 names below should be switched?

(defthmd lior-land-1
  (equal (lior x (land y z n) n)
         (land (lior x y n) (lior x z n) n))
  :hints (("Goal" :in-theory (enable lior0-land0-1))))

(defthmd lior-land-2
  (equal (lior (land y z n) x n)
         (land (lior x y n) (lior x z n) n))
  :hints (("Goal" :in-theory (enable lior0-land0-2))))

(defthmd land-lior-1
  (equal (land x (lior y z n) n)
         (lior (land x y n) (land x z n) n))
  :hints (("Goal" :in-theory (enable land0-lior0-1))))

(defthmd land-lior-2
  (equal (land (lior y z n) x n)
         (lior (land x y n) (land x z n) n))
  :hints (("Goal" :in-theory (enable land0-lior0-2))))

(defthmd lior-land-lxor
  (equal (lior (land x y n) (lior (land x z n) (land y z n) n) n)
         (lior (land x y n) (land (lxor x y n) z n) n))
  :hints (("Goal" :in-theory (enable lior0-land0-lxor0))))

(defthmd lxor-rewrite
  (equal (lxor x y n)
         (lior (land x (lnot y n) n)
               (land y (lnot x n) n)
               n))
  :hints (("Goal" :in-theory (enable lxor0-rewrite))))

(defthmd lnot-lxor
  (equal (lnot (lxor x y n) n)
         (lxor (lnot x n) y n))
  :hints (("Goal" :in-theory (enable lnot-lxor0))))

;consider enabling?
(defthmd lnot-lior
  (equal (lnot (lior x y n) n)
         (land (lnot x n) (lnot y n) n))
  :hints (("Goal" :in-theory (enable lnot-lior0))))

;consider enabling?
(defthmd lnot-land
  (equal (lnot (land x y n) n)
         (lior (lnot x n) (lnot y n) n))
  :hints (("Goal" :in-theory (enable lnot-land0))))

; Added for rel5.  (Much of this really "should" go in lextra-proofs.lisp, but
; it was developed here before that realization, and moving it doesn't seem
; worth the trouble.)

(defthmd land-cat
  (implies (and (case-split (natp n))
                (case-split (integerp m))
                (> m 0)
                (equal l (+ m n)))
           (equal (land (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (land x1 x2 m) m (land y1 y2 n) n)))
  :hints (("Goal" :in-theory (enable land0-cat))))

(defthm land-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (land c (cat x2 m y2 n) l)
                  (cat (land (bits c (+ -1 m n) n) x2 m)
                       m
                       (land (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use land0-cat-constant)))

(defthmd lior-cat
  (implies (and (case-split (natp n))
                (case-split (integerp m))
                (> m 0)
                (equal l (+ m n)))
           (equal (lior (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (lior x1 x2 m) m (lior y1 y2 n) n)))
  :hints (("Goal" :in-theory (enable lior0-cat))))

(defthm lior-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (lior c (cat x2 m y2 n) l)
                  (cat (lior (bits c (+ -1 m n) n) x2 m)
                       m
                       (lior (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use lior0-cat-constant)))

(defthmd lxor-cat
  (implies (and (case-split (natp n))
                (case-split (integerp m))
                (> m 0)
                (equal l (+ m n)))
           (equal (lxor (cat x1 m y1 n) (cat x2 m y2 n) l)
                  (cat (lxor x1 x2 m) m (lxor y1 y2 n) n)))
  :hints (("Goal" :in-theory (enable lxor0-cat))))

(defthm lxor-cat-constant
  (implies (and (case-split (integerp n))
                (case-split (integerp m))
                (syntaxp (quotep c))
                (> n 0)
                (> m 0)
                (equal l (+ m n)))
           (equal (lxor c (cat x2 m y2 n) l)
                  (cat (lxor (bits c (+ -1 m n) n) x2 m)
                       m
                       (lxor (bits c (1- n) 0) y2 n)
                       n)))
  :hints (("Goal" :use lxor0-cat-constant)))

(defthm lxor-bnd
  (<= (lxor x y n) (lior x y n))
  :hints (("Goal"
           :in-theory
           (e/d (lxor lior)
                (lxor-is-lxor0 lior-is-lior0))))
  :rule-classes (:rewrite :linear))

; Start proof of lxor-slice.

(local (include-book "../../arithmetic/top"))

(local (in-theory (enable a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a12 a13 a14 a15
                          bits-lnot bits-bits
                          bits-with-indices-in-the-wrong-order
                          lnot-bvecp-simple lnot-bvecp
                          bits-0)))

(local
 (defthmd lxor-slice-1-1
   (implies (and (<= j i)
                 (<= i n)
                 (integerp n)
                 (integerp i)
                 (integerp j)
                 (<= 0 j))
            (equal (bits x (1- n) 0)
                   (cat (bits x (1- n) i) (- n i)
                        (bits x (1- i) j) (- i j)
                        (bits x (1- j) 0) j)))
   :hints (("Goal" :use ((:instance bits-plus-bits
                                    (n (1- n))
                                    (m 0)
                                    (p i))
                         (:instance bits-plus-bits
                                    (n (1- i))
                                    (m 0)
                                    (p j)))))))

(local
 (encapsulate
  ()

  (local
   (defthm lxor-slice-1-2-1
     (implies (and (<= 0 j)
                   (<= j i)
                   (<= i n)
                   (integerp n)
                   (integerp i)
                   (integerp j))
              (equal (bits (- (expt 2 i) (expt 2 j))
                           (+ -1 n)
                           0)
                     (- (expt 2 i) (expt 2 j))))
     :hints (("Goal" :use ((:instance expt-weak-monotone (n i) (m n))
                           (:instance expt-weak-monotone (n j) (m i)))
              :in-theory (e/d (bits-reduce) (expt-compare))))
     :rule-classes nil))

  (local
   (defthm lxor-slice-1-2-2
     (implies (and (<= 0 i)
                   (<= i n)
                   (integerp n)
                   (integerp i))
              (equal (bits (+ -1 (expt 2 i))
                           (+ -1 n)
                           0)
                     (+ -1 (expt 2 i))))
     :hints (("Goal" :use ((:instance lxor-slice-1-2-1 (j 0)))))))

  (defthm lxor-slice-1-2-3 ; used in final lxor-slice proof
    (implies (and (<= 0 j)
                  (<= j i)
                  (<= i n)
                  (integerp n)
                  (integerp i)
                  (integerp j))
             (equal (bits (+ (expt 2 i) (* -1 (expt 2 j)))
                          (+ -1 n)
                          0)
                    (+ (expt 2 i) (* -1 (expt 2 j)))))
    :hints (("Goal" :use ((:instance lxor-slice-1-2-1 (j j))))))

  (defthm lxor-slice-1-2
    (implies (and (<= j i)
                  (<= i n)
                  (integerp n)
                  (integerp i)
                  (integerp j)
                  (<= 0 j))
             (equal (bits (- (expt 2 i) (expt 2 j)) (1- n) 0)
                    (cat 0 (- n i)
                         (1- (expt 2 (- i j))) (- i j)
                         0 j)))
    :hints (("Goal" :in-theory (enable cat))))))

(local
 (defthm lxor-slice-1
   (implies (and (<= j i)
                 (<= i n)
                 (integerp n)
                 (integerp i)
                 (integerp j)
                 (<= 0 j))
            (equal (lxor (cat (bits x (1- n) i) (- n i)
                              (bits x (1- i) j) (- i j)
                              (bits x (1- j) 0) j)
                         (cat 0 (- n i)
                              (1- (expt 2 (- i j))) (- i j)
                              0 j)
                         n)
                   (lxor (bits x (1- n) 0)
                         (bits (- (expt 2 i) (expt 2 j)) (1- n) 0)
                         n)))
   :hints (("Goal" :use (lxor-slice-1-1 lxor-slice-1-2)))
   :rule-classes nil))

(local
 (defthm lxor-slice-2
   (implies (and (< j i)
                 (< i n)
                 (integerp n)
                 (integerp i)
                 (integerp j)
                 (<= 0 j))
            (equal (lxor (cat (bits x (1- n) i) (- n i)
                              (bits x (1- i) j) (- i j)
                              (bits x (1- j) 0) j)
                         (cat 0 (- n i)
                              (1- (expt 2 (- i j))) (- i j)
                              0 j)
                         n)
                   (cat (bits x (1- n) i) (- n i)
                        (lnot (bits x (1- i) j) (- i j)) (- i j)
                        (bits x (1- j) 0) j)))
   :hints (("Goal" :in-theory (e/d (lxor0-cat)
                                   (cat-0 cat-0-alt cat-bits-bits))
            :use ((:instance lxor0-ones
                             (x (bits x (+ -1 i) j))
                             (n (+ i (* -1 j)))))))
   :rule-classes nil))

(local
 (defthm lxor-slice-3 ; i=j case
   (implies (and (<= i n)
                 (<= 0 i)
                 (integerp n)
                 (integerp i))
            (equal (lxor (bits x (1- n) 0)
                         0
                         n)
                   (cat (bits x (1- n) i) (- n i)
                        (lnot (bits x (1- i) i) 0) 0
                        (bits x (1- i) 0) i)))
   :hints (("Goal" :in-theory (enable cat)))
   :rule-classes nil))

(local
 (encapsulate
  ()

  (local
   (defthm hack-1
     (implies (natp n)
              (equal (bits (+ -1 (* 2 (expt 2 n)))
                           n
                           0)
                     (+ -1 (* 2 (expt 2 n)))))
     :hints (("Goal" :in-theory (enable bits-reduce)))))

  (local
   (defthm hack-2
     (implies (and (< j n)
                   (integerp n)
                   (integerp j)
                   (< 0 j))
              (equal (bits (+ -1 (expt 2 (+ n (* -1 j))))
                           (+ -1 n (* -1 j))
                           0)
                     (+ -1 (expt 2 (+ n (* -1 j))))))
     :hints (("Goal"
              :use ((:instance bits-reduce
                               (x (+ -1 (expt 2 (+ n (* -1 j)))))
                               (i (+ -1 n (* -1 j)))))))))

  (defthm lxor-slice-2-i=n
    (implies (and (< j n)
                  (integerp n)
                  (integerp j)
                  (<= 0 j))
             (equal (lxor (cat (bits x (1- n) n) 0
                               (bits x (1- n) j) (- n j)
                               (bits x (1- j) 0) j)
                          (cat 0 0
                               (1- (expt 2 (- n j))) (- n j)
                               0 j)
                          n)
                    (cat (bits x (1- n) n) 0
                         (lnot (bits x (1- n) j) (- n j)) (- n j)
                         (bits x (1- j) 0) j)))
    :hints (("Goal" :in-theory (e/d (lxor0-cat)
                                    (cat-0 cat-0-alt cat-bits-bits))
             :use ((:instance lxor0-ones
                              (x (bits x (+ -1 n) j))
                              (n (+ n (* -1 j)))))))
    :rule-classes nil)))

(defthmd lxor-slice
  (implies (and (<= j i)
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j))
           (equal (lxor x
                        (- (expt 2 i) (expt 2 j))
                        n)
                  (cat (bits x (1- n) i) (- n i)
                       (lnot (bits x (1- i) j) (- i j)) (- i j)
                       (bits x (1- j) 0) j)))
  :hints (("Goal" :use (lxor-slice-1 lxor-slice-2 lxor-slice-2-i=n)
           :in-theory (e/d (lxor-bits-1) (expt)))))

; Start proof of lxor-expt, using lxor-slice, which is in this file because it
; is a corollary of lxor-slice.

(local
 (defthm lxor-expt-1-1
   (implies (and (natp n)
                 (natp k)
                 (< k n))
            (equal (lxor x (expt 2 k) n)
                   (cat (bits x (1- n) (1+ k)) (1- (- n k))
                        (lnot (bits x k k) 1) 1
                        (bits x (1- k) 0) k)))
   :hints (("Goal" :use ((:instance lxor-slice
                                    (i (1+ k))
                                    (j k)))))
   :rule-classes nil))

(local
 (defthm lxor-expt-1-2
   (implies (and (natp n)
                 (natp k)
                 (< k n))
            (equal (cat (bits x (1- n) (1+ k)) (1- (- n k))
                        (lnot (bits x k k) 1) 1
                        (bits x (1- k) 0) k)
                   (+ (* (expt 2 (1+ k)) (bits x (1- n) (1+ k)))
                      (cat (lnot (bits x k k) 1) 1
                           (bits x (1- k) 0) k))))
   :hints (("Goal" :use ((:instance binary-cat
                                    (x (bits x (1- n) (1+ k)))
                                    (m (1- (- n k)))
                                    (y (cat (lnot (bits x k k) 1) 1
                                            (bits x (1- k) 0) k))
                                    (n (+ 1 k))))))
   :rule-classes nil))

(local
 (defthm lxor-expt-1-3
   (implies (and (natp n)
                 (natp k)
                 (< k n))
            (equal (cat (lnot (bits x k k) 1) 1
                        (bits x (1- k) 0) k)
                   (+ (* (expt 2 k) (lnot (bits x k k) 1))
                      (bits x (1- k) 0))))
   :hints (("Goal" :use ((:instance binary-cat
                                    (x (lnot (bits x k k) 1))
                                    (m 1)
                                    (y (bits x (1- k) 0))
                                    (n k)))))
   :rule-classes nil))

(local
 (defthmd lxor-expt-1
   (implies (and (natp n)
                 (natp k)
                 (< k n))
            (equal (lxor x (expt 2 k) n)
                   (+ (* (expt 2 (1+ k)) (bits x (1- n) (1+ k)))
                      (* (expt 2 k) (lnot (bits x k k) 1))
                      (bits x (1- k) 0))))
   :hints (("Goal" :use (lxor-expt-1-1 lxor-expt-1-2 lxor-expt-1-3)))))

(local
 (defthmd lxor-expt-2
   (implies (and (natp n)
                 (natp k)
                 (< k n))
            (equal (bits x (1- n) 0)
                   (+ (* (expt 2 (1+ k))
                         (bits x (1- n) (1+ k)))
                      (* (expt 2 k) (bitn x k))
                      (bits x (1- k) 0))))
   :hints (("Goal" :use ((:instance bits-plus-bits
                                    (n (1- n))
                                    (m 0)
                                    (p (1+ k)))
                         (:instance bitn-plus-bits ; could just enable
                                    (n k)
                                    (m 0)))))))

(defthmd lxor-expt
  (implies (and (natp n)
		(natp k)
		(< k n))
	   (equal (lxor x (expt 2 k) n)
		  (+ (bits x (1- n) 0)
                     (* (expt 2 k) (- 1 (* 2 (bitn x k)))))))
  :hints (("Goal" :in-theory (union-theories '(lxor-expt-1 lxor-expt-2)
                                             (current-theory 'ground-zero)))
          ("Goal''" :in-theory (enable lnot bitn))))

(include-book "bits-trunc")

; adapted from bits-trunc.lisp:

;; (defthm bits-trunc
;;   (implies (and (>= x (expt 2 (1- n)))
;;                 (< x (expt 2 n))
;;                 (integerp x) (> x 0)
;;                 (integerp m) (>= m n)
;;                 (integerp n) (> n k)
;;                 (integerp k) (> k 0)
;;                 )
;;            (= (trunc x k)
;;               (land x (- (expt 2 m) (expt 2 (- n k))) n)))
;;   :hints (("Goal" :use bits-trunc-original))
;;   :rule-classes ())

(defthm trunc-land
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) (> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0)
                )
           (= (trunc x k)
              (land x (- (expt 2 m) (expt 2 (- n k))) n)))
  :hints (("Goal" :use bits-trunc-original))
  :rule-classes ())

(defthm bits-trunc
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :hints (("Goal" :use ((:instance bits-trunc-2))))
  :rule-classes ())
