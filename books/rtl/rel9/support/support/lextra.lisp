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

; adapted from fadd.lisp:

(include-book "fadd")

(defthm gen-extend
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (gen x y i j)
                  (lior (gen x y i (1+ k))
                        (land (prop x y i (1+ k))
                              (gen x y k j)
                              1)
                        1)))
  :hints (("Goal" :use gen-extend-original))
  :rule-classes nil)

(defthm prop-extend
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (prop x y i j)
                  (land (prop x y i (1+ k))
                        (prop x y k j)
                        1)))
  :hints (("Goal" :use prop-extend-original))
  :rule-classes ())

(defthm gen-special-case
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (bitn (+ (bits x i j) (bits y i j)) (- i j)) 0))
           (equal (gen x y i j)
                  (lior (bitn x i) (bitn y i) 1)))
  :hints (("Goal" :use gen-special-case-original))
  :rule-classes ())

(defthm land-gen-0
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (land (bits x i j) (bits y i j) (1+ (- i j))) 0))
           (equal (gen x y i j) 0))
  :hints (("Goal" :use land0-gen-0)))

(defthm bits-sum-plus-1
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0))
           (equal (bits (+ 1 x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (lior (prop x y (1- j) 0)
                                 (gen x y (1- j) 0)
                                 1))
                        (- i j) 0)))
  :hints (("Goal" :use bits-sum-plus-1-with-prop-gen-original))
  :rule-classes ())

(defthm add-3
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n)
                (bvecp z n))
           (equal (+ x y z)
                  (+ (lxor x (lxor y z n) n)
                     (* 2 (lior (land x y n)
                                (lior (land x z n)
                                      (land y z n)
                                      n)
                                n)))))
  :hints (("Goal" :use add-3-original))
  :rule-classes ())

(defthm add-2
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n))
           (equal (+ x y)
                  (+ (lxor x y n)
                     (* 2 (land x y n)))))
  :hints (("Goal" :use add-2-original))
  :rule-classes ())

(defthm top-thm-1
  (implies (and (natp n)
                (natp k)
                (< k n)
                (integerp a)
                (integerp b))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lnot (lxor a b n) n) k 0) 0)))
  :hints (("Goal" :use top-thm-1-original))
  :rule-classes ())

(defund sigm (a b c n)
  (if (= c 0)
      (lnot (lxor a b n) n)
    (lxor a b n)))

(local-defthm sigm-is-sigm-0
  (equal (sigm a b c n)
         (sigm-0 a b c n))
  :hints (("Goal" :in-theory (enable sigm-0 sigm))))

(defund kap (a b c n)
  (if (= c 0)
      (* 2 (lior a b n))
    (* 2 (land a b n))))

(local-defthm kap-is-kap-0
  (equal (kap a b c n)
         (kap-0 a b c n))
  :hints (("Goal" :in-theory (enable kap-0 kap))))

(defund tau (a b c n)
  (lnot (lxor0 (sigm a b c n) (kap a b c n) (1+ n)) (1+ n)))

(local-defthm tau-is-tau-0
  (equal (tau a b c n)
         (tau-0 a b c n))
  :hints (("Goal" :in-theory (enable tau-0 tau))))

(defthm bvecp-sigm
  (bvecp (sigm a b c n) n)
  :hints (("Goal" :use bvecp-sigm-0 :in-theory (disable bvecp-sigm-0)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((sigm a b c n)))))

(defthm bvecp-kap
  (implies (and (integerp n) (<= 0 n))
           (bvecp (kap a b c n) (1+ n)))
  :hints (("Goal" :use bvecp-kap-0 :in-theory (disable bvecp-kap-0)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((kap a b c n)))))

(defthm bvecp-tau
  (bvecp (tau a b c n) (1+ n))
  :hints (("Goal" :use bvecp-tau-0 :in-theory (disable bvecp-tau-0)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((tau a b c n)))))

(defthm top-thm-2
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
                  (equal (bits (lxor (lxor a b n)
                                     (cat (lior a b n) n c 1)
                                     (1+ n))
                               k 0)
                         0)))
  :hints (("Goal" :use top-thm-2-original))
  :rule-classes nil)

(defthm top-thm-3
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lnot (lxor (lxor a b n)
				           (cat (land a b n) n 0 1)
					   (1+ n))
				     (1+ n))
			       k 0)
			 0)))
  :hints (("Goal" :use top-thm-3-original))
  :rule-classes ())

(defthm lop-thm-1
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (= e (expo a))
                (< (expo b) e)
                (= lambda
                   (lior (* 2 (mod a (expt 2 e)))
                         (lnot (* 2 b) (1+ e))
                         (1+ e))))
           (or (= (expo (- a b)) (expo lambda))
               (= (expo (- a b)) (1- (expo lambda)))))
  :hints (("Goal" :use lop-thm-1-original))
  :rule-classes ())

(defun lamt (a b e)
  (lxor a (lnot b (1+ e)) (1+ e)))

(defun lamg (a b e)
  (land a (lnot b (1+ e)) (1+ e)))

(defun lamz (a b e)
  (lnot (lior a (lnot b (1+ e)) (1+ e)) (1+ e)))

(defun lam1 (a b e)
  (land (bits (lamt a b e) e 2)
	(land (bits (lamg a b e) (1- e) 1)
	      (lnot (bits (lamz a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam2 (a b e)
  (land (lnot (bits (lamt a b e) e 2) (1- e))
	(land (bits (lamz a b e) (1- e) 1)
	      (lnot (bits (lamz a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam3 (a b e)
  (land (bits (lamt a b e) e 2)
	(land (bits (lamz a b e) (1- e) 1)
	      (lnot (bits (lamg a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam4 (a b e)
  (land (lnot (bits (lamt a b e) e 2) (1- e))
	(land (bits (lamg a b e) (1- e) 1)
	      (lnot (bits (lamg a b e) (- e 2) 0) (1- e))
	      (1- e))
	(1- e)))

(defun lam0 (a b e)
  (lior (lam1 a b e)
	(lior (lam2 a b e)
	      (lior (lam3 a b e)
		    (lam4 a b e)
		    (1- e))
	      (1- e))
	(1- e)))

(defun lamb (a b e)
  (+ (* 2 (lam0 a b e))
     (lnot (bitn (lamt a b e) 0) 1)))

(defthm lop-thm-2
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (not (= a b))
                (= e (expo a))
                (= e (expo b))
                (> e 1))
           (and (not (= (lamb a b e) 0))
                (or (= (expo (- a b)) (expo (lamb a b e)))
                    (= (expo (- a b)) (1- (expo (lamb a b e)))))))
  :hints (("Goal" :use lop-thm-2-original))
  :rule-classes ())

(defthm land-gen-0-cor
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n i)
                (>= i j)
                (>= j 0)
                (= (land x y n) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :hints (("Goal" :use land-gen-0-cor-original))
  :rule-classes ())

; Start proof of lior-plus from add-2.

(local (in-theory (e/d (binary-land binary-lior binary-lxor)
                       (land-is-land0 lior-is-lior0 lxor-is-lxor0))))

(local-defthm lxor-is-lior
  (implies (equal (land x y n) 0)
           (equal (lxor x y n)
                  (lior x y n))))

(defthmd lior-plus
  (implies (= (land x y n) 0)
           (equal (lior x y n)
                  (+ (bits x (1- n) 0)
                     (bits y (1- n) 0))))
  :hints (("Goal" :use ((:instance add-2
                                   (x (bits x (1- n) 0))
                                   (y (bits y (1- n) 0))))
           :in-theory (enable lior-bits-1 lior-bits-2
                              land-bits-1 land-bits-2))))

; Start proof of gen-plus:

(encapsulate
 ()

 (local-defthm gen-plus-1-1
   (implies (and (natp x)
                 (natp y)
                 (natp k)
                 (bvecp z (1+ k))
                 (= (land z y (1+ k)) 0)
                 (= (gen x y k 0) 1))
            (equal (+ (bits x k 0) (bits y k 0))
                   (+ (expt 2 (1+ k))
                      (bits (+ x y) k 0))))
   :hints (("Goal" :use ((:instance gen-val-cor2 (i k)))))
   :rule-classes nil)

 (local-defthm gen-plus-1-2
   (implies (and (natp x)
                 (natp y)
                 (natp k)
                 (bvecp z (1+ k))
                 (= (land z y (1+ k)) 0))
            (equal (+ (bits y k 0) (bits z k 0))
                   (bits (+ y z) k 0)))
   :hints (("Goal" :use ((:instance land-gen-0-cor
                                    (x y) (y z) (i k) (j 0) (n (1+ k))))
            :in-theory (enable bvecp)))
   :rule-classes nil)

 (local-defthm gen-plus-1-3
   (< (bits x i j)
      (expt 2 (1+ (- i j))))
   :hints (("Goal"
            :use ((:instance bits-upper-bound-2 (z (expt 2 (1+ (- i j))))))))
   :rule-classes nil)

 (local-defthm gen-plus-1
   (implies (and (natp x)
                 (natp y)
                 (natp k)
                 (bvecp z (1+ k))
                 (= (land z y (1+ k)) 0)
                 (= (gen x y k 0) 1))
            (< (+ (bits (+ x y) k 0)
                  (bits z k 0))
               (expt 2 (1+ k))))
   :hints (("Goal" :use (gen-plus-1-1
                         gen-plus-1-2
                         (:instance gen-plus-1-3 (x x) (i k) (j 0))
                         (:instance gen-plus-1-3 (x (+ y z)) (i k) (j 0)))
            :in-theory (disable land)))
   :rule-classes nil)

 (defthmd gen-plus
   (implies (and (natp x)
                 (natp y)
                 (natp k)
                 (bvecp z (1+ k))
                 (= (land z y (1+ k)) 0)
                 (= (gen x y k 0) 1))
            (equal (gen (+ x y) z k 0) 0))
   :hints (("Goal" :use gen-plus-1
            :in-theory (enable gen-val)))))

; Start proof of gen-extend-3.

(local (in-theory (enable bvecp-bits-0))) ; needed for gen-extend-3-a and more

(local-defthm gen-extend-3-a-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                (= (land y z (1+ j)) 0))
           (equal (gen (+ x y) z i (+ 1 j))
                  0))
  :rule-classes nil)

(defthmd gen-extend-3-a
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                (= (land y z (1+ j)) 0))
           (equal (gen (+ x y) z i 0)
                  (land (prop (+ x y) z i (1+ j))
                        (gen (+ x y) z j 0)
                        1)))
  :hints (("Goal" :use ((:instance gen-extend
                                   (x (+ x y))
                                   (y z)
                                   (i i)
                                   (j 0)
                                   (k j))
                        gen-extend-3-a-1))))

(local-defthm bitn-0-1-rewrite
  (implies (not (equal (bitn x n) 0))
           (equal (bitn x n) 1))
  :hints (("Goal" :use bitn-0-1)))

(local-defthm gen-is-0-or-1
  (implies (and (natp x)
                (natp y)
                (not (equal (gen x y i j) 1)))
           (equal (gen x y i j) 0))
  :rule-classes nil)

(local-defthm gen-extend-3-b-1-1-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                 (= (land y z (1+ j)) 0)
                (equal (gen (+ x y) z j 0) 1))
           (equal (gen x y j 0) 0))
  :hints (("Goal" :use ((:instance gen-plus (k j))
                        (:instance gen-is-0-or-1
                                   (i j) (j 0)))))
  :rule-classes nil)

(local-defthm gen-extend-3-b-1-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                (= (land y z (1+ j)) 0)
                (equal (gen (+ x y) z j 0) 1))
           (equal (bits (+ x y) i (1+ j))
                  (bits (+ (bits x i (1+ j))
                           (bits y i (1+ j)))
                        (- i (1+ j))
                        0)))
  :hints (("Goal" :use ((:instance bits-sum (j (1+ j)))
                        gen-extend-3-b-1-1-1)))
  :rule-classes nil)

(local-defthm gen-extend-3-b-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                (equal (gen (+ x y) z j 0) 1)
                (= (land y z (1+ j)) 0))
           (iff (equal (prop (+ x y) z i (1+ j))
                       1)
                (equal (bits (+ (bits x i (1+ j))
                                (bits y i (1+ j)))
                             (- i (1+ j))
                             0)
                       (1- (expt 2 (- i j))))))
  :hints (("Goal" :use (gen-extend-3-b-1-1
                        (:instance prop-val
                                   (x (+ x y))
                                   (y z)
                                   (i i)
                                   (j (1+ j))))))
  :rule-classes nil)

(local-defthm prop-is-0-or-1
  (implies (not (equal (prop x y i j) 1))
           (equal (prop x y i j) 0))
  :rule-classes nil)

; Most or all of the following are needed for gen-extend-3-b-2-1-2, and this is
; a good idea anyhow.
(local (in-theory (e/d (bits-nonnegative-integerp-type)
                       (bits-slice-zero-gen))))

(local-defthm gen-extend-3-b-2-1-1-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y))
           (equal (+ (bits x i (1+ j))
                     (bits y i (1+ j)))
                  (bits (+ (bits x i (1+ j))
                           (bits y i (1+ j)))
                        (- i j)
                        0)))
  :hints (("Goal" :use ((:instance bits-bvecp
                                   (x x) (i i) (j (1+ j)) (k (- i j)))
                        (:instance bits-bvecp
                                   (x y) (i i) (j (1+ j)) (k (- i j)))
                        (:instance bits-tail
                                   (x (+ (bits x i (+ 1 j))
                                         (bits y i (+ 1 j))))
                                   (i (+ i (* -1 j)))))
           :expand ((expt 2 (+ 1 i (* -1 j))))
           :in-theory (enable bvecp)))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2-1-1-2
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y))
           (equal (bits (+ (bits x i (1+ j))
                           (bits y i (1+ j)))
                        (- i j)
                        0)
                  (+ (* (expt 2 (- i j))
                        (bitn (+ (bits x i (1+ j))
                                 (bits y i (1+ j)))
                              (- i j)))
                     (bits (+ (bits x i (1+ j))
                              (bits y i (1+ j)))
                           (1- (- i j))
                           0))))
  :hints (("Goal" :use ((:instance bitn-plus-bits
                                   (x (+ (bits x i (1+ j))
                                         (bits y i (1+ j))))
                                   (n (- i j))
                                   (m 0)))))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2-1-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (equal (bits (+ (bits x i (1+ j))
                                (bits y i (1+ j)))
                             (- i (1+ j))
                             0)
                       (1- (expt 2 (- i j)))))
           (equal (+ (bits x i (1+ j))
                     (bits y i (1+ j)))
                  (+ (* (expt 2 (- i j))
                        (bitn (+ (bits x i (1+ j))
                                 (bits y i (1+ j)))
                              (- i j)))
                     (1- (expt 2 (- i j))))))
  :hints (("Goal" :use (gen-extend-3-b-2-1-1-1 gen-extend-3-b-2-1-1-2)))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2-1-2
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y))
           (< (+ (bits x i (1+ j))
                 (bits y i (1+ j)))
              (1- (+ (expt 2 (- i j))
                     (expt 2 (- i j))))))
  :hints (("Goal" :use ((:instance bits-bvecp
                                   (x x) (i i) (j (1+ j)) (k (- i j)))
                        (:instance bits-bvecp
                                   (x y) (i i) (j (1+ j)) (k (- i j)))
                        (:instance expt-2-positive-integer-type
                                   (i (+ i (* -1 j)))))
           :in-theory (e/d (bvecp) (a14 power2-integer expt2-integer))))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2-1
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (equal (bits (+ (bits x i (1+ j))
                                (bits y i (1+ j)))
                             (- i (1+ j))
                             0)
                       (1- (expt 2 (- i j)))))
           (equal (+ (bits x i (1+ j))
                     (bits y i (1+ j)))
                  (1- (expt 2 (- i j)))))
  :hints (("Goal" :use (gen-extend-3-b-2-1-1 gen-extend-3-b-2-1-2)))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2-2-1
  (implies (and (natp i)
                (natp j)
                (> i j))
           (equal (bits (1- (expt 2 (- i j)))
                        (- i (1+ j))
                        0)
                  (1- (expt 2 (- i j)))))
  :hints (("Goal" :in-theory (enable bvecp bits-does-nothing (expo))))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2-2
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (equal (+ (bits x i (1+ j))
                          (bits y i (1+ j)))
                       (1- (expt 2 (- i j)))))
           (equal (bits (+ (bits x i (1+ j))
                           (bits y i (1+ j)))
                        (- i (1+ j))
                        0)
                  (1- (expt 2 (- i j)))))
  :hints (("Goal" :use gen-extend-3-b-2-2-1))
  :rule-classes nil)

(local-defthm gen-extend-3-b-2
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y))
           (iff (equal (bits (+ (bits x i (1+ j))
                                (bits y i (1+ j)))
                             (- i (1+ j))
                             0)
                       (1- (expt 2 (- i j))))
                (equal (+ (bits x i (1+ j))
                          (bits y i (1+ j)))
                       (1- (expt 2 (- i j))))))
  :hints (("Goal" :use (gen-extend-3-b-2-1 gen-extend-3-b-2-2)))
  :rule-classes nil)

(local-defthm gen-extend-3-b
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                (= (land y z (1+ j)) 0)
                (equal (gen (+ x y) z j 0) 1))
           (equal (prop (+ x y) z i (1+ j))
                  (prop x y i (1+ j))))
  :hints (("Goal" :use (gen-extend-3-b-1
                        (:instance prop-val (j (1+ j)))
                        gen-extend-3-b-2
                        (:instance prop-is-0-or-1
                                   (x (+ x y))
                                   (y z)
                                   (i i)
                                   (j (1+ j)))
                        (:instance prop-is-0-or-1
                                   (x x)
                                   (y y)
                                   (i i)
                                   (j (1+ j))))
           :in-theory (enable bits-reduce)
           ))
  :rule-classes nil)

(defthmd gen-extend-3
  (implies (and (natp i)
                (natp j)
                (> i j)
                (natp x)
                (natp y)
                (bvecp z (1+ j))
                (= (land y z (1+ j)) 0))
           (equal (gen (+ x y) z i 0)
                  (land (prop x y i (1+ j))
                        (gen (+ x y) z j 0)
                        1)))
  :hints (("Goal" :use (gen-extend-3-a
                        gen-extend-3-b
                        (:instance gen-is-0-or-1
                                   (x (+ x y))
                                   (y z)
                                   (i j)
                                   (j 0)))
           :in-theory (enable bvecp) ; need (natp z)
           )))
