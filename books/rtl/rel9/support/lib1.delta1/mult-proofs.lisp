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

;(include-book "add")

(include-book "../support/rtl")
(include-book "../support/sumbits")
(include-book "../support/util")

;; (set-inhibit-warnings "theory")
;;
;; (local (in-theory nil))

(local (include-book "../../arithmetic/top"))

;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************


(defun theta (i y)
  (+ (bitn y (1- (* 2 i)))
     (bitn y (* 2 i))
     (* -2 (bitn y (1+ (* 2 i))))))

(defun sum-theta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta (1- m) y))
        (sum-theta (1- m) y))))


;----------------------------------------------------------------------


;; (local-defthm
;;  expt-merge-specific
;;  (implies (integerp i)
;;           (EQUAL (+ (EXPT 2 (+ -1 i))
;;                     (* 2 (EXPT 2 (+ -2 i))))
;;                  (EXPT 2 i)))
;;  :hints (("Goal" :in-theory (enable EXPT-2-REDUCE-LEADING-CONSTANT))))



;; (local-defthm
;;  bitn-minus-1-is-0
;;  (implies (integerp x)
;;           (equal (bitn x -1) 0))
;;  :hints (("Goal" :in-theory (enable bitn bits))))



(defthm sum-theta-lemma-i
  (implies (and (not (zp m))
                (integerp k)
                (integerp y)
                (<= 0 k)
                (<= k m))
           (equal (sumbits y (* 2 k))
                  (+ (sum-theta k y)
                     (* (expt 2 (* 2 k))
                        (bitn y (+ -1 (* 2 k)))))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (enable expt-2-reduce-leading-constant
                              bitn-neg)
           :induct (sum-theta k y)))
  :rule-classes ())


(local-defthm
 bvecp-integerp
 (implies (bvecp x k)
          (integerp x))
 :hints (("Goal" :in-theory (enable bvecp)))
 :rule-classes :forward-chaining)


(defthm sum-theta-lemma
  (implies (and (not (zp m))
                (bvecp y (1- (* 2 m))))
           (equal y (sum-theta m y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sum-theta-lemma-i
                                   (k m))
                        (:instance  sumbits-thm
                                    (n (+ -1  (* 2 m)))
                                    (x y)))
           :expand (SUMBITS Y (* 2 M))
           :do-not-induct t
           :do-not '(fertilize))))


;----------------------------------------------------------------------

(defun bmux4 (zeta x n)
  (case zeta
    (1  x)
    (-1 (lnot x n))
    (2  (* 2 x))
    (-2 (lnot (* 2 x) n))
    (0  0)))

(defun neg (x) (if (< x 0) 1 0))





(local-defthm bvecp-bvecp
  (implies  (and (BVECP X (+ -1 N))
                 (integerp n))
            (bvecp x n))
  :hints (("Goal" :in-theory (e/d (bvecp) (expt-compare))
           :use ((:instance expt-weak-monotone
                            (n (+ -1 n))
                            (m n))))))



(defthm bmux4-reduce-to
  (implies (and (integerp zeta)
                (<= zeta 2)
                (<= -2 zeta)
                (integerp n)
                (bvecp x (+ -1 n))
                (>= n 0))
           (equal (bmux4 zeta x n)
                  (if (<= 0 zeta)
                      (* zeta x)
                    (+ -1 (expt 2 n)
                       (* zeta x)))))
  :hints (("Goal" :in-theory (enable lnot BITS-TAIL-SPECIAL))))

;(include-book "bits")


(encapsulate ((zeta (i) t))
 (local (defun zeta (i) (declare (ignore i)) 0))
 (defthm zeta-bnd
     (and (integerp (zeta i))
	  (<= (zeta i) 2)
	  (>= (zeta i) -2))))

(defun pp4 (i x n)
  (if (zerop i)
      (cat 1 1
	   (lnot (neg (zeta i)) 1) 1
	   (bmux4 (zeta i) x n) n)
    (cat 1 1
	 (lnot (neg (zeta i)) 1) 1
	 (bmux4 (zeta i) x n) n
	 0 1
	 (neg (zeta (1- i))) 1
	 0 (* 2 (1- i)))))

(defun sum-zeta (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 2 (1- m))) (zeta (1- m)))
       (sum-zeta (1- m)))))

(defun sum-pp4 (x m n)
  (if (zp m)
      0
    (+ (pp4 (1- m) x n)
       (sum-pp4 x (1- m) n))))



(encapsulate ()
  (local (include-book "../support/cat"))
  (defthmd cat-bvecp-2
    (implies (and (<= (+ a0 a1) a)
                  (case-split (integerp a)))
             (bvecp (cat x1 a1 x0 a0) a))))


(local-defthmd binary-cat-2
              (implies (and (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a1)
                            (natp a0))
                       (equal (cat x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0)))))
              :hints (("Goal" :in-theory (enable binary-cat))))


(local-defthmd bcevp-sum-2
              (implies (and (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0)))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-2)
                                    (:instance binary-cat-2)))))

(local-defthmd binary-cat-3
              (implies (and (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                               (x1 x2)
                                               (a1 a2)
                                               (x0 (cat x1 a1 x0 a0))
                                               (a0 (+ a0 a1)))
                                    (:instance binary-cat-2)
                                    (:instance bcevp-sum-2
                                               (a (+ a0 a1)))))))



(defthmd cat-bvecp-3
    (implies (and (<= (+ a0 a1 a2) a)
                  (case-split (integerp a)))
             (bvecp (cat x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-3
              (implies (and (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1))))
                              a))
              :hints (("Goal" :use ((:instance binary-cat-3)
                                    (:instance cat-bvecp-3)))))



(local-defthmd binary-cat-4
              (implies (and (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x3 a3 x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1)))
                                 (* x3 (expt 2 (+ a0 a1 a2))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                        (x1 x3)
                                        (a1 a3)
                                        (x0 (cat x2 a2 x1 a1 x0 a0))
                                        (a0 (+ a0 a1 a2)))
                                    (:instance binary-cat-3)
                                    (:instance bcevp-sum-3
                                               (a (+ a0 a1 a2)))))))



(defthmd cat-bvecp-4
    (implies (and (<= (+ a0 a1 a2 a3) a)
                  (case-split (integerp a)))
             (bvecp (cat x3 a3 x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-4
              (implies (and (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2 a3) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1)))
                                 (* x3  (expt 2 (+ a0 a1 a2))))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-4)
                                    (:instance binary-cat-4)))))





(local-defthmd binary-cat-5
              (implies (and (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x4 a4 x3 a3 x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1)))
                                 (* x3 (expt 2 (+ a0 a1 a2)))
                                 (* x4 (expt 2 (+ a0 a1 a2 a3))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                        (x1 x4)
                                        (a1 a4)
                                        (x0 (cat x3 a3 x2 a2 x1 a1 x0 a0))
                                        (a0 (+ a0 a1 a2 a3)))
                                    (:instance binary-cat-4)
                                    (:instance bcevp-sum-4
                                               (a (+ a0 a1 a2 a3)))))))



(defthmd cat-bvecp-5
    (implies (and (<= (+ a0 a1 a2 a3 a4) a)
                  (case-split (integerp a)))
             (bvecp (cat x4 a4 x3 a3 x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-5
              (implies (and (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2 a3 a4) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1)))
                                 (* x3  (expt 2 (+ a0 a1 a2)))
                                 (* x4  (expt 2 (+ a0 a1 a2 a3))))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-5)
                                    (:instance binary-cat-5)))))





(local-defthmd binary-cat-6
              (implies (and (bvecp x5 a5)
                            (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a5)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x5 a5 x4 a4 x3 a3 x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1)))
                                 (* x3 (expt 2 (+ a0 a1 a2)))
                                 (* x4 (expt 2 (+ a0 a1 a2 a3)))
                                 (* x5 (expt 2 (+ a0 a1 a2 a3 a4))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                        (x1 x5)
                                        (a1 a5)
                                        (x0 (cat x4 a4 x3 a3 x2 a2 x1 a1 x0 a0))
                                        (a0 (+ a0 a1 a2 a3 a4)))
                                    (:instance binary-cat-5)
                                    (:instance bcevp-sum-5
                                               (a (+ a0 a1 a2 a3 a4)))))))


(defthmd cat-bvecp-6
    (implies (and (<= (+ a0 a1 a2 a3 a4 a5) a)
                  (case-split (integerp a)))
             (bvecp (cat x5 a5 x4 a4 x3 a3 x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-6
              (implies (and (bvecp x5 a5)
                            (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a5)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2 a3 a4 a5) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1)))
                                 (* x3  (expt 2 (+ a0 a1 a2)))
                                 (* x4  (expt 2 (+ a0 a1 a2 a3)))
                                 (* x5  (expt 2 (+ a0 a1 a2 a3 a4))))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-6)
                                    (:instance binary-cat-6)))))





(defthm zeta-bnd-properties
  (integerp (zeta i))
  :rule-classes :type-prescription)


(defthm zeta-bnd-properties-2
  (<= (zeta i) 2)
  :rule-classes :linear)

(defthm zeta-bnd-properties-3
  (<= -2 (zeta i))
  :rule-classes :linear)


(local
 (encapsulate ()
     (local-defthm x-zeta-bnd-specific
                   (implies (and (<= 0 x)
                                 (< (* 2 x) y)
                                 (integerp y)
                                 (integerp n)
                                 (integerp x))
                            (>=  (+ (* x (zeta i)) y) 1))
                   :hints (("Goal" :in-theory (disable zeta-bnd)
                            :use ((:instance zeta-bnd))))
                   :rule-classes nil)

     (local-defthm arith-hack-local
                   (implies (and (< x y)
                                 (<= (* 2 y) z))
                            (< (* 2 x) z))
                   :rule-classes nil)


     (local-defthm zeta-i-rationalp
                   (RATIONALP (ZETA I))
                   :hints (("Goal" :use ((:instance zeta-bnd)))))

     (local-defthm x-expt-hack-2
                   (implies (and (<= 0 x)
                                 (rationalp x))
                            (<= (* x (zeta i))
                                (* 2 x)))
                   :hints (("Goal" :use zeta-bnd))
                   :rule-classes nil)

  (defthm bvecp-bmux4
    (implies (and (bvecp x (+ -1 n))
                  (integerp n)
                  (< 0 n))
             (bvecp (bmux4 (zeta i) x n) n))
    :hints (("Goal" :in-theory (e/d (bvecp zeta-bnd EXPT-2-REDUCE-LEADING-CONSTANT) ())
             :use ((:instance expt-weak-monotone-linear
                              (n (+ -1 n))
                              (m n))))
            ("Subgoal 2" :use ((:instance x-zeta-bnd-specific
                                          (y (expt 2 n)))
                               (:instance arith-hack-local
                                          (x x)
                                          (z (expt 2 n))
                                          (y (expt 2 (+ -1 n))))
                               (:instance expt-weak-monotone-linear
                                          (n (+ -1 n))
                                          (m n))))
            ("Subgoal 1" :use x-expt-hack-2)))))


(local-defthm lnot-bvecp-1
              (implies (and (> i 0)
                            (integerp i))
                       (bvecp (lnot any 1) i))
              :hints (("Goal" :in-theory (enable lnot bvecp))))

(local-defthm neg-bvecp-1
              (implies (and (> i 0)
                            (integerp i))
                       (bvecp (neg any) i))
              :hints (("Goal" :in-theory (enable bvecp))))

(local-defthm zero-bvecp-1
              (bvecp 0 any)
              :hints (("Goal" :in-theory (enable bvecp))))


(local-defthm one-bvecp-1
              (implies (and (integerp i)
                            (< 0 i))
                       (bvecp 1 i))
              :hints (("Goal" :in-theory (enable bvecp))))


(local-defthm neg-lnot
              (EQUAL (+ (NEG any)
                        (LNOT (neg any) 1))
                     1)
              :hints (("Goal" :in-theory (enable neg lnot))))


(defthm pp4-reduce-to-1
  (implies (and (integerp n)
                (integerp i)
                (< 0 i)
                (bvecp x (+ -1 n))
                (> n 0))
           (equal (pp4 i x n)
                 (+ (EXPT 2 (+ 1 N (* 2 I)))
                    (EXPT 2 (+ N (* 2 I)))
                    (* -1 (NEG (ZETA I))
                       (EXPT 2 (+ N (* 2 I))))
                    (* (EXPT 2 (* 2 I))
                       (BMUX4 (ZETA I) X N))
                    (* (NEG (ZETA (+ -1 I)))
                       (EXPT 2 (+ -2 (* 2 I)))))))
  :hints (("Goal" :in-theory (disable bmux4-reduce-to bmux4 neg)
           :use ((:instance binary-cat-6
                                   (x5 1)
                                   (a5 1)
                                   (x4 (lnot (neg (zeta i)) 1))
                                   (a4 1)
                                   (x3 (bmux4 (zeta i) x n))
                                   (a3 n)
                                   (x2 0)
                                   (a2 1)
                                   (x1 (neg (zeta (+ -1 i))))
                                   (a1 1)
                                   (x0 0)
                                   (a0 (* 2 (+ -1 i))))))))


(defthm pp4-reduce-to-2
  (implies (and (integerp n)
                (bvecp x (+ -1 n))
                (> n 0))
           (equal (pp4 0 x n)
                  (+ (EXPT 2 (+ 1 N))
                     (EXPT 2 (+ N))
                     (* -1 (NEG (ZETA 0))
                        (EXPT 2 (+ N)))
                     (BMUX4 (ZETA 0) X N))))
  :hints (("Goal" :in-theory (disable bmux4-reduce-to bmux4 neg)
           :use ((:instance binary-cat-3
                                   (x2 1)
                                   (a2 1)
                                   (x1 (lnot (neg (zeta 0)) 1))
                                   (a1 1)
                                   (x0 (bmux4 (zeta 0) x n))
                                   (a0 n))))))



(defun sum-pp4-part1 (i n)
  (if (zp i)
      0
    (+ (sum-pp4-part1 (+ -1 i) n)
       (+ (expt 2 (+ 1 n (* 2 (+ -1 i))))
          (expt 2 (+ n (* 2 (+ -1 i))))))))


(defthm sum-pp4-part1-reduce-to-expt-n-2m
  (implies (and (integerp n)
                (integerp m)
                (< 0 m))
           (equal (+ (expt 2 n)
                     (sum-pp4-part1 m n))
                  (expt 2 (+ n (* 2 m)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (enable expt-2-reduce-leading-constant))
          ("Subgoal *1/3" :expand ((SUM-PP4-PART1 1 N)))))


(defun sum-pp4-part3 (m)
  (if (zp m)
      0
    (if (equal m 1)
        0
      (+ (sum-pp4-part3 (+ -1 m))
         (* (neg (zeta (+ -2 m)))
            (expt 2 (+ -2 (* 2 (+ -1 m)))))))))


(defun sum-pp4-part2 (m x n)
  (if (zp m)
      0
    (+ (sum-pp4-part2 (+ -1 m) x n)
       (+ (* -1 (neg (zeta (+ -1 m)))
             (expt 2 (+ n (* 2 (+ -1 m)))))
          (* (EXPT 2 (* 2 (+ -1 m)))
             (bmux4 (zeta (+ -1 m)) x n))))))


(defthm integerp-bmux4
  (implies (and (natp n)
                (integerp x))
           (INTEGERP (BMUX4 (ZETA I) X N)))
  :hints (("Goal" :in-theory (e/d (lnot)
                                  (zeta-bnd))
           :use ((:instance zeta-bnd)))))

(defthm integerp-bmux4-f
  (implies (and (natp n)
                (integerp x))
           (integerp (BMUX4 (ZETA I) X N)))
  :hints (("Goal" :in-theory (disable bmux4 zeta-bnd)))
  :rule-classes :type-prescription)




(defthm sum-pp4-reduce-to
  (implies (and (integerp n)
                (bvecp x (+ -1 n))
                (> n 0)
                (integerp m)
                (< 0 m))
           (equal (sum-pp4 x m n)
                  (+ (sum-pp4-part1 m n)
                     (sum-pp4-part2 m x n)
                     (sum-pp4-part3 m))))
  :hints (("Goal" :in-theory (disable pp4 bmux4-reduce-to zeta-bnd neg lnot
                                      bmux4)
           :do-not '(generalize))))

(defthm integerp-sum-pp4-part2
  (implies (and (integerp x)
                (integerp n)
                (< 0 n)
                (integerp n)
                (< 0 m))
           (integerp (sum-pp4-part2 m x n)))
  :hints (("Goal" :in-theory (e/d () (bmux4 bmux4-reduce-to))))
  :rule-classes :type-prescription)



;; (defun sum-bmux4 (x m n)
;;   (if (zp m) 0
;;     (+ (sum-bmux4 x (+ -1 m) n)
;;        (* (bmux4 (zeta (+ -1 m)) x n)
;;           (expt 2 (* 2 (+ -1 m)))))))


;; :pe bmux4-reduce-to
;;          18  (DEFTHM
;;                 BMUX4-REDUCE-TO
;;                 (IMPLIES (AND (INTEGERP ZETA)
;;                               (<= ZETA 2)
;;                               (<= -2 ZETA)
;;                               (INTEGERP N)
;;                               (BVECP X (+ -1 N))
;;                               (>= N 0))
;;                          (EQUAL (BMUX4 ZETA X N)
;;                                 (IF (<= 0 ZETA)
;;                                     (* ZETA X)
;;                                     (+ -1 (EXPT 2 N) (* ZETA X)))))


;; (defthm part2-item-reduce-to-alt
;;   (equal (+ (* -1 (NEG (ZETA i))
;;                (EXPT 2 (+ N (* 2 i))))
;;             (* (EXPT 2 (* 2 i))
;;                (BMUX4 (ZETA i) X N)))
;;          (+ (* x (zeta i)))))




;(BMUX4 (ZETA (+ -1 M)) X N))

;;          (EQUAL (+ (EXPT 2 (* 2 M))
;;                    (* (EXPT 2 (* 2 M))
;;                       (BMUX4 (ZETA (+ -1 M)) X N)))
;;                 (+ (EXPT 2 (+ N (* 2 M)))
;;                    (* X (ZETA (+ -1 M))
;;                       (EXPT 2 (* 2 M)))))).



(local-defthm arith-hack-reduce
               (implies (and (not (equal x 0))
                             (acl2-numberp x)
                             (acl2-numberp v)
                             (acl2-numberp w))
                        (equal (equal (+ x (* x y))
                                      (+ z (* v w x)))
                               (equal (+ 1 y)
                                      (+ (/ z x) (* v w)))))
               :rule-classes nil)


(local-defthm sum-pp4-part2-reduce-lemma
  (implies (and (integerp n)
                (bvecp x (+ -1 n))
                (< 0 m)
                (integerp m)
                (>= n 0))
           (EQUAL (+ (* (NEG (ZETA (+ -1 M)))
                        (EXPT 2 (+ -2 (* 2 M))))
                     (* -1 (NEG (ZETA (+ -1 M)))
                        (EXPT 2 (+ -2 N (* 2 M))))
                     (* (EXPT 2 (+ -2 (* 2 M)))
                        (BMUX4 (ZETA (+ -1 M)) X N)))
                  (* X (ZETA (+ -1 M))
                     (EXPT 2 (+ -2 (* 2 M))))))
  :hints (("Goal" :in-theory (e/d (expt-2-reduce-leading-constant)
                                  (bmux4 bmux4-reduce-to zeta-bnd
                                         EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
           :use ((:instance bmux4-reduce-to
                            (zeta (zeta (+ -1 m))))
                 (:instance zeta-bnd (i (+ -1 m)))
                 (:instance arith-hack-reduce
                            (x (expt 2 (* 2 m)))
                            (y (bmux4 (zeta (+ -1 m)) x n))
                            (z (expt 2 (+ n (* 2 m))))
                            (v x)
                            (w (zeta (+ -1 m)))))))
  :rule-classes nil)


(defthm integerp-sum-zeta
  (integerp (sum-zeta m))
  :rule-classes :type-prescription)

(defthm integerp-sum-zeta-specific
  (integerp (sum-zeta 1))
  :rule-classes :type-prescription)

(defthm integerp-zeta
  (integerp (zeta i))
  :rule-classes :type-prescription)

(defthm sum-zeta-1-is-zeta-0
  (equal (SUM-ZETA 1)
         (zeta 0))
  :hints (("Goal" :in-theory (disable (sum-zeta)))))


(local-defthm sum-pp4-part2-reduce
  (implies (and (integerp n)
                (integerp m)
                (< 0 m)
                (bvecp x (+ -1 n))
                (>= n 0))
           (equal (+ (sum-pp4-part2 m x n)
                     (sum-pp4-part3 m)
                     (* (neg (zeta (+ -1 m)))
                        (expt 2 (* 2 (+ -1 m)))))
                  (* x (sum-zeta m))))
  :hints (("Goal"

; The following hint, :induct t, was added by Matt Kaufmann on 9/28/2013 so
; that the proof goes through with ACL2(hp) and, presumably, ACL2(p).  A
; difference between those two and "vanilla" ACL2 is in the algorithm for
; reverting to prove the original goal by induction: this can happen later with
; ACL2(p) and ACL2(hp) than with ACL2.  In this case, without :induct t,
; ACL2(hp) created subgoals such as Subgoal 1.1.1.1.1.1.1.2'', while on the
; other hand ACL2 aborted immediately after Subgoal 1.2'' to prove the original
; goal by induction.

           :induct t
           :in-theory (e/d ()
                           (bmux4 (sum-zeta)
                                  bmux4-reduce-to neg lnot zeta-bnd))
           :do-not '(generalize))
          ("Subgoal *1/3" :use sum-pp4-part2-reduce-lemma)
          ("Subgoal *1/2" :in-theory (e/d (neg lnot zeta-bnd) ((sum-zeta)))
           :expand ((BMUX4 (ZETA 0) X N)))))


(defthm booth4-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n)))
	     (= (+ (expt 2 n)
		   (sum-pp4 x m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-zeta m))
		   (- (* (expt 2 (* 2 (1- m))) (neg (zeta (1- m))))))))
    :hints (("Goal" :do-not '(generalize fertilize)
             :do-not-induct t
             :in-theory (disable sum-pp4 sum-zeta sum-pp4-part2-reduce
                                 sum-pp4-part2
                                 sum-pp4-part3
                                 sum-pp4-part1
                                 (sum-zeta)
                                 sum-pp4-part1-reduce-to-expt-n-2m)
             :use ((:instance sum-pp4-part2-reduce)
                   (:instance sum-pp4-part1-reduce-to-expt-n-2m))))
  :rule-classes ())




(defun pp4-theta (i x y n)
   (if (zerop i)
       (cat 1 1
	    (lnot (neg (theta i y)) 1) 1
	    (bmux4 (theta i y) x n) n)
     (cat 1 1
	  (lnot (neg (theta i y)) 1) 1
	  (bmux4 (theta i y) x n) n
	  0 1
	  (neg (theta (1- i) y)) 1
	  0 (* 2 (1- i)))))


(defun sum-pp4-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4-theta (1- m) x y n)
       (sum-pp4-theta x y (1- m) n))))



(local-defthm booth4-corollary-lemma
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4-theta x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-theta m y))
		   (- (* (expt 2 (* 2 (1- m))) (neg (theta (1- m) y)))))))
  :rule-classes ()
  :hints (("Goal"
           :use ((:functional-instance
                  booth4-thm
                  (zeta (lambda (i) (theta i y)))
                  (sum-zeta (lambda (m) (sum-theta m y)))
                  (pp4  (lambda (i x n) (pp4-theta i x y n)))
                  (sum-pp4  (lambda (x m n) (sum-pp4-theta x y m n))))))
          ("Subgoal 2" :in-theory (disable pp4-theta))))

;; (defthm sum-theta-lemma
;;   (implies (and (not (zp m))
;;                 (integerp m)
;;                 (bvecp y (1- (* 2 m))))
;;            (equal y (sum-theta m y)))

(defthm theta-m-minus-1
  (implies (bvecp y (1- (* 2 m)))
           (equal (neg (theta (+ -1 m) y))
                  0)))

(defthm booth4-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4-theta x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance booth4-corollary-lemma)
                        (:instance sum-theta-lemma))
           :in-theory (disable pp4-theta theta
                               sum-pp4-theta sum-theta))))


;;;**********************************************************************
;;;                Statically Encoded Multiplier Arrays
;;;**********************************************************************

(defun m-mu-chi (i mode)
  (cond ((equal mode 'mu)
         (if (zp i)  1
           (cons (cons 1  i) 1)))
        ((equal mode 'chi)
         (if (zp i)  0
           (cons (cons 1  i) 0)))))


(mutual-recursion
 (defun mu (i y)
   (declare (xargs :measure (m-mu-chi i 'mu)))
     (+ (bits y (1+ (* 2 i)) (* 2 i)) (chi i y)))

 (defun chi (i y)
   (declare (xargs :measure (m-mu-chi i 'chi)))
   (if (zp i)
       0
     (if (>= (mu (1- i) y) 3)
	 1
       0))))


(defun phi (i y)
  (if (= (bits (mu i y) 1 0) 3)
      -1
    (bits (mu i y) 1 0)))

(defthm phi-bnd
    (member (phi i y) '(-1 0 1 2)))

(defun sum-odd-powers-of-2 (m)
  (if (zp m)
      0
    (+ (expt 2 (1- (* 2 m)))
       (sum-odd-powers-of-2 (1- m)))))


;; Subgoal *1/4'
;; (IMPLIES (AND (NOT (ZP M))
;;               (< (SUM-ODD-POWERS-OF-2 (+ -1 M)) Y)
;;               (<= 0 M)
;;               (INTEGERP Y)
;;               (<= 0 Y)
;;               (<= Y
;;                   (+ (SUM-ODD-POWERS-OF-2 (+ -1 M))
;;                      (EXPT 2 (+ -1 (* 2 M))))))
;;          (< (+ (CHI (+ -1 M) Y)
;;                (BITS Y (+ -1 (* 2 M)) (+ -2 (* 2 M))))
;;             3)).

(local
 (encapsulate ()
              (local (include-book "../support/cat"))
              (defthm cat-bits-bits
                (implies (and (equal j (1+ k))
                              (equal n (+ 1 (- l) k))
                              (case-split (<= (+ 1 (- j) i) m))
                              (case-split (<= j i))
                              (case-split (<= l k))
                              (case-split (integerp i))
                              (case-split (integerp k))
                              (case-split (integerp l))
                              (case-split (integerp m))
                              )
                         (equal (cat (bits x i j) m (bits x k l) n)
                                (bits x i l))))))


;; (local-defthmd binary-cat-2
;;               (implies (and (bvecp x1 a1)
;;                             (bvecp x0 a0)
;;                             (natp a1)
;;                             (natp a0))
;;                        (equal (cat x1 a1 x0 a0)
;;                               (+ x0
;;                                  (* x1 (expt 2 a0)))))
;;               :hints (("Goal" :in-theory (enable binary-cat))))




(local-defthm bits-bits-split
              (implies (and (natp i)
                            (natp j)
                            (natp l)
                            (< l j)
                            (< j i))
                       (equal (bits x i l)
                              (+ (* (expt 2 (+ (* -1 l) j))
                                    (bits x i j))
                                 (bits x (+ -1 j) l))))
              :hints (("Goal" :in-theory (disable cat-bits-bits)
                       :use ((:instance cat-bits-bits
                                        (k (+ -1 j))
                                        (m (+ 1 i (* -1 j)))
                                        (n (+ j (* -1 l))))
                             (:instance binary-cat-2
                                        (x1 (bits x i j))
                                        (a1 (+ 1 i (* -1 j)))
                                        (x0 (bits x (+ -1 j) l))
                                        (a0 (+ j (* -1 l)))))))
              :rule-classes nil)


(local-defthm y-expand-local
              (implies (and (integerp k)
                            (<= 0 k))
                       (equal (bits  y (+ 1 (* 2 k)) 0)
                              (+ (* (expt 2 (* 2 k))
                                    (bits y (+ 1 (* 2 k)) (* 2 k)))
                                 (bits y (+ -1 (* 2 k)) 0))))
              :hints (("Goal"
                       :use ((:instance bits-bits-split
                                        (x y)
                                        (i (+ 1 (* 2 k)))
                                        (l 0)
                                        (j (* 2 k))))))
              :rule-classes nil)


(defun sum-powers-of-2 (n)
  (if (zp n) 0
    (+ (expt 2 (+ -1 n))
       (sum-powers-of-2 (+ -1 n)))))


(defthm expt-0-is-1
  (equal (EQUAL 1 (EXPT 2 0)) t)
  :hints (("Goal" :expand ((expt 2 0)))))

(local-defthmd sum-powers-of-2-equal
              (implies (natp n)
                       (equal (sum-powers-of-2 n)
                              (+ -1 (expt 2 n))))
              :hints (("Goal" :do-not '(fertilize generalize))
                      ("Subgoal *1/4" :cases ((equal (+ (expt 2 (+ -1 n))
                                                        (expt 2 (+ -1 n)))
                                                     (expt 2 n))))
                      ("Subgoal *1/4.1" :in-theory (disable a3))))


(local-defthmd sum-odd-powers-upper-bound-lemma
               (implies (and (integerp k)
                             (< 0 k))
                        (< (sum-odd-powers-of-2 k)
                           (sum-powers-of-2 (* 2 k))))
               :rule-classes :linear)


(local-defthmd sum-odd-powers-upper-bound-weak
               (implies (and (integerp k)
                             (< 0 k))
                        (< (sum-odd-powers-of-2 k)
                           (+ -1 (expt 2 (* 2 k)))))
               :rule-classes :linear
               :hints (("Goal" :use ((:instance
                                      sum-odd-powers-upper-bound-lemma)
                                     (:instance sum-powers-of-2-equal
                                                (n (* 2 k)))))))

(local-defthmd y-lower-bound
              (implies (and (integerp k)
                            (<= 0 k))
                       (<= (* (expt 2 (* 2 k))
                              (bits y (+ 1 (* 2 k)) (* 2 k)))
                           (bits y (+ 1 (* 2 k)) 0)))
              :hints (("Goal" :use ((:instance y-expand-local)))))


(local-defthmd chi-m-subgoal-1-5
  (IMPLIES (AND (EQUAL (BITS Y (+ -1 (* 2 M)) (+ -2 (* 2 M)))
                       3)
                (integerp y)
                (NOT (ZP M))
                (<= 0 M))
           (< (+ (SUM-ODD-POWERS-OF-2 (+ -1 M))
                 (EXPT 2 (+ -1 (* 2 M))))
              (bits y (+ -1 (* 2 m)) 0)))
  :hints (("Goal" :in-theory (enable EXPT-2-REDUCE-LEADING-CONSTANT
                                     expt-weak-monotone-linear)
           :use ((:instance sum-odd-powers-upper-bound-weak
                            (k (+ -1 m)))
                 (:instance y-lower-bound
                            (k (+ -1 m)))))))




(local-defthmd chi-upper-bound
               (<= (chi  m y)
                   1)
               :hints (("Goal" :expand (chi m y)))
               :rule-classes :linear)



(local-defthm chi-m-lemma
    (implies (and (natp m)
		  (natp y)
		  (<= (bits y (+ -1 (* 2 m)) 0)
                      (sum-odd-powers-of-2 m)))
	     (equal (chi m y) 0))
    :hints (("Goal" :do-not '(generalize)

; Matt K. mod 5/2016 (type-set bit for {1}) [note: this comment was written
; before a recent update, "Library updates for bitp changes" (github commit
; hash 6bc56b062cd7a1b5ff3547aa8133f5006a75b913), but I suspect that it still
; is valid, and at any rate some patch is needed here]: formerly Goal' was
; proved by induction (so, an alternate fix is to specify :induct t for that
; subgoal), but now, we get to Goal'' because from falsity of (EQUAL (CHI M Y)
; 0) we know (EQUAL (CHI M Y) 1), which allows linear arithmetic to make some
; progress after Goal' (using ACL2 function polys-from-type-set).  So I'm
; disabling the type-prescription rule responsible for that progress.

             :in-theory (disable (:t chi)))
            ("Subgoal *1/5":use chi-m-subgoal-1-5)
            ("Subgoal *1/4":cases ((not (<= (bits y (+ -1 (* 2 m))
                                                  (+ -2 (* 2 m)))
                                            1))))
            ("Subgoal *1/4.2" :in-theory (enable chi-upper-bound))
            ("Subgoal *1/4.1" :cases ((not (equal (BITS Y (+ -1 (* 2 M))
                                                        (+ -2 (* 2 m))) 3))))
            ("Subgoal *1/4.1.2" :use chi-m-subgoal-1-5)
            ("Subgoal *1/4.1.1" :use ((:instance y-expand-local
                                                 (k (+ -1 m))))
             :in-theory (enable expt-2-reduce-leading-constant)))
  :rule-classes())

(defthm chi-m
    (implies (and (natp m)
		  (natp y)
		  (<= y
                      (sum-odd-powers-of-2 m)))
	     (equal (chi m y) 0))
    :hints (("Goal" :use chi-m-lemma))
    :rule-classes ())

(local-defthm chi-m-equal-0-implies-mu-less-than-3
              (implies (and (equal (chi m y) 0)
                            (not (zp m)))
                       (< (mu (+ -1 m) y) 3))
              :hints (("Goal" :in-theory (disable mu)
                       :expand ((chi m y)))))

(defthm phi-m-1
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (>= (phi (1- m) y) 0))
    :hints (("Goal" :use ((:instance chi-m)
                          (:instance chi-m-equal-0-implies-mu-less-than-3))
             :do-not-induct t
             :in-theory (disable chi mu)))
    :rule-classes())


(defun sum-phi (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (phi (1- m) y))
	(sum-phi (1- m) y))))


(local-defthmd mu-upper-bound
               (<= (mu i y) 4)
               :hints (("Goal" :in-theory (enable chi-upper-bound))))


(local-defthmd mu-upper-bound
               (<= (mu i y) 4)
               :hints (("Goal" :in-theory (enable chi-upper-bound))))


(local-defthmd chi-lower-bound
               (<= 0 (chi  m y))
               :hints (("Goal" :expand (chi m y)))
               :rule-classes :linear)

(local-defthmd mu-lower-bound
               (<= 0 (mu i y))
               :hints (("Goal" :in-theory (enable chi-lower-bound))))


(local-defthmd bitn-2-of-mu-is-chi
               (implies (not (equal (mu i y) 3))
                        (equal (bitn (mu i y) 2) (chi (+ 1 i) y)))
               :hints (("Goal" :cases ((not (equal (mu i y) 4))))
                       ("Subgoal 1" :use ((:instance mu-upper-bound)))))


(local-defthmd bitn-plus-bits-reduce
              (implies (and (integerp x)
                            (<= 0 x)
                            (< x 8))
                       (equal (+ (bits x 1 0)
                                 (* 4 (bitn x 2)))
                              x))
              :hints (("Goal" :in-theory (enable mu-upper-bound)
                       :use ((:instance BITN-PLUS-BITS
                                        (m 0)
                                        (n 2))))))


(local-defthmd 4-chi-plus-phi-is-mu
              (implies (natp i)
                       (equal (+ (phi i y) (* 4 (chi (+ 1 i) y)))
                              (mu i y)))
              :hints (("Goal" :cases ((not (equal (mu i y) 3))))
                      ("Subgoal 1" :in-theory (e/d () (mu))
                       :use ((:instance bitn-2-of-mu-is-chi)
                             (:instance bitn-plus-bits-reduce
                                        (x (mu i y)))
                             (:instance mu-upper-bound)))))


(local-defthm sum-phi-lemma-k
               (implies (natp m)
                        (equal (bits y (+ -1 (* 2 m)) 0)
                               ;; could have used sumbits here.
                               (+ (sum-phi m y)
                                  (* (chi m y) (expt 2 (* 2 m))))))
               :hints (("Goal" :do-not '(generalize)
                        :in-theory (e/d (expt-2-reduce-leading-constant)  (chi phi)))
                       ("Subgoal *1/4" :use ((:instance y-expand-local
                                                        (k (+ -1 m)))
                                             (:instance 4-chi-plus-phi-is-mu
                                                        (i (+ -1 m)))))
                       ("Subgoal *1/1" :expand ((chi 0 y))))
  :rule-classes ())

(local-defthmd y-upper-bound
  (implies (and (<= y (sum-odd-powers-of-2 m))
                (integerp m)
                (< 0 m))
           (<  y (expt 2 (* 2 m))))
  :hints (("Goal" :in-theory (enable SUM-ODD-POWERS-UPPER-BOUND-WEAK
                                     sum-odd-powers-upper-bound-lemma)))
  :rule-classes :linear)



(defthm sum-phi-lemma
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal y (sum-phi m y)))
    :hints (("Goal" :in-theory (e/d () (chi phi mu))
             :do-not '(fertilize generalize)
             :do-not-induct t
             :use ((:instance sum-phi-lemma-k)
                   (:instance chi-m)
                   (:instance y-upper-bound))))
  :rule-classes ())


(defun pp4-phi (i x y n)
   (if (zerop i)
       (cat 1 1
	    (lnot (neg (phi i y)) 1) 1
	    (bmux4 (phi i y) x n) n)
     (cat 1 1
	  (lnot (neg (phi i y)) 1) 1
	  (bmux4 (phi i y) x n) n
	  0 1
	  (neg (phi (1- i) y)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4-phi (x y m n)
  (if (zp m)
      0
    (+ (pp4-phi (1- m) x y n)
       (sum-pp4-phi x y (1- m) n))))


(local-defthm static-booth4-corollary-lemma
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n)))
	     (= (+ (expt 2 n)
		   (sum-pp4-phi x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-phi m y))
		   (- (* (expt 2 (* 2 (1- m))) (neg (phi (1- m) y)))))))
  :rule-classes ()
  :hints (("Goal"
           :use ((:functional-instance
                  booth4-thm
                  (zeta (lambda (i) (phi i y)))
                  (sum-zeta (lambda (m) (sum-phi m y)))
                  (pp4  (lambda (i x n) (pp4-phi i x y n)))
                  (sum-pp4  (lambda (x m n) (sum-pp4-phi x y m n))))))
          ("Subgoal 2" :in-theory (disable pp4-phi))))


(local-defthm neg-phi-m-1-is-0
              (implies (and (<= y (sum-odd-powers-of-2 m))
                            (natp m)
                            (natp y))
                       (equal (neg (phi (+ -1 m) y)) 0))
              :hints (("Goal" :in-theory (e/d () (phi))
                       :use phi-m-1)))


(defthm static-booth
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
                  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (= (+ (expt 2 n)
		   (sum-pp4-phi x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance static-booth4-corollary-lemma)
                        (:instance sum-phi-lemma)
                        (:instance phi-m-1))
           :in-theory (e/d () (pp4-phi phi
                               sum-pp4-phi sum-phi)))))


;;;**********************************************************************
;;;                Encoding Redundant Representations
;;;**********************************************************************

(include-book "../support/lior")
(include-book "../support/land")
(include-book "../support/lxor")


(defun gamma (i a b c)
   (if (zp i)
       (bitn c 0)
     (lior (bitn  a (+ -1  (* 2 i)))
 	   (bitn  b (+ -1  (* 2 i)))
 	  1)))


(defun delta (i a b c d)
  (if (zp i)
      (bitn d 0)
    (land (lior (land (bitn a (+ -2 (* 2 i)))
                      (bitn b (+ -2 (* 2 i)))
                      1)
		(lior (land (bitn a (+ -2 (* 2 i)))
                            (gamma (1- i) a b c)
                            1)
		      (land (bitn b (+ -2 (* 2 i)))
                            (gamma (1- i) a b c)
                            1)
                      1)
                1)
	  (lnot (lxor (bitn a (1- (* 2 i)))
                      (bitn b (1- (* 2 i)))
                      1)
                1)
	  1)))



(defun psi (i a b c d)
  (if (not (natp i))
      0
    (+ (bits a (1+ (* 2 i)) (* 2 i))
       (bits b (1+ (* 2 i)) (* 2 i))
       (gamma i a b c)
       (delta i a b c d)
       (* -4 (+ (gamma (1+ i) a b c)
                (delta (1+ i) a b c d))))))


;; (local-defthm bitn-not-less-than
;;               (implies (and (<= 0 b)
;;                             (< b (expt 2 k)))
;;                        (equal (bitn b k) 0)))


;;see  bitn-too-small

(defthm psi-m-1
    (implies (and (natp m)
                  (>= m 1)
		  (bvecp a (- (* 2 m) 2))  ;;
		  (bvecp b (- (* 2 m) 2))  ;;
		  (bvecp c 1)
		  (bvecp d 1))
	     (and (equal (gamma m a b c) 0)
		  (equal (delta m a b c d) 0)
		  (>= (psi (1- m) a b c d) 0)))
    :hints (("Goal" :in-theory (enable bvecp expt-2-reduce-leading-constant
                                       expt-weak-monotone-linear)))
  :rule-classes ())


(defun sum-psi (m a b c d)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (psi (1- m) a b c d))
	(sum-psi (1- m) a b c d))))



(local-defthmd gamma-0-is-c
               (implies (bvecp c 1)
                        (equal (gamma 0 a b c)
                               c)))

(local-defthmd delta-0-is-d
               (implies (bvecp d 1)
                        (equal (delta 0 a b c d)
                               d)))


(local-defthm sum-psi-lemma-k
    (implies (and (natp k)
		  (bvecp c 1)
		  (bvecp d 1))
	     (equal (+ (bits a (+ -1 (* 2 k)) 0)
                       (bits b (+ -1 (* 2 k)) 0)
                       c d)
                    (+ (sum-psi k a b c d)
                       (* (expt 2 (* 2 k))
                          (+ (gamma k a b c)
                             (delta k a b c d))))))
    :hints (("Goal" :induct (sum-psi k a b c d)
             :do-not '(generalize)
             :in-theory (e/d (expt-2-reduce-leading-constant
                              gamma-0-is-c delta-0-is-d
                              ) (gamma delta)))
            ("Subgoal *1/2" :use ((:instance y-expand-local
                                             (y a)
                                             (k (+ -1 k)))
                                  (:instance y-expand-local
                                             (y b)
                                             (k (+ -1 k))))))
  :rule-classes ())

(local-defthmd gamma-m-is-zero-when-a-b-small
               (implies (and (bvecp a (+ -2 (* 2 m)))
                             (bvecp b (+ -2 (* 2 m)))
                             (< 0 m)
                             (integerp m))
                        (equal (gamma m a b c)
                               0))
               :hints (("Goal" :in-theory (enable BITN-BVECP-0))))


(local-defthmd delta-m-is-zero-when-a-b-small
              (implies (and (bvecp a (+ -2 (* 2 m)))
                            (bvecp b (+ -2 (* 2 m)))
                            (< 0 m)
                            (integerp m))
                       (equal (delta m a b c d)
                              0))
              :hints (("Goal" :in-theory (enable ;bvecp
                                          bitn-bvecp-0
                                          expt-weak-monotone-linear
                                          expt-2-reduce-leading-constant))))


(local-defthmd bits-tail-general
               (implies (and (bvecp x k)
                             (integerp k)
                             (integerp j)
                             (<= k (+ 1 j)))
                        (equal (bits x j 0) x))
               :hints (("Goal" :in-theory (enable bvecp
                                                  expt-weak-monotone-linear)
                        :cases ((not (<= (expt 2 k) (expt 2 (+ 1 j))))))))

(defthm sum-psi-lemma
    (implies (and (natp m)
                  (<= 1 m)
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (equal (+ a b c d) (sum-psi m a b c d)))
    :hints (("Goal" :use ((:instance sum-psi-lemma-k
                                     (k m)))
             :in-theory (e/d (gamma-0-is-c
                              gamma-m-is-zero-when-a-b-small
                              delta-0-is-d
                              delta-m-is-zero-when-a-b-small
                              bits-tail-general)
                             (gamma delta sum-psi BITS-REDUCE))))
  :rule-classes ())




(local-defthm delta-bnd-1
  (<= 0 (delta i a b c d))
  :rule-classes :linear)

(local-defthm delta-bnd-2
  (<= (delta i a b c d) 1)
  :rule-classes :linear)


(local-defthm gamma-bnd-1
  (<= 0 (gamma i a b c))
  :rule-classes :linear)

(local-defthm gamma-bnd-2
  (<= (gamma i a b c) 1)
  :rule-classes :linear)


(local-defthm bitn-gamma-gamma
  (equal (bitn (gamma i a b c) 0)
         (gamma i a b c)))

(local-defthm bitn-delta-delta
  (equal (bitn (delta i a b c d) 0)
         (delta i a b c d)))



;; (local-defthmd binary-cat-2
;;               (implies (and (bvecp x1 a1)
;;                             (bvecp x0 a0)
;;                             (natp a1)
;;                             (natp a0))
;;                        (equal (cat x1 a1 x0 a0)
;;                               (+ x0
;;                                  (* x1 (expt 2 a0)))))
;;               :hints (("Goal" :in-theory (enable binary-cat))))


(local-defthmd bits-expand-specific
  (implies (natp i)
           (equal (BITS x (+ 1 (* 2 I)) (* 2 I))
                  (+ (* 2 (bitn x (+ 1 (* 2 i))))
                     (bitn x (* 2 i)))))
  :hints (("Goal" :in-theory (enable bitn)
           :use ((:instance cat-bits-bits
                            (i (+ 1 (* 2 i)))
                            (j (+ 1 (* 2 i)))
                            (m 1)
                            (n 1)
                            (k (* 2 i))
                            (l (* 2 i)))
                 (:instance binary-cat-2
                            (x1 (bitn x (+ 1 (* 2 i))))
                            (a1 1)
                            (x0 (bitn x (* 2 i)))
                            (a0 1))))))


(defthmd psi-bnd
  (and (integerp (psi i a b c d))
       (<= (psi i a b c d) 2)
       (>= (psi i a b c d) -2))
  :hints (("Goal" :in-theory (e/d (bits-expand-specific)
                                  (bits bitn
                                        gamma
                                        delta))
           :expand ((gamma (+ 1 i) a b c)
                    (DELTA (+ 1 I) A B C D)))))






(defun pp4-psi (i x a b c d n)
   (if (zerop i)
       (cat 1 1
	    (lnot (neg (psi i a b c d)) 1) 1
	    (bmux4 (psi i a b c d) x n) n)
     (cat 1 1
	  (lnot (neg (psi i a b c d)) 1) 1
	  (bmux4 (psi i a b c d) x n) n
	  0 1
	  (neg (psi (1- i) a b c d)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4-psi (x a b c d m n)
  (if (zp m)
      0
    (+ (pp4-psi (1- m) x a b c d n)
       (sum-pp4-psi x a b c d (1- m) n))))

(defthm integerp-psi
  (integerp (psi i a b c d)))


(local-defthm
 redundant-booth4-corollary-lemma
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n)))
	     (= (+ (expt 2 n)
		   (sum-pp4-psi x a b c d m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x (sum-psi m a b c d))
		   (- (* (expt 2 (* 2 (1- m))) (neg (psi (1- m) a b c d)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (psi-bnd) (psi pp4-psi))
           :do-not-induct t
           :use ((:functional-instance
                  booth4-thm
                  (zeta (lambda (m) (psi m a b c d)))
                  (sum-zeta (lambda (m) (sum-psi m a b c d)))
                  (pp4  (lambda (m x n) (pp4-psi m x a b c d  n)))
                  (sum-pp4  (lambda (x m n) (sum-pp4-psi x a b c d m n))))))
          ("Subgoal 1" :in-theory (enable pp4-psi))))



(local-defthm neg-psi-m-1-is-0
              (implies (and (NATP M)
                              (>= M 1)
                              (BVECP A (- (* 2 M) 2))
                              (BVECP B (- (* 2 M) 2))
                              (BVECP C 1)
                              (BVECP D 1))
                       (equal (neg (psi (+ -1 m) a b c d)) 0))
              :hints (("Goal" :in-theory (e/d () (psi))
                       :use psi-m-1)))


(defthm redundant-booth
    (implies (and (natp m)
                  (<= 1 m)
                  (not (zp n))
		  (bvecp x (1- n))
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1)
		  (= y (+ a b c d)))
	     (= (+ (expt 2 n)
		   (sum-pp4-psi x a b c d m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
    :hints (("Goal" :in-theory (disable psi sum-pp4-psi)
             :use ((:instance redundant-booth4-corollary-lemma)
                   (:instance sum-psi-lemma))))

  :rule-classes ())

;;;**********************************************************************
;;;			Radix-8 Booth Encoding
;;;**********************************************************************


(defun eta (i y)
  (+ (bitn y (1- (* 3 i)))
     (bitn y (* 3 i))
     (* 2 (bitn y (1+ (* 3 i))))
     (* -4 (bitn y (+ 2 (* 3 i))))))

(defun sum-eta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 3 (1- m))) (eta (1- m) y))
	(sum-eta (1- m) y))))



(defthm sum-eta-lemma-i
  (implies (and (not (zp m))
                (integerp k)
                (integerp y)
                (<= 0 k)
                (<= k m))
           (equal (sumbits y (* 3 k))
                  (+ (sum-eta k y)
                     (* (expt 2 (* 3 k))
                        (bitn y (+ -1 (* 3 k)))))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (enable bitn-neg
                              expt-2-reduce-leading-constant)
           :induct (sum-eta k y))
          ("Subgoal *1/2" :expand ((SUMBITS Y (* 3 K))
                                   (SUMBITS Y (+ -1 (* 3 K)))
                                   (SUMBITS Y (+ -2 (* 3 K))))))
  :rule-classes ())


(defthm sum-eta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 3 m))))
	     (equal y (sum-eta m y)))
  :hints (("Goal" :use ((:instance sum-eta-lemma-i
                                   (k m))
                        (:instance  sumbits-thm
                                    (n (+ -1  (* 3 m)))
                                    (x y)))
           :do-not-induct t
           :do-not '(fertilize)))
  :rule-classes ())


(defun bmux8 (zeta x n)
  (case zeta
    (1  x)
    (-1 (lnot x n))
    (2  (* 2 x))
    (-2 (lnot (* 2 x) n))
    (3  (* 3 x))
    (-3 (lnot (* 3 x) n))
    (4  (* 4 x))
    (-4 (lnot (* 4 x) n))
    (0  0)))

(encapsulate ((xi (i) t))
 (local (defun xi (i) (declare (ignore i)) 0))
 (defthm xi-bnd
     (and (integerp (xi i))
	  (<= (xi i) 4)
	  (>= (xi i) -4))))


(defun pp8 (i x n)
  (if (zerop i)
      (cat 3 2
	   (lnot (neg (xi i)) 1) 1
	   (bmux8 (xi i) x n) n)
    (cat 3 2
	 (lnot (neg (xi i)) 1) 1
	 (bmux8 (xi i) x n) n
	 0 2
	 (neg (xi (1- i))) 1
	 0 (* 3 (1- i)))))

(defun sum-xi (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 3 (1- m))) (xi (1- m)))
       (sum-xi (1- m)))))



(defun sum-pp8 (x m n)
  (if (zp m)
      0
    (+ (pp8 (1- m) x n)
       (sum-pp8 x (1- m) n))))




(defthm bmux8-reduce-to
  (implies (and (integerp eta)
                (<= eta 2)
                (<= -2 eta)
                (integerp n)
                (bvecp x (+ -1 n))
                (>= n 0))
           (equal (bmux8 eta x n)
                  (if (<= 0 eta)
                      (* eta x)
                    (+ -1 (expt 2 n)
                       (* eta x)))))
  :hints (("Goal" :in-theory (enable lnot BITS-TAIL-SPECIAL))))




(defthm xi-bnd-properties
  (integerp (xi i))
  :rule-classes :type-prescription)


(defthm xi-bnd-properties-2
  (<= (xi i) 4)
  :rule-classes :linear)

(defthm xi-bnd-properties-3
  (<= -4 (xi i))
  :rule-classes :linear)


(defthm bvecp-bmux8
  (implies (and (bvecp x (+ -2 n))
                (integerp i)
                (integerp n)
                (< 0 n))
           (bvecp (bmux8 (xi i) x n) n))
  :hints (("Goal" :in-theory (e/d (bvecp lnot xi-bnd EXPT-2-REDUCE-LEADING-CONSTANT) ())
           :use ((:instance expt-weak-monotone-linear
                            (n (+ -2 n))
                            (m n))))))




(defthm pp8-reduce-to-1
  (implies (and (integerp n)
                (integerp i)
                (< 0 i)
                (bvecp x (+ -2 n))
                (> n 0))
           (equal (pp8 i x n)
                 (+ (EXPT 2 (+ 2 N (* 3 I)))
                    (EXPT 2 (+ 1 N (* 3 I)))
                    (EXPT 2 (+ N (* 3 I)))
                    (* -1 (NEG (XI I))
                       (EXPT 2 (+ N (* 3 I))))
                    (* (EXPT 2 (* 3 I))
                       (BMUX8 (XI i) X N))
                    (* (NEG (XI (+ -1 I)))
                       (EXPT 2 (+ -3 (* 3 I)))))))
  :hints (("Goal" :in-theory (e/d (expt-2-reduce-leading-constant)
                                  (bmux8-reduce-to bmux8 (bmux8) neg))
           :use ((:instance binary-cat-6
                                   (x5 3)
                                   (a5 2)
                                   (x4 (lnot (neg (xi i)) 1))
                                   (a4 1)
                                   (x3 (bmux8 (xi i) x n))
                                   (a3 n)
                                   (x2 0)
                                   (a2 2)
                                   (x1 (neg (xi (+ -1 i))))
                                   (a1 1)
                                   (x0 0)
                                   (a0 (* 3 (+ -1 i))))))))



;;                         (CAT 3 2 (LNOT (NEG (XI I)) 1)
;;                              1 (BMUX8 (XI I) X N)
;;                              N)

(defthm pp8-reduce-to-2
  (implies (and (integerp n)
                (bvecp x (+ -2 n))
                (> n 0))
           (equal (pp8 0 x n)
                  (+ (EXPT 2 (+ 2 N))
                     (EXPT 2 (+ 1 N))
                     (EXPT 2 N)
                     (* -1 (NEG (xi 0))
                        (EXPT 2 (+ N)))
                     (BMUX8 (xi 0) X N))))
  :hints (("Goal" :in-theory (e/d (expt-2-reduce-leading-constant)
                                  (bmux8-reduce-to bmux8 neg))
           :use ((:instance binary-cat-3
                                   (x2 3)
                                   (a2 2)
                                   (x1 (lnot (neg (xi 0)) 1))
                                   (a1 1)
                                   (x0 (bmux8 (xi 0) x n))
                                   (a0 n))))))



;(i-am-here) ;; Fri Oct 20 11:08:20 2006


(defun sum-pp8-part1 (i n)
  (if (zp i)
      0
    (+ (sum-pp8-part1 (+ -1 i) n)
       (+ (expt 2 (+ 2 n (* 3 (+ -1 i))))
          (expt 2 (+ 1 n (* 3 (+ -1 i))))
          (expt 2 (+ n (* 3 (+ -1 i))))))))


(defthm sum-pp8-part1-reduce-to-expt-n-3m
  (implies (and (integerp n)
                (integerp m)
                (< 0 m))
           (equal (+ (expt 2 n)
                     (sum-pp8-part1 m n))
                  (expt 2 (+ n (* 3 m)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (enable expt-2-reduce-leading-constant))
          ("Subgoal *1/3" :expand ((SUM-PP8-PART1 1 N)))))



(defun sum-pp8-part3 (m)
  (if (zp m)
      0
    (if (equal m 1)
        0
      (+ (sum-pp8-part3 (+ -1 m))
         (* (neg (xi (+ -2 m)))
            (expt 2 (* 3 (+ -2 m))))))))


(defun sum-pp8-part2 (m x n)
  (if (zp m)
      0
    (+ (sum-pp8-part2 (+ -1 m) x n)
       (+ (* -1 (neg (xi (+ -1 m)))
             (expt 2 (+ n (* 3 (+ -1 m)))))
          (* (EXPT 2 (* 3 (+ -1 m)))
             (bmux8 (xi (+ -1 m)) x n))))))


(defthm sum-pp8-reduce-to
  (implies (and (integerp n)
                (bvecp x (+ -2 n))
                (> n 0)
                (integerp m)
                (< 0 m))
           (equal (sum-pp8 x m n)
                  (+ (sum-pp8-part1 m n)
                     (sum-pp8-part2 m x n)
                     (sum-pp8-part3 m))))
  :hints (("Goal" :in-theory (e/d (expt-2-reduce-leading-constant)
                                  (pp8 bmux8-reduce-to xi-bnd neg lnot
                                       bmux8))
           :do-not '(generalize))))



(local-defthmd bvecp-bits-specific-2
               (implies (and (bvecp x (+ -2 n))
                             (integerp n))
                        (equal (BITS X (+ -1 N) 0)
                               x))
               :hints (("Goal" :in-theory (e/d (bvecp) (expt-compare bits-reduce))
                        :use ((:instance expt-weak-monotone-linear
                                         (n (+ -2 n))
                                         (m n))
                              (:instance bits-reduce
                                         (i (+ -1 n)))))))


(local-defthmd bvecp-bits-specific-3
               (implies (and (bvecp x (+ -2 n))
                             (integerp n))
                        (equal (BITS (* 3 X) (+ -1 N) 0)
                               (* 3 x)))
               :hints (("Goal" :in-theory (e/d (bvecp expt-2-reduce-leading-constant)
                                               (expt-compare
                                                bits-reduce))
                        :use ((:instance bits-reduce
                                         (x (* 3 x))
                                         (i (+ -1 n)))))))




(local-defthm sum-pp8-part2-reduce-lemma
  (implies (and (integerp n)
                (bvecp x (+ -2 n))
                (< 0 m)
                (integerp m)
                (>= n 0))
           (EQUAL (+ (* (NEG (xi (+ -1 M)))
                        (EXPT 2 (+ -3 (* 3 M))))
                     (* -1 (NEG (xi (+ -1 M)))
                        (EXPT 2 (+ -3 N (* 3 M))))
                     (* (EXPT 2 (+ -3 (* 3 M)))
                        (BMUX8 (xi (+ -1 M)) X N)))
                  (* X (xi (+ -1 M))
                     (EXPT 2 (+ -3 (* 3 M))))))
  :hints (("Goal" :in-theory (e/d (expt-2-reduce-leading-constant
                                   lnot
                                   bvecp-bits-specific-2
                                   bvecp-bits-specific-3)
                                  (bmux4 bmux8-reduce-to xi-bnd
                                         EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
           :use ((:instance bmux8-reduce-to
                            (eta (+ -1 m)))
                 (:instance xi-bnd (i (+ -1 m))))))
  :rule-classes nil)


(local-defthm sum-pp8-part2-reduce
  (implies (and (integerp n)
                (integerp m)
                (< 0 m)
                (bvecp x (+ -2 n))
                (>= n 0))
           (equal (+ (sum-pp8-part2 m x n)
                     (sum-pp8-part3 m)
                     (* (neg (xi (+ -1 m)))
                        (expt 2 (* 3 (+ -1 m)))))
                  (* x (sum-xi m))))
  :hints (("Goal" :in-theory (e/d ()
                                  (bmux8 (sum-xi)
                                         bmux8-reduce-to neg lnot xi-bnd))
           :do-not '(generalize))
          ("Subgoal *1/3" :use sum-pp8-part2-reduce-lemma)
          ("Subgoal *1/2" :in-theory (e/d (bvecp-bits-specific-3
                                           bvecp-bits-specific-2 neg lnot
                                           xi-bnd)
                                          ((sum-xi)))
           :expand ((BMUX8 (ZETA 0) X N)))))


(defthm booth8-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2)))
	     (= (+ (expt 2 n)
		   (sum-pp8 x m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x (sum-xi m))
		   (- (* (expt 2 (* 3 (1- m))) (neg (xi (1- m))))))))
    :hints (("Goal" :do-not '(generalize fertilize)
             :do-not-induct t
             :in-theory (disable sum-pp8 sum-xi sum-pp8-part2-reduce
                                 sum-pp8-part2
                                 sum-pp8-part3
                                 sum-pp8-part1
                                 (sum-xi)
                                 sum-pp8-part1-reduce-to-expt-n-3m)
             :use ((:instance sum-pp8-part2-reduce)
                   (:instance sum-pp8-part1-reduce-to-expt-n-3m))))
  :rule-classes ())


(defun pp8-eta (i x y n)
  (if (zerop i)
      (cat 3 2
	   (lnot (neg (eta i y)) 1) 1
	   (bmux8 (eta i y) x n) n)
    (cat 3 2
	 (lnot (neg (eta i y)) 1) 1
	 (bmux8 (eta i y) x n) n
	 0 2
	 (neg (eta (1- i) y)) 1
	 0 (* 3 (1- i)))))


(defun sum-pp8-eta (x y m n)
  (if (zp m)
      0
    (+ (pp8-eta (1- m) x y n)
       (sum-pp8-eta x y (1- m) n))))



;; (defthm sum-eta-lemma
;;     (implies (and (not (zp m))
;; 		  (bvecp y (1- (* 3 m))))
;; 	     (equal y (sum-eta m y)))
;;   :hints (("Goal" :use ((:instance sum-eta-lemma-i
;;                                    (k m))
;;                         (:instance  sumbits-thm
;;                                     (n (+ -1  (* 3 m)))
;;                                     (x y)))
;;            :do-not-induct t
;;            :do-not '(fertilize)))
;;   :rule-classes ())


(local-defthmd eta-m-1-lemma
  (implies (bvecp y (+ -1 (* 3 m)))
           (equal (bitn y (+ -1 (* 3 m))) 0))
  :hints (("Goal" :in-theory (enable bvecp))))


(local-defthmd eta-m-1
  (implies (bvecp y (+ -1 (* 3 m)))
           (>= (eta (+ -1 m) y) 0))
  :hints (("Goal" :in-theory (enable bvecp eta-m-1-lemma))))

(defthm neg-eta-m-1-is-0
  (implies (bvecp y (+ -1 (* 3 m)))
           (equal (neg (eta (+ -1 m) y)) 0))
  :hints (("Goal" :in-theory (enable neg eta-m-1))))


(defthm eta-bnd
  (and (integerp (eta i y))
       (<= (eta i y) 4)
       (<= -4 (eta i y))))


(defthm booth8-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2))
		  (bvecp y (1- (* 3 m))))
	     (= (+ (expt 2 n)
		   (sum-pp8-eta x y m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x y))))
  :hints (("Goal"
           :in-theory (disable sum-eta
                               pp8-eta
                               bmux8
                               sum-pp8-eta
                               pp8-reduce-to-2
                               pp8-reduce-to-1
                               bmux8-reduce-to)
           :do-not-induct t
           :use ((:functional-instance
                  booth8-thm
                  (xi (lambda (i) (eta i y)))
                  (sum-xi (lambda (m) (sum-eta m y)))
                  (pp8  (lambda (i x n) (pp8-eta i x y n)))
                  (sum-pp8  (lambda (x m n) (sum-pp8-eta x y m n))))
                 (:instance sum-eta-lemma)))
          ("Subgoal 3" :in-theory (enable sum-eta))
          ("Subgoal 2" :in-theory (e/d (sum-pp8-eta) (pp8-eta)))
          ("Subgoal 1" :in-theory (e/d (pp8-eta) (bmux8 bmux8-reduce-to))))
  :rule-classes ())
