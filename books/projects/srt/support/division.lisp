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

(include-book "rtl/rel11/lib/basic" :dir :system)
(include-book "rtl/rel11/lib/bits" :dir :system)
(include-book "rtl/rel11/lib/util" :dir :system)

(set-prover-step-limit acl2::*default-step-limit*)

(encapsulate ()

(local (include-book "arithmetic-5/top" :dir :system))

;;**********************************************************************************

(encapsulate (((rho$) => *) ((x$) => *) ((d$) => *) ((h$ *) => *))
  (local (defun rho$ () 1))
  (local (defun x$ () 0))
  (local (defun d$ () 1))
  (local (defun h$ (k) (declare (ignore k)) 0))
  (defthm rho$-constraint
    (integerp (rho$))
    :rule-classes (:rewrite :type-prescription))
  (defthm x$-constraint
    (rationalp (x$))
    :rule-classes (:rewrite :type-prescription))
  (defthm d$-constraint
    (and (rationalp (d$))
         (> (d$) 0))
    :rule-classes (:rewrite :type-prescription))
  (defthm integerp-h$
    (implies (not (zp k))
             (integerp (h$ k)))
    :rule-classes (:rewrite :type-prescription)))

(defund p$ (k)
  (if (zp k)
      (x$)
    (- (* (expt 2 (rho$)) (p$ (1- k)))
       (* (h$ k) (d$)))))

(defund q$ (k)
  (if (zp k)
      0
    (+ (q$ (1- k))
       (/ (h$ k) (expt 2 (* k (rho$)))))))

(local-defthm lemma-2-1-1
  (implies (and (not (zp k))
                (= (p$ (1- k))
                   (* (expt 2 (* (1- k) (rho$)))
                      (- (x$) (* (q$ (1- k)) (d$))))))
           (equal (* (expt 2 (* k (rho$))) (- (x$) (* (q$ k) (d$))))
                  (p$ k)))
  :hints (("Goal" :in-theory (enable p$ q$)))
  :rule-classes ())

(local-defthm lemma-2-1-2
  (implies (zp k)
           (equal (- (x$) (* (q$ k) (d$)))
                  (p$ k)))
  :hints (("Goal" :in-theory (enable p$ q$)))
  :rule-classes ())

(defun natp-induct (n)
  (if (zp n)
      t
    (natp-induct (1- n))))

(defthmd lemma-2-1
  (implies (natp k)
           (equal (p$ k)
                  (* (expt 2 (* k (rho$)))
                     (- (x$) (* (q$ k) (d$))))))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/2" :use lemma-2-1-1)
          ("Subgoal *1/1" :use lemma-2-1-2)))

(local-defthm lemma-2-1-3
  (implies (natp k)
           (equal (/ (p$ k) (d$))
                  (* (expt 2 (* k (rho$)))
                     (- (/ (x$) (d$)) (q$ k)))))
  :hints (("Goal" :in-theory (enable lemma-2-1)))
  :rule-classes ())

(local-defthm rat-p$
  (rationalp (p$ k))
  :hints (("Goal" :in-theory (enable p$))))

(local-defthm lemma-2-1-4
  (implies (and (<= (- (d$)) (p$ k))
                (< (p$ k) (d$)))
           (and (<= -1 (/ (p$ k) (d$)))
                (< (/ (p$ k) (d$)) 1)))
  :rule-classes ())

(local-defthm lemma-2-1-5
  (implies (and (natp k)
                (<= (- (d$)) (p$ k))
                (< (p$ k) (d$)))
           (and (<= -1
                    (* (expt 2 (* k (rho$)))
                       (- (/ (x$) (d$)) (q$ k))))
                (< (* (expt 2 (* k (rho$)))
                      (- (/ (x$) (d$)) (q$ k)))
                   1)))
  :hints (("Goal" :use (lemma-2-1-3
                        lemma-2-1-4)))
  :rule-classes ())

(local-defthm *-weakly-monotonic
  (implies (and (rationalp y)
                (rationalp y+)
                (rationalp x)
                (> x 0))
           (iff (<= y y+)
                (<= (* x y) (* x y+))))
  :rule-classes ())

(local-defthm lemma-2-1-6
  (implies (and (rationalp a)
                (rationalp b)
                (> a 0)
                (<= -1 (* a b))
                (< (* a b) 1))
           (and (<= (- (/ a)) b)
                (< b (/ a))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x a) (y (- (/ a))) (y+ b))))))

(local-defthm lemma-2-1-7
  (implies (and (natp k)
                (<= (- (d$)) (p$ k))
                (< (p$ k) (d$)))
           (and (<= (- (/ (expt 2 (* k (rho$)))))
                    (- (/ (x$) (d$)) (q$ k)))
                (<  (- (/ (x$) (d$)) (q$ k))
                    (/ (expt 2 (* k (rho$)))))))
  :hints (("Goal" :use (lemma-2-1-5
                        (:instance lemma-2-1-6 (a (expt 2 (* k (rho$)))) (b (- (/ (x$) (d$)) (q$ k)))))))
  :rule-classes ())

(defthm lemma-2-1-corollary
  (implies (and (natp k)
                (<= (- (d$)) (p$ k))
                (< (p$ k) (d$)))
           (and (<= (- (/ (expt 2 (* k (rho$)))))
                    (- (/ (x$) (d$)) (q$ k)))
                (< (- (/ (x$) (d$)) (q$ k))
                   (/ (expt 2 (* k (rho$)))))))
  :hints (("Goal" :use (lemma-2-1-7)))
  :rule-classes ())

)

;;**********************************************************************************

(encapsulate ()

; Matt K., 10/6/2013, avoiding dependence on rel8:
; (local (include-book "rtl/rel8/lib/arith" :dir :system))

;; bozo, jared, yuck: changing the order of these includes breaks the proof of div-table-1!!
(local (include-book "arith"))
(local (include-book "arithmetic-5/top" :dir :system))

(local (deftheory jared-disables-1
         #!acl2
         '(SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE)
           ; mattk mod (:TYPE-PRESCRIPTION rtl::EXPT-2-POSITIVE-INTEGER-TYPE)
           )))

(local (deftheory jared-disables-2
         #!acl2
         '((:TYPE-PRESCRIPTION NOT-INTEGERP-3B)
           ; mattk mod (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE)
           ; mattk mod (:TYPE-PRESCRIPTION EXPT-2-POSITIVE-RATIONAL-TYPE)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))))

(local (deftheory jared-disables-3
         #!acl2
         '((:TYPE-PRESCRIPTION NOT-INTEGERP-4B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT)
           ; mattk mod a14
           (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION)
           ; mattk mod new: RATIONALP-X
           ; mattk mod (:TYPE-PRESCRIPTION EXPT-POSITIVE-INTEGER-TYPE)
           )))

(defund delta0 (j n)
  (1+ (/ j (expt 2 n))))

(defund pi0 (i m)
  (if (< i (expt 2 (1- m)))
      (/ i (expt 2 (- m 2)))
    (- (/ i (expt 2 (- m 2)))
       4)))

(defund div-accessible-p (i j m n)
  (and (< (- (- (delta0 j n)) (+ (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
          (pi0 i m))
       (< (pi0 i m)
          (+ (delta0 j n) (/ (expt 2 n))))))

(defund lower (i j rho m n)
  (min (1- (expt 2 rho))
       (if (or (< i (expt 2 (1- m)))
               (= i (1- (expt 2 m))))
           (1- (cg (* (expt 2 rho)
                      (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                         (delta0 j n)))))
         (1- (cg (* (expt 2 rho)
                    (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                       (+ (delta0 j n) (/ (expt 2 n))))))))))

(defund upper (i j rho m n)
  (max (- 1 (expt 2 rho))
       (if (< i (expt 2 (1- m)))
           (1+ (fl (* (expt 2 rho)
                      (/ (pi0 i m)
                         (+ (delta0 j n) (/ (expt 2 n)))))))
         (1+ (fl (* (expt 2 rho)
                    (/ (pi0 i m)
                       (delta0 j n))))))))

(defund lookup (i j table)
  (ifix (nth j (nth i table))))

(defthm integerp-lookup
  (integerp (lookup i j table))
  :hints (("Goal" :in-theory (enable lookup)))
  :rule-classes (:rewrite :type-prescription))

(defund check-div-entry (i j rho m n entry)
  (or (not (div-accessible-p i j m n))
      (and (< (- (expt 2 rho)) entry)
           (< entry (expt 2 rho))
           (<= (lower i j rho m n)
               entry)
           (<= entry
               (upper i j rho m n)))))

(defund check-div-row (i j rho m n row)
  (if (zp j)
      t
    (and (check-div-entry i (1- j) rho m n (ifix (nth (1- j) row)))
         (check-div-row i (1- j) rho m n row))))

(defund check-div-rows (i rho m n rows)
  (if (zp i)
      t
    (and (check-div-row (1- i) (expt 2 n) rho m n (nth (1- i) rows))
         (check-div-rows (1- i) rho m n rows))))

(defund admissible-div-table-p (rho m n table)
  (check-div-rows (expt 2 m) rho m n table))

(local-defthm check-div-row-lemma
  (implies (and (check-div-row i j rho m n row)
                (natp j)
                (natp k)
                (< k j))
           (check-div-entry i k rho m n (ifix (nth k row))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-div-row))))

(local-defthm check-div-rows-lemma
  (implies (and (check-div-rows i rho m n rows)
                (natp i)
                (natp k)
                (< k i))
           (check-div-row k (expt 2 n) rho m n (nth k rows)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-div-rows))))

(local-defthm check-div-table-lemma
  (implies (and (admissible-div-table-p rho m n table)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (natp m)
                (natp n)
                (natp i)
                (natp j))
           (check-div-entry i j rho m n (lookup i j table)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lookup admissible-div-table-p)
                  :use ((:instance check-div-rows-lemma (rows table) (k i) (i (expt 2 m)))
                        (:instance check-div-row-lemma (row (nth i table)) (k j) (j (expt 2 n)))))))

(defthm div-table-1
  (implies (and (natp m)
                (natp n)
                (rationalp d)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3))))))
           (div-accessible-p i j m n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable div-accessible-p))))

(local-defthm div-table-2
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table)))
           (and (integerp k)
                (< (- (expt 2 rho)) k)
                (< k (expt 2 rho))
                (<= (lower i j rho m n) k)
                (<= k (upper i j rho m n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-div-entry)
                  :use (check-div-table-lemma div-table-1))))

(local-defthm div-table-3
  (implies (and (natp rho)
                (rationalp d)
                (rationalp p)
                (<= (- d) p) (< p d)
                (= k (1- (expt 2 rho))))
           (< (* (expt 2 rho) p)
              (* (1+ k) d)))
  :rule-classes ()
  :hints (("Goal"
           :use (check-div-table-lemma div-table-1)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3
                                ))))

(local-defthm div-table-4
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho)))))
            (< k (1- (expt 2 rho))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2))))

(local-defthm div-table-5
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (>= k (1- (cg (* (expt 2 rho)
                             (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                (delta0 j n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lower)
                  :use (div-table-4 div-table-2))))

(local-defthm div-table-6
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (natp i))
            (>= (cg (* (expt 2 rho)
                       (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                          (delta0 j n))))
                (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                      (delta0 j n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0 delta0))))

(local-defthm div-table-7
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (>= k (1- (* (expt 2 rho)
                         (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                            (delta0 j n))))))
  :rule-classes ()
  :hints (("Goal"
           :use (div-table-6
                 div-table-5)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-8
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (>= (1+ k)
                (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                      (delta0 j n)))))
  :rule-classes ()
  :hints (("Goal"
           :use (div-table-7)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-9
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (>= (* (1+ k) (delta0 j n))
                (* (expt 2 rho)
                   (+ (pi0 i m) (/ (expt 2 (- m 3)))))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2 div-table-8)
           ;; 21.74 baseline; 15.17 disbales1; 3.11 disables 1+2, 2.23 disbales 1-3
           :in-theory (e/d (pi0 delta0)
                            (jared-disables-1
                             jared-disables-2
                             jared-disables-3)))))

(local-defthm div-table-10
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (and (integerp k)
                 (rationalp (delta0 j n))
                 (>= (delta0 j n) 1)
                 (rationalp (pi0 i m))
                 (>= (+ (pi0 i m) (/ (expt 2 (- m 3)))) 0)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2)
           :in-theory (e/d (pi0 delta0)
                            (jared-disables-1
                             ;jared-disables-2
                             jared-disables-3)))))

(local-defthm div-table-11
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
           (>= (1+ k) 0))
  :rule-classes ()
  :hints (("Goal"
           :use (div-table-10 div-table-8)
           :in-theory (disable jared-disables-1
                                ;jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-12
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (>= (* (1+ k) d)
                (* (1+ k) (delta0 j n))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-10
                        div-table-11
                        (:instance *-WEAKLY-MONOTONIC (x (1+ k)) (y (delta0 j n)) (y+ d))))))

(local-defthm div-table-13
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (>= (* (1+ k) d)
                (* (expt 2 rho)
                   (+ (pi0 i m) (/ (expt 2 (- m 3)))))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-9 div-table-12)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-14
  (implies (and (natp m)
                (natp rho)
                (rationalp p)
                (natp i)
                (< i (expt 2 m))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3))))))
            (> (* (expt 2 rho)
                  (+ (pi0 i m) (/ (expt 2 (- m 3)))))
               (* (expt 2 rho)
                  p)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0))))

(local-defthm div-table-15
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m))) (= i (1- (expt 2 m)))))
            (> (* (1+ k) d)
               (* (expt 2 rho) p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-14 div-table-13)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-16
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (>= k (1- (cg (* (expt 2 rho)
                             (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                (+ (delta0 j n) (/ (expt 2 n)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (lower)
                            (jared-disables-1
                             ;jared-disables-2
                             jared-disables-3))
           :use (div-table-4 div-table-2))))

(local-defthm div-table-17
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (natp i))
            (>= (cg (* (expt 2 rho)
                       (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                          (+ (delta0 j n) (/ (expt 2 n))))))
                (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                      (+ (delta0 j n) (/ (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0 delta0))))

(local-defthm div-table-18
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (>= k (1- (* (expt 2 rho)
                         (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                            (+ (delta0 j n) (/ (expt 2 n))))))))
  :rule-classes ()
  :hints (("Goal"
           :use (div-table-16
                 div-table-17)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-19
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (>= (1+ k)
                (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                      (+ (delta0 j n) (/ (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           :use (div-table-18))))

(local-defthm div-table-20
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (and (integerp k)
                 (rationalp (delta0 j n))
                 (>= (delta0 j n) 1)
                 (rationalp (pi0 i m))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (pi0 delta0)
                            (jared-disables-1
                             jared-disables-2
                             jared-disables-3))
           :use (div-table-2))))

(local-defthm div-table-21
  (implies (and (natp m)
                (natp i)
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
           (<= (+ (pi0 i m) 4)
               (* (/ (expt 2 (- m 2))) (- (expt 2 m) 2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (pi0)
                            (jared-disables-1
                             ;jared-disables-2
                             ;jared-disables-3
                             ))
           :use ((:instance *-weakly-monotonic
                            (x (/ (expt 2 (- m 2))))
                            (y i)
                            (y+ (- (expt 2 m) 2)))))))

(local-defthm expt-plus
  (implies (and (integerp m) (integerp n))
           (equal (expt 2 (+ m n))
                  (* (expt 2 m) (expt 2 n))))
  :rule-classes ())

(local-defthm div-table-22
  (implies (natp m)
           (equal (* (/ (expt 2 (- m 2))) (- (expt 2 m) 2))
                  (- 4 (expt 2 (- 3 m)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-plus (m (- 2 m)) (n m))
                        (:instance expt-plus (m (- 2 m)) (n 1))))))

(local-defthm div-table-23
  (implies (and (natp m)
                (natp i)
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
           (and (rationalp (pi0 i m))
                (<= (pi0 i m)
                    (- (/ (expt 2 (- m 3)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (pi0)
                                   (jared-disables-1
                                    jared-disables-2
                                    jared-disables-3))
                  :use (div-table-22 div-table-21))))

(local-defthm div-table-24
  (implies (and (natp n)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (natp j)
                (< d (+ (delta0 j n) (/ (expt 2 n)))))
            (and (rationalp (delta0 j n))
                 (< (/ (+ (delta0 j n) (/ (expt 2 n))))
                    (/ d))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0)
                  :use (div-table-20))))

(local-defthm div-table-25
  (implies (and (natp m)
                (natp i)
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m)))
                (natp n)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (natp j)
                (< d (+ (delta0 j n) (/ (expt 2 n)))))
            (>= (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                      (+ (delta0 j n) (/ (expt 2 n)))))
                (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                      d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-23
                        div-table-24
                        (:instance *-weakly-monotonic-negative-multiplier
                                   (x (* (expt 2 rho) (+ (pi0 i m) (/ (expt 2 (- m 3))))))
                                   (y (/ (+ (delta0 j n) (/ (expt 2 n)))))
                                   (y+ (/ d))))
           :in-theory (disable jared-disables-1
                               jared-disables-3
                               acl2::NOT-INTEGERP-4E
                               acl2::NOT-INTEGERP-3B
                               acl2::NOT-INTEGERP-2B
                               acl2::NOT-INTEGERP-1B
                               acl2::NOT-INTEGERP-3E
                               acl2::NOT-INTEGERP-2E
                               acl2::NOT-INTEGERP-1E
                               ;; ---
                               acl2::not-integerp-4a-expt
                               acl2::not-integerp-2a-expt
                               acl2::not-integerp-1d-expt
                               acl2::not-integerp-3d-expt
                               )
           )))

(local-defthm div-table-26
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x y)
                (>= y z))
           (>= x z))
  :rule-classes ())

(local-defthm div-table-27
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (>= (1+ k)
                (* (expt 2 rho)
                   (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                       d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-19
                        div-table-20
                        div-table-25
                        (:instance div-table-26
                                   (x (1+ k))
                                   (y (* (expt 2 rho)
                                         (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                            (+ (delta0 j n) (/ (expt 2 n))))))
                                   (z (* (expt 2 rho)
                                         (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                            d)))))
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-28
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (>= (* (1+ k) d)
                (* (expt 2 rho)
                   (+ (pi0 i m) (/ (expt 2 (- m 3)))))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-27
                        div-table-20
                        (:instance *-weakly-monotonic
                                   (x d)
                                   (y+ (1+ k))
                                   (y (* (expt 2 rho)
                                         (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                            d)))))
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3))))

(local-defthm div-table-29
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (>= (* (expt 2 rho)
                   (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (* (expt 2 rho)
                   p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-27
                        div-table-20
                        (:instance *-strongly-monotonic
                                   (x (expt 2 rho))
                                   (y+ (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                                   (y p)))
           :in-theory (disable jared-disables-1
                                jared-disables-3)
           )))

(local-defthm div-table-30
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (1- (expt 2 rho))))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
            (> (* (1+ k) d)
               (* (expt 2 rho)
                  p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-28
                        div-table-29)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3)
           )))

(local-defthm div-table-31
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table)))
            (> (* (1+ k) d)
               (* (expt 2 rho) p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-3
                        div-table-15
                        div-table-30)
           :in-theory (disable jared-disables-1
                                ;;jared-disables-2
                                ;;jared-disables-3
                                )
           )))

(local-defthm div-table-3-1
  (implies (and (natp rho)
                (rationalp d)
                (rationalp p)
                (<= (- d) p) (< p d)
                (= k (- 1 (expt 2 rho))))
           (>= (* (expt 2 rho) p)
               (* (1- k) d)))
  :rule-classes ()
  :hints (("Goal" :use (check-div-table-lemma div-table-1)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3
                                )
           )))

(local-defthm div-table-4-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho)))))
            (> k (- 1 (expt 2 rho))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2))))

(local-defthm div-table-5-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (< i (expt 2 (1- m))))
            (<= k (1+ (fl (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n)))))))))
  :rule-classes ()
  :hints (("Goal"
           :use (div-table-4-1 div-table-2)
           :in-theory (e/d (upper)
                            (jared-disables-1
                             jared-disables-2
                             jared-disables-3))
           )))

(local (in-theory (disable jared-disables-1)))

(local-defthm div-table-6-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (natp i))
            (<= (fl (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n))))))
                (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0 delta0))))

(local-defthm div-table-7-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (< i (expt 2 (1- m))))
            (<= k (1+ (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n))))))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-6-1
                        div-table-5-1))))

(local-defthm div-table-8-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (< i (expt 2 (1- m))))
            (<= (1- k) (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n)))))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-7-1))))

(local-defthm div-table-9-1
  (implies (and (natp m)
                (natp n)
                (natp j)
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 (1- m))))
            (and (rationalp (delta0 j n))
                 (>= (delta0 j n) 1)
                 (rationalp (pi0 i m))
                 (>= (pi0 i m) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0 pi0))))

(local-defthm div-table-10-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (rationalp d)
                (<= 1 d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 (1- m))))
            (<= (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n)))))
                (* (expt 2 rho) (/ (pi0 i m) d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-9-1
                        (:instance *-weakly-monotonic
                                   (x (* (expt 2 rho) (pi0 i m)))
                                   (y (/ (+ (delta0 j n) (expt 2 (- n)))))
                                   (y+ (/ d)))))))

(local-defthm div-table-11-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (rationalp d)
                (<= 1 d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (rationalp p)
                (< (pi0 i m) p)
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 (1- m))))
            (<= (* (expt 2 rho) (/ (pi0 i m) d))
                (* (expt 2 rho) (/ p d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-9-1
                        (:instance *-weakly-monotonic
                                   (x (/ (expt 2 rho) d))
                                   (y (pi0 i m))
                                   (y+ p))))))

(local-defthm div-table-12-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (rationalp d)
                (<= 1 d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (rationalp p)
                (<= (pi0 i m) p)
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 (1- m))))
            (<= (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n)))))
                (* (expt 2 rho) (/ p d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-9-1
                        div-table-10-1
                        div-table-11-1)
           :in-theory (disable jared-disables-1
                                ;;jared-disables-2
                                jared-disables-3
                                )
           )))

(local-defthm div-table-13-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (< i (expt 2 (1- m))))
            (<= (1- k) (* (expt 2 rho) (/ p d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2
                        div-table-8-1
                        div-table-9-1
                        div-table-12-1
                        (:instance div-table-26
                                   (x (* (expt 2 rho) (/ p d)))
                                   (y (* (expt 2 rho) (/ (pi0 i m) (+ (delta0 j n) (expt 2 (- n))))))
                                   (z (1- k))))
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3
                                )
           )))

(local-defthm div-table-14-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (< i (expt 2 (1- m))))
            (<= (* (1- k) d)
                (* (expt 2 rho) p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2
                        div-table-8-1
                        div-table-13-1
                        (:instance *-weakly-monotonic
                                   (x d)
                                   (y (1- k))
                                   (y+ (* (expt 2 rho) (/ p d)))))
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3
                                )
           )))

(local-defthm div-table-15-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (>= i (expt 2 (1- m))))
            (<= k (1+ (fl (* (expt 2 rho) (/ (pi0 i m) (delta0 j n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable upper)
                  :use (div-table-4-1 div-table-2)
                  )))

(local-defthm div-table-16-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (natp i))
            (<= (fl (* (expt 2 rho) (/ (pi0 i m) (delta0 j n))))
                (* (expt 2 rho) (/ (pi0 i m) (delta0 j n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0 delta0))))

(local-defthm div-table-17-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (>= i (expt 2 (1- m))))
            (<= k (1+ (* (expt 2 rho) (/ (pi0 i m) (delta0 j n))))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-16-1
                        div-table-15-1))))

(local-defthm div-table-18-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (>= i (expt 2 (1- m))))
            (<= (1- k) (* (expt 2 rho) (/ (pi0 i m) (delta0 j n)))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-17-1))))

(local-defthm div-table-19-1
  (implies (and (natp m)
                (natp n)
                (natp j)
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 m))
                (>= i (expt 2 (1- m))))
            (and (rationalp (delta0 j n))
                 (>= (delta0 j n) 1)
                 (rationalp (pi0 i m))
                 (<= (pi0 i m) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0 pi0))))

(local-defthm div-table-20-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (rationalp d)
                (<= 1 d)
                (>= d (delta0 j n))
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 m))
                (>= i (expt 2 (1- m))))
            (<= (* (expt 2 rho) (/ (pi0 i m) (delta0 j n)))
                (* (expt 2 rho) (/ (pi0 i m) d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-19-1
                        (:instance *-weakly-monotonic-negative-multiplier
                                   (x (* (expt 2 rho) (pi0 i m)))
                                   (y+ (/ (delta0 j n)))
                                   (y (/ d))))
           )))

(local-defthm div-table-21-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (rationalp d)
                (<= 1 d)
                (>= d (delta0 j n))
                (rationalp p)
                (< (pi0 i m) p)
                (< j (expt 2 n))
                (natp i)
                (>= i (expt 2 (1- m))))
            (<= (* (expt 2 rho) (/ (pi0 i m) d))
                (* (expt 2 rho) (/ p d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-19-1
                        (:instance *-weakly-monotonic
                                   (x (/ (expt 2 rho) d))
                                   (y (pi0 i m))
                                   (y+ p))))))

(local-defthm div-table-22-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp j)
                (rationalp d)
                (<= 1 d)
                (>= d (delta0 j n))
                (rationalp p)
                (<= (pi0 i m) p)
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 m))
                (>= i (expt 2 (1- m))))
            (<= (* (expt 2 rho) (/ (pi0 i m) (delta0 j n)))
                (* (expt 2 rho) (/ p d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-19-1
                        div-table-20-1
                        div-table-21-1)
           :in-theory (disable jared-disables-1
                                ;;jared-disables-2
                                jared-disables-3
                                )
           )))

(local-defthm div-table-23-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (>= i (expt 2 (1- m))))
            (<= (1- k) (* (expt 2 rho) (/ p d))))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2
                        div-table-18-1
                        div-table-19-1
                        div-table-22-1
                        (:instance div-table-26
                                   (x (* (expt 2 rho) (/ p d)))
                                   (y (* (expt 2 rho) (/ (pi0 i m) (delta0 j n))))
                                   (z (1- k))))
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3
                                )

           )))

(local-defthm div-table-24-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table))
                (not (= k (- 1 (expt 2 rho))))
                (>= i (expt 2 (1- m))))
            (<= (* (1- k) d)
                (* (expt 2 rho) p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-2
                        div-table-18-1
                        div-table-23-1
                        (:instance *-weakly-monotonic
                                   (x d)
                                   (y (1- k))
                                   (y+ (* (expt 2 rho) (/ p d)))))
           :in-theory (e/d (;jared-disables-1
                             )
                            (jared-disables-1
                             jared-disables-2
                             jared-disables-3
                             ))

           )))

(local-defthm div-table-25-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table)))
            (<= (* (1- k) d)
                (* (expt 2 rho) p)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-24-1
                        div-table-3-1
                        div-table-14-1))))

(local-defthm div-table-26-1
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (rationalp d)
                (<= 1 d)
                (< d 2)
                (rationalp p)
                (<= (- d) p) (< p d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= k (lookup i j table)))
           (and (integerp k)
                (< (- (expt 2 rho)) k)
                (< k (expt 2 rho))
                (<= (- d) (- (* (expt 2 rho) p) (* d k)))
                (< (- (* (expt 2 rho) p) (* d k)) d)))
  :rule-classes ()
  :hints (("Goal" :use (div-table-25-1
                        div-table-31
                        div-table-2)
           :in-theory (disable jared-disables-1
                                jared-disables-2
                                jared-disables-3
                                )
           )))

(local-defthm div-table-27-1
  (implies (and (natp n)
                (natp j)
                (< j (expt 2 n)))
           (and (<= 1 (delta0 j n))
                (<= (+ (delta0 j n) (/ (expt 2 n))) 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0)
                  :use (:instance *-weakly-monotonic (y (1+ j)) (y+ (expt 2 n)) (x (expt 2 (- n)))))))

(defthm lemma-2-2
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (admissible-div-table-p rho m n table)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (rationalp p)
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (rationalp d)
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (<= (- d) p)
                (< p d)
                (= k (lookup i j table)))
           (and (< (- (expt 2 rho)) k)
                (< k (expt 2 rho))
                (<= (- d) (- (* (expt 2 rho) p) (* d k)))
                (< (- (* (expt 2 rho) p) (* d k)) d)))
  :rule-classes ()
  :hints (("Goal"
           :use ((:instance div-table-26-1 (k (lookup i j table)))
                 div-table-27-1)
           :in-theory (e/d (lookup)
                            (jared-disables-1
                             jared-disables-2
                             jared-disables-3
                             )
                            ))))

)


;;**********************************************************************************

(include-book "arithmetic-5/top" :dir :system)

(local (deftheory jared-disables-1
         #!acl2
         '(SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE)
           )))

(local (deftheory jared-disables-2
         #!acl2
         '((:TYPE-PRESCRIPTION NOT-INTEGERP-3B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))))

(local (deftheory jared-disables-3
         #!acl2
         '((:TYPE-PRESCRIPTION NOT-INTEGERP-4B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT)
           (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION)
           )))

(local (deftheory jared-disables-4
         #!acl2
         '(not-integerp-1a
           not-integerp-2a
           not-integerp-3a
           not-integerp-4a
           not-integerp-1d
           not-integerp-2d
           not-integerp-3d
           not-integerp-4d
           not-integerp-1f
           not-integerp-2f
           not-integerp-3f
           not-integerp-4f
           default-plus-1
           default-plus-2
           default-times-1
           default-times-2)))

;; Assume that dmin < dmax and pmin < pmax.  Consider the closed rectangle
;;   R = {(d,p) | dmin <= d <= dmax and pmin <= p <= pmax}
;; and the half-open rectangle
;;   R' = {(d,p) | dmin <= d < dmax and pmin <= p < pmax}.
;; If there exists (d,p) in R such that p < h*d, then (d1,p1) is a point
;; in R' with p1 < h*d1:

(defund d1 (dmin pmin dmax pmax h)
  (declare (ignore pmax))
  (if (< pmin (* h dmin))
      dmin
    (/ (+ (/ pmin h) dmax) 2)))

(defund p1 (dmin pmin dmax pmax h)
  (declare (ignore dmin dmax pmax h))
  pmin)

;; If there exists (d,p) in R such that p > h*d, then (d2,p2) is a point
;; in R' with p2 > h*d2:

(defund d2 (dmin pmin dmax pmax h)
  (declare (ignore pmin))
  (if (> pmax (* h dmin))
      dmin
    (/ (+ (/ pmax h) dmax) 2)))

(defund p2 (dmin pmin dmax pmax h)
  (let ((d2 (d2 dmin pmin dmax pmax h)))
    (if (> pmin (* h d2))
        pmin
      (/ (+ (* h d2) pmax) 2))))

;; If (d1,p1) and (d2,p2) are in points in R' such that p1 < h*d1 and
;; p2 > h*d2, then (d3,p3) is in R' and p3 = h*d3:

(defund d3 (d1 p1 d2 p2 h)
  (if (= h 0)
      d1
    (if (<= p1 p2)
        (if (<= p2 (* h d1))
            (/ p2 h)
          d1)
      (if (<= p1 (* h d2))
          d2
        (/ p1 h)))))

(defund p3 (d1 p1 d2 p2 h)
  (if (= h 0)
      0
    (if (<= p1 p2)
        (if (<= p2 (* h d1))
            p2
          (* h d1))
      (if (<= p1 (* h d2))
          (* h d2)
        p1))))

;; Assume hmin < hmax.  If there exist (d1,p1) and (d2,p2) in R such
;; that p1 < hmax*d1 and p2 > hmin*d2, then (d4,p4) is in R' and
;; hmin*d4 < p4 < hmax*d4:

(defund d4 (dmin pmin dmax pmax hmin hmax)
  (let ((d1 (d1 dmin pmin dmax pmax hmax))
        (p1 (p1 dmin pmin dmax pmax hmax)))
    (if (> p1 (* hmin d1))
        d1
      (let ((d2 (d2 dmin pmin dmax pmax hmin))
            (p2 (p2 dmin pmin dmax pmax hmin)))
        (if (< p2 (* hmax d2))
            d2
          (d3 d1 p1 d2 p2 (/ (+ hmin hmax) 2)))))))

(defund p4 (dmin pmin dmax pmax hmin hmax)
  (let ((d1 (d1 dmin pmin dmax pmax hmax))
        (p1 (p1 dmin pmin dmax pmax hmax)))
    (if (> p1 (* hmin d1))
        p1
      (let ((d2 (d2 dmin pmin dmax pmax hmin))
            (p2 (p2 dmin pmin dmax pmax hmin)))
        (if (< p2 (* hmax d2))
            p2
          (p3 d1 p1 d2 p2 (/ (+ hmin hmax) 2)))))))

;; Suppose that admissible-div-table-p rho m n table) = NIL.
;; Let i = (i-witness rho m n table), j = (j-witness rho m n table),
;; and entry = (lookup i j table).
;; Then 0 <= i < 2^m, 0 <= j < 2^n, and
;; (check-div-entry i j rho m n entry) = NIL.
;; Let d = (d-witness rho m n table) and p = (p-witness rho m n table).
;; Then (d,p) is in S_ij and |p| <= d.
;; If -2^rho < entry < 2^rho, then |2^rho * p - entry * d| > d:

(defund i-witness-aux (i rho m n table)
  (if (zp i)
      ()
    (if (check-div-row (1- i) (expt 2 n) rho m n (nth (1- i) table))
        (i-witness-aux (1- i) rho m n table)
      (1- i))))

(defund i-witness (rho m n table)
  (i-witness-aux (expt 2 m) rho m n table))

(defund j-witness-aux (i j rho m n row)
  (if (zp j)
      ()
    (if (check-div-entry i (1- j) rho m n (ifix (nth (1- j) row)))
        (j-witness-aux i (1- j) rho m n row)
      (1- j))))

(defund j-witness (rho m n table)
  (let ((i (i-witness rho m n table)))
    (j-witness-aux i (expt 2 n) rho m n (nth i table))))

(defund d-witness (rho m n table)
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (entry (lookup i j table)))
    (if (or (>= entry (expt 2 rho))
            (<= entry (- (expt 2 rho))))
        (d4 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            -1
            1)
      (if (< entry (lower i j rho m n))
          (d4 (delta0 j n)
              (pi0 i m)
              (+ (delta0 j n) (expt 2 (- n)))
              (+ (pi0 i m) (expt 2 (- 3 m)))
              (/ (1+ entry) (expt 2 rho))
              1)
        (d4 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            -1
            (/ (1- entry) (expt 2 rho)))))))

(defund p-witness (rho m n table)
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (entry (lookup i j table)))
    (if (or (>= entry (expt 2 rho))
            (<= entry (- (expt 2 rho))))
        (p4 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            -1
            1)
      (if (< entry (lower i j rho m n))
          (p4 (delta0 j n)
              (pi0 i m)
              (+ (delta0 j n) (expt 2 (- n)))
              (+ (pi0 i m) (expt 2 (- 3 m)))
              (/ (1+ entry) (expt 2 rho))
              1)
        (p4 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            -1
            (/ (1- entry) (expt 2 rho)))))))

(local-defthm converse-1
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h) (= h 0)
                (< p (* h d)))
           (let ((d1 (d1 dmin pmin dmax pmax h))
                 (p1 (p1 dmin pmin dmax pmax h)))
             (and (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax))))
;                  (< p1 (* h d1)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable d1 p1))))

(local-defthm converse-2
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (not (= h 0))
                (< pmin (* h dmin))
                (< p (* h d)))
           (let ((d1 (d1 dmin pmin dmax pmax h))
                 (p1 (p1 dmin pmin dmax pmax h)))
             (and (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (< d1 dmax)
                  (<= pmin p1)
                  (< p1 pmax))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable d1 p1))))

(local-defthm converse-3
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (not (= h 0))
                (< h 0)
                (< p (* h d)))
           (<= (* d h) (* h dmin)))
  :rule-classes ())

(local-defthm converse-4
  (implies (and (rationalp a1)
                (rationalp a2)
                (rationalp a3)
                (rationalp a4)
                (<= a1 a2)
                (< a2 a3)
                (<= a3 a4))
           (< a1 a4))
  :rule-classes ())

(local-defthm converse-5
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (not (= h 0))
                (< h 0)
                (< p (* h d)))
           (< pmin (* h dmin)))
  :rule-classes ()
  :hints (("Goal" :use (converse-3
                        (:instance converse-4 (a1 pmin) (a2 p) (a3 (* h d)) (a4 (* h dmin)))))))

(local-defthm converse-6
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (>= pmin (* h dmin))
                (> h 0)
                (< p (* h d)))
           (let ((d1 (/ (+ (/ pmin h) dmax) 2)))
             (and (rationalp d1)
                  (< pmin (* h d1)))))
  :rule-classes ()
  :hints (("Goal"
           :use (:instance converse-4 (a1 pmin) (a2 p) (a3 (* h d)) (a4 (* h dmax)))
           )))

(local-defthm converse-7
  (implies (and (rationalp a1)
                (rationalp a2)
                (rationalp a3)
                (<= a1 a2)
                (< a1 a3))
           (< a1 (/ (+ a2 a3) 2)))
  :rule-classes ())

(local-defthm converse-8
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp h)
                (> h 0))
           (iff (< (* pmin h) (* dmin h))
                (< pmin dmin)))
  :rule-classes ())

(local-defthm converse-9
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp h)
                (> h 0))
            (iff (< (/ pmin h) dmin)
                 (< pmin (* dmin h))))
  :rule-classes ()
  :hints (("Goal" :use (:instance converse-8 (pmin (/ pmin h))))))

(local-defthm converse-10
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (>= pmin (* h dmin))
                (> h 0)
                (< p (* h d)))
           (let ((d1 (/ (+ (/ pmin h) dmax) 2)))
             (<= dmin d1)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-9
                        (:instance converse-7 (a1 dmin) (a2 (/ pmin h)) (a3 dmax))))))

(local-defthm converse-11
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (>= pmin (* h dmin))
                (> h 0)
                (< p (* h d)))
           (< pmin (* h dmax)))
  :rule-classes ()
  :hints (("Goal"
           :use (:instance converse-4 (a1 pmin) (a2 p) (a3 (* h d)) (a4 (* h dmax))))))

(local-defthm converse-12
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (>= pmin (* h dmin))
                (> h 0)
                (< p (* h d)))
           (< (/ pmin h) dmax))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-11
                 (:instance converse-9 (dmin dmax))))))

(local-defthm converse-13
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (>= pmin (* h dmin))
                (> h 0)
                (< p (* h d)))
           (let ((d1 (/ (+ (/ pmin h) dmax) 2)))
             (< d1 dmax)))
  :rule-classes ()
  :hints (("Goal" :use (converse-12))))




(defthm d1-p1-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (< p (* h d)))
           (let ((d1 (d1 dmin pmin dmax pmax h))
                 (p1 (p1 dmin pmin dmax pmax h)))
             (and (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (< d1 dmax)
                  (<= pmin p1)
                  (< p1 pmax)
                  (< p1 (* h d1)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d1 p1)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   ))
                  :use (converse-1 converse-2 converse-5 converse-6 converse-10 converse-13))))

(local-defthm converse-14
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (> pmax (* h dmin)))
           (let ((d2 (d2 dmin pmin dmax pmax h)))
             (and (rationalp d2)
                  (<= dmin d2)
                  (< d2 dmax)
                  (> pmax (* h d2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable d2))))

(local-defthm converse-15
  (implies (and (rationalp a1)
                (rationalp a2)
                (rationalp a3)
                (rationalp a4)
                (<= a1 a2)
                (<= a2 a3)
                (<= a3 a4))
           (<= a1 a4))
  :rule-classes ())

(local-defthm converse-16
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (<= pmax (* h dmin)))
           (< h 0))
  :rule-classes ()
  :hints (("Goal"
           :use (:instance converse-15 (a1 p) (a2 pmax) (a3 (* h dmin)) (a4 (* h d)))
           :in-theory (enable jared-disables-1)
           )))

(local-defthm converse-17
  (implies (and (rationalp pmax)
                (rationalp dmin)
                (rationalp h)
                (< h 0))
           (iff (<= pmax dmin)
                (>= (* pmax h) (* dmin h))))
  :rule-classes ())

(local-defthm converse-18
  (implies (and (rationalp pmax)
                (rationalp dmin)
                (rationalp h)
                (< h 0))
           (iff (<= pmax (* h dmin))
                (>= (/ pmax h) dmin)))
  :rule-classes ()
  :hints (("Goal" :use (:instance converse-17 (dmin (* h dmin)) (h (/ h))))))

(local-defthm converse-19
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (<= pmax (* h dmin))
                (< h 0))
           (let ((d2 (/ (+ (/ pmax h) dmax) 2)))
             (and (rationalp d2)
                  (< dmin d2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-18
                        (:instance converse-7 (a1 dmin) (a2 (/ pmax h)) (a3 dmax))))))

(local-defthm converse-20
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (<= pmax (* h dmin))
                (< h 0))
           (> pmax (* h dmax)))
  :rule-classes ()
  :hints (("Goal"
           :use ((:instance converse-4 (a1 (* h dmax)) (a2 (* h d)) (a3 p) (a4 pmax)))
           )))

(local-defthm converse-21
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (<= pmax (* h dmin))
                (< h 0))
           (< (/ pmax h) dmax))
  :rule-classes ()
  :hints (("Goal" :use (converse-20
                        (:instance converse-18 (dmin dmax))))))

(local-defthm converse-22
  (implies (and (rationalp a1)
                (rationalp a2)
                (rationalp a3)
                (>= a1 a2)
                (> a1 a3))
           (> a1 (/ (+ a2 a3) 2)))
  :rule-classes ())

(local-defthm converse-23
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (<= pmax (* h dmin))
                (< h 0))
           (let ((d2 (d2 dmin pmin dmax pmax h)))
             (and (rationalp d2)
                  (< dmin d2)
                  (< d2 dmax))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d2)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   ))
                  :use (converse-21
                        converse-19
                        (:instance converse-22 (a1 dmax) (a2 dmax) (a3 (/ pmax h)))))))

(local-defthm converse-24
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (<= pmax (* h dmin))
                (< h 0))
           (let ((d2 (d2 dmin pmin dmax pmax h)))
             (and (rationalp d2)
                  (< dmin d2)
                  (< d2 dmax)
                  (> pmax (* h d2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d2)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
                  :use (converse-21
                        converse-23
                        (:instance converse-17 (pmax (d2 dmin pmin dmax pmax h)) (dmin (/ pmax h)))
                        (:instance converse-7 (a1 (/ pmax h)) (a2 (/ pmax h)) (a3 dmax))))))

(local-defthm converse-25
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d)))
           (let ((d2 (d2 dmin pmin dmax pmax h)))
             (and (rationalp d2)
                  (<= dmin d2)
                  (< d2 dmax)
                  (> pmax (* h d2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d2 p2)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
                  :use (converse-24 converse-14 converse-16))))

(local-defthm converse-26
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d)))
           (let ((d2 (d2 dmin pmin dmax pmax h))
                 (p2 (p2 dmin pmin dmax pmax h)))
             (implies (> pmin (* h d2))
                      (and (rationalp p2)
                           (<= pmin p2)
                           (< p2 pmax)
                           (> p2 (* h d2))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p2)
                  :use (converse-25))))

(local-defthm converse-27
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d))
                (rationalp d2)
                (<= dmin d2)
                (< d2 dmax)
                (> pmax (* h d2))
                (<= pmin (* h d2)))
           (let ((p2 (/ (+ (* h d2) pmax) 2)))
             (and (rationalp p2)
                  (<= pmin p2)
                  (< p2 pmax)
                  (> p2 (* h d2)))))
  :rule-classes ())

(defthm d2-p2-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (> p (* h d)))
           (let ((d2 (d2 dmin pmin dmax pmax h))
                 (p2 (p2 dmin pmin dmax pmax h)))
             (and (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (< d2 dmax)
                  (<= pmin p2)
                  (< p2 pmax)
                  (> p2 (* h d2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (p2)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   acl2::rationalp-x
                                   acl2::default-less-than-1
                                   acl2::default-less-than-2
                                   ))
                  :use (converse-27 converse-26 converse-25))))

(local-defthm converse-28
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d1)
                (rationalp p1)
                (rationalp d2)
                (rationalp p2)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d1)
                (< d1 dmax)
                (<= pmin p1)
                (< p1 pmax)
                (<= dmin d2)
                (<= d2 dmax)
                (<= pmin p2)
                (<= p2 pmax)
                (rationalp h)
                (< p1 (* h d1))
                (> p2 (* h d2))
                (= h 0))
           (let ((d3 (d3 d1 p1 d2 p2 h))
                 (p3 (p3 d1 p1 d2 p2 h)))
             (and (rationalp d3)
                  (rationalp p3)
                  (<= dmin d3)
                  (< d3 dmax)
                  (<= pmin p3)
                  (< p3 pmax)
                  (= p3 (* h d3)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable d3 p3))))

(local-defthm converse-29
  (implies (and (rationalp p)
                (rationalp h)
                (rationalp d)
                (not (= h 0)))
           (if (> h 0)
               (and (iff (> (* h a) (* h b))
                         (> a b))
                    (iff (< (* h a) (* h b))
                         (< a b)))
             (and (iff (> (* h a) (* h b))
                       (< a b))
                  (iff (< (* h a) (* h b))
                       (> a b)))))
  :rule-classes ())

(local-defthm converse-30
  (implies (and (rationalp p)
                (rationalp h)
                (rationalp d)
                (not (= h 0)))
           (if (> h 0)
               (and (iff (> p (* h d))
                         (> (/ p h) d))
                    (iff (< p (* h d))
                         (< (/ p h) d)))
             (and (iff (> p (* h d))
                       (< (/ p h) d))
                  (iff (< p (* h d))
                       (> (/ p h) d)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (:instance converse-29 (a (/ p h)) (b d)))))

(local-defthm converse-31
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d1)
                (rationalp p1)
                (rationalp d2)
                (rationalp p2)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d1)
                (< d1 dmax)
                (<= pmin p1)
                (< p1 pmax)
                (<= dmin d2)
                (< d2 dmax)
                (<= pmin p2)
                (< p2 pmax)
                (rationalp h)
                (< p1 (* h d1))
                (> p2 (* h d2))
                (not (= h 0))
                (<= p1 p2))
           (let ((d3 (d3 d1 p1 d2 p2 h))
                 (p3 (p3 d1 p1 d2 p2 h)))
             (and (rationalp d3)
                  (rationalp p3)
                  (<= dmin d3)
                  (< d3 dmax)
                  (<= pmin p3)
                  (< p3 pmax)
                  (= p3 (* h d3)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d3 p3)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   acl2::default-less-than-1
                                   acl2::default-less-than-2
                                   acl2::rationalp-x
                                   acl2::remove-strict-inequalities
                                   ))
                  :use ((:instance converse-30 (p p2) (d d1))
                        (:instance converse-30 (p p2) (d d2))))))

(local-defthm converse-32
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d1)
                (rationalp p1)
                (rationalp d2)
                (rationalp p2)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d1)
                (< d1 dmax)
                (<= pmin p1)
                (< p1 pmax)
                (<= dmin d2)
                (< d2 dmax)
                (<= pmin p2)
                (< p2 pmax)
                (rationalp h)
                (< p1 (* h d1))
                (> p2 (* h d2))
                (not (= h 0))
                (> p1 p2))
           (let ((d3 (d3 d1 p1 d2 p2 h))
                 (p3 (p3 d1 p1 d2 p2 h)))
             (and (rationalp d3)
                  (rationalp p3)
                  (<= dmin d3)
                  (< d3 dmax)
                  (<= pmin p3)
                  (< p3 pmax)
                  (= p3 (* h d3)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d3 p3)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
                  :use ((:instance converse-30 (p p1) (d d1))
                        (:instance converse-30 (p p1) (d d2))))))

(defthm d3-p3-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d1)
                (rationalp p1)
                (rationalp d2)
                (rationalp p2)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d1)
                (< d1 dmax)
                (<= pmin p1)
                (< p1 pmax)
                (<= dmin d2)
                (< d2 dmax)
                (<= pmin p2)
                (< p2 pmax)
                (rationalp h)
                (< p1 (* h d1))
                (> p2 (* h d2)))
           (let ((d3 (d3 d1 p1 d2 p2 h))
                 (p3 (p3 d1 p1 d2 p2 h)))
             (and (rationalp d3)
                  (rationalp p3)
                  (<= dmin d3)
                  (< d3 dmax)
                  (<= pmin p3)
                  (< p3 pmax)
                  (= p3 (* h d3)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-28 converse-31 converse-32))))

(defthm d4-p4-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d1)
                (rationalp p1)
                (rationalp d2)
                (rationalp p2)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d1)
                (<= d1 dmax)
                (<= pmin p1)
                (<= p1 pmax)
                (<= dmin d2)
                (<= d2 dmax)
                (<= pmin p2)
                (<= p2 pmax)
                (rationalp hmax)
                (rationalp hmin)
                (< hmin hmax)
                (< p1 (* hmax d1))
                (> p2 (* hmin d2)))
           (let ((d4 (d4 dmin pmin dmax pmax hmin hmax))
                 (p4 (p4 dmin pmin dmax pmax hmin hmax)))
             (and (rationalp d4)
                  (rationalp p4)
                  (<= dmin d4)
                  (< d4 dmax)
                  (<= pmin p4)
                  (< p4 pmax)
                  (< p4 (* hmax d4))
                  (> p4 (* hmin d4)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d4 p4)
                                  (;jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   acl2::default-less-than-1
                                   acl2::default-less-than-2
                                   acl2::rationalp-x
                                   ))
                  :use ((:instance d1-p1-lemma (d d1) (p p1) (h hmax))
                        (:instance d2-p2-lemma (d d2) (p p2) (h hmin))
                        (:instance d3-p3-lemma (d1 (d1 dmin pmin dmax pmax hmax))
                                               (p1 (p1 dmin pmin dmax pmax hmax))
                                               (d2 (d2 dmin pmin dmax pmax hmin))
                                               (p2 (p2 dmin pmin dmax pmax hmin))
                                               (h (/ (+ hmin hmax) 2)))))))


(local-defthm converse-33
  (implies (and (natp i)
                (not (check-div-rows i rho m n table)))
           (let ((w (i-witness-aux i rho m n table)))
             (and (natp w)
                  (< w i)
                  (not (check-div-row w (expt 2 n) rho m n (nth w table))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable i-witness-aux check-div-rows))))

(local-defthm converse-34
  (implies (and (natp m)
                (not (admissible-div-table-p rho m n table)))
           (let ((i (i-witness rho m n table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (not (check-div-row i (expt 2 n) rho m n (nth i table))))))
  :rule-classes ()
  :hints (("Goal" :use (:instance converse-33 (i (expt 2 m)))
                  :in-theory (enable i-witness admissible-div-table-p))))

(local-defthm converse-35
  (implies (and (natp j)
                (not (check-div-row i j rho m n row)))
           (let ((w (j-witness-aux i j rho m n row)))
             (and (natp w)
                  (< w j)
                  (not (check-div-entry i w rho m n (ifix (nth w row)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable j-witness-aux check-div-row))))

(defthm div-witness-lemma
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (admissible-div-table-p rho m n table)))
           (let* ((i (i-witness rho m n table))
                  (j (j-witness rho m n table))
                  (k (lookup i j table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (not (and (< (- (expt 2 rho)) k)
                            (< k (expt 2 rho))
                            (>= k (lower i j rho m n))
                            (<= k (upper i j rho m n)))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-34
                        (:instance converse-35 (i (i-witness rho m n table))
                                               (j (expt 2 n))
                                               (row (nth (i-witness rho m n table) table))))
                  :in-theory (enable lookup check-div-entry j-witness))))

(local-defthm converse-37
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (< k (expt 2 rho))
                (not (check-div-entry i j rho m n k)))
           (and (< (- (- (delta0 j n)) (+ (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
                   (pi0 i m))
                (< (pi0 i m)
                   (+ (delta0 j n) (/ (expt 2 n))))
                (or (< k (lower i j rho m n))
                    (> k (upper i j rho m n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-div-entry div-accessible-p))))

(local-defthm converse-38
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (< k (lower i j rho m n)))
           (and (< k (1- (expt 2 rho)))
                (or (< (1+ k)
                       (cg (* (expt 2 rho)
                              (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                 (delta0 j n)))))
                    (< (1+ k)
                       (cg (* (expt 2 rho)
                              (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                 (+ (delta0 j n) (/ (expt 2 n))))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lower))))

(local-defthm converse-39
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (rationalp (delta0 j n))
                (rationalp (pi0 i m))
                (>= (delta0 j n) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0 pi0))))

(local-defthm converse-40
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (< k (lower i j rho m n)))
           (or (< (1+ k)
                  (* (expt 2 rho)
                     (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                        (delta0 j n))))
               (< (1+ k)
                  (* (expt 2 rho)
                     (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                        (+ (delta0 j n) (/ (expt 2 n))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-38
                 converse-39
                 (:instance cg-unique
                            (x (* (expt 2 rho)
                                  (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                     (+ (delta0 j n) (/ (expt 2 n))))))
                            (n (1+ k)))
                 (:instance cg-unique
                            (x (* (expt 2 rho)
                                  (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                     (+ (delta0 j n)))))
                            (n (1+ k)))))))

(local-defthm converse-41
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (1+ k)
                  (* (expt 2 rho)
                     (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                        (delta0 j n)))))
           (< (* (/ (1+ k) (expt 2 rho)) (delta0 j n))
              (+ (pi0 i m) (/ (expt 2 (- m 3))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                        (:instance converse-8
                                   (pmin (1+ k))
                                   (h (/ (delta0 j n) (expt 2 rho)))
                                   (dmin (* (expt 2 rho)
                                            (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                               (delta0 j n)))))))))

(local-defthm converse-42
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (rationalp x)
                (> x 0)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (1+ k)
                  (* (expt 2 rho)
                     (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                        x))))
           (< (* (/ (1+ k) (expt 2 rho)) x)
              (+ (pi0 i m) (/ (expt 2 (- m 3))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4)

           :use (converse-39
                        (:instance converse-8
                                   (pmin (1+ k))
                                   (h (/ x (expt 2 rho)))
                                   (dmin (* (expt 2 rho)
                                            (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                               x))))))))

(local-defthm converse-43
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (1+ k)
                  (* (expt 2 rho)
                     (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                        (+ (delta0 j n) (/ (expt 2 n)))))))
           (< (* (/ (1+ k) (expt 2 rho)) (+ (delta0 j n) (/ (expt 2 n))))
              (+ (pi0 i m) (/ (expt 2 (- m 3))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        (:instance converse-42 (x (+ (delta0 j n) (/ (expt 2 n)))))))))

(local-defthm converse-44
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (< k (lower i j rho m n)))
           (and (< k (1- (expt 2 rho))           )
                (or (< (* (/ (1+ k) (expt 2 rho)) (delta0 j n))
                       (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                    (< (* (/ (1+ k) (expt 2 rho)) (+ (delta0 j n) (/ (expt 2 n))))
                       (+ (pi0 i m) (/ (expt 2 (- m 3))))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-38
                        converse-40
                        converse-41
                        converse-43))))

(local-defthm converse-45
  (implies (and (integerp rho)
                (integerp k)
                (< k (1- (expt 2 rho))))
           (< (/ (1+ k) (expt 2 rho)) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-8 (pmin (/ (1+ k) (expt 2 rho))) (dmin 1) (h (expt 2 rho)))))))

(local-defthm converse-46
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (< (- (expt 2 rho)) k)
                  (< k (1- (expt 2 rho)))
                  (< k (lower i j rho m n))
                  (< k (expt 2 rho))
                  (< (* (/ (1+ k) (expt 2 rho)) (delta0 j n))
                     (+ (pi0 i m) (/ (expt 2 (- m 3))))))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< p d)
                  (> p (* (/ (1+ k) (expt 2 rho)) d)))))
  :rule-classes ()
  :hints (("Goal"
           :use ((:instance converse-45 (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))
                        (:instance converse-39 (i (i-witness rho m n table))
                                               (j (j-witness rho m n table)))
                        (:instance d4-p4-lemma (dmin (delta0 (j-witness rho m n table) n))
                                               (dmax (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                               (pmin (pi0 (i-witness rho m n table) m))
                                               (pmax (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                               (d1 (+ (delta0 (j-witness rho m n table) n) (/ (expt 2 n))))
                                               (p1 (pi0 (i-witness rho m n table) m))
                                               (d2 (delta0 (j-witness rho m n table) n))
                                               (p2 (+ (pi0 (i-witness rho m n table) m) (/ (expt 2 (- m 3)))))
                                               (hmin (/ (1+ (lookup (i-witness rho m n table) (j-witness rho m n table) table))
                                                        (expt 2 rho)))
                                               (hmax 1)))
                  :in-theory (e/d (div-accessible-p d-witness p-witness)
                                  (;jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4)))))

(local-defthm converse-47
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (< (- (expt 2 rho)) k)
                  (< k (1- (expt 2 rho)))
                  (< k (lower i j rho m n))
                  (< k (expt 2 rho))
                  (< (* (/ (1+ k) (expt 2 rho)) (+ (delta0 j n) (/ (expt 2 n))))
                     (+ (pi0 i m) (/ (expt 2 (- m 3))))))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< p d)
                  (> p (* (/ (1+ k) (expt 2 rho)) d)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-45 (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))
                        (:instance converse-39 (i (i-witness rho m n table))
                                               (j (j-witness rho m n table)))
                        (:instance d4-p4-lemma (dmin (delta0 (j-witness rho m n table) n))
                                               (dmax (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                               (pmin (pi0 (i-witness rho m n table) m))
                                               (pmax (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                               (d1 (+ (delta0 (j-witness rho m n table) n) (/ (expt 2 n))))
                                               (p1 (pi0 (i-witness rho m n table) m))
                                               (d2 (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                               (p2 (+ (pi0 (i-witness rho m n table) m) (/ (expt 2 (- m 3)))))
                                               (hmin (/ (1+ (lookup (i-witness rho m n table) (j-witness rho m n table) table))
                                                        (expt 2 rho)))
                                               (hmax 1)))
                  :in-theory (e/d (div-accessible-p d-witness p-witness)
                                  (;jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4)))))


(local-defthm converse-48
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (< (- (expt 2 rho)) k)
                  (< k (expt 2 rho))
                  (< k (lower i j rho m n)))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< p d)
                  (> p (* (/ (1+ k) (expt 2 rho)) d)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable
                       jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4)
           :use (converse-46
                        converse-47
                        (:instance converse-44 (i (i-witness rho m n table))
                                               (j (j-witness rho m n table))
                                               (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))))))

(local-defthm converse-49
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (> (expt 2 rho) k)
                (> k (upper i j rho m n)))
           (and (> k (- 1 (expt 2 rho)))
                (or (> (1- k)
                       (fl (* (expt 2 rho)
                              (/ (pi0 i m)
                                 (delta0 j n)))))
                    (> (1- k)
                       (fl (* (expt 2 rho)
                              (/ (pi0 i m)
                                 (+ (delta0 j n) (/ (expt 2 n))))))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39)
                  :in-theory (enable upper))))

(local-defthm converse-50
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (> (expt 2 rho) k)
                (> k (upper i j rho m n)))
           (and (> k (- 1 (expt 2 rho)))
                (or (> (1- k)
                       (* (expt 2 rho)
                          (/ (pi0 i m)
                             (delta0 j n))))
                    (> (1- k)
                       (* (expt 2 rho)
                          (/ (pi0 i m)
                             (+ (delta0 j n) (/ (expt 2 n)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable
                       ;jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4)
           :use (converse-39
                        converse-49
                        (:instance fl-unique
                                   (x (* (expt 2 rho)
                                         (/ (pi0 i m)
                                            (+ (delta0 j n) (/ (expt 2 n))))))
                                   (n (1- k)))
                        (:instance fl-unique
                                   (x (* (expt 2 rho)
                                         (/ (pi0 i m)
                                            (+ (delta0 j n)))))
                                   (n (1- k)))))))

(local-defthm converse-51
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (> (1- k)
                   (* (expt 2 rho)
                      (/ (pi0 i m)
                         (delta0 j n)))))
           (> (* (/ (1- k) (expt 2 rho)) (delta0 j n))
              (pi0 i m)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                        (:instance converse-8
                                   (dmin (1- k))
                                   (h (/ (delta0 j n) (expt 2 rho)))
                                   (pmin (* (expt 2 rho)
                                            (/ (pi0 i m)
                                               (delta0 j n)))))))))

(local-defthm converse-52
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (> (1- k)
                   (* (expt 2 rho)
                      (/ (pi0 i m)
                         (+ (delta0 j n) (expt 2 (- n)))))))
           (> (* (/ (1- k) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
              (pi0 i m)))
  :rule-classes ()
  :hints (("Goal"
           :use (converse-39
                        (:instance converse-8
                                   (dmin (1- k))
                                   (h (/ (+ (delta0 j n) (expt 2 (- n))) (expt 2 rho)))
                                   (pmin (* (expt 2 rho)
                                            (/ (pi0 i m)
                                               (+ (delta0 j n) (expt 2 (- n)))))))))))

(local-defthm converse-53
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (> (expt 2 rho) k)
                (> k (upper i j rho m n)))
           (and (> k (- 1 (expt 2 rho))           )
                (or (> (* (/ (1- k) (expt 2 rho)) (delta0 j n))
                       (pi0 i m))
                    (> (* (/ (1- k) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
                       (pi0 i m)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-50
                        converse-51
                        converse-52)
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           )))

(local-defthm converse-54
  (implies (and (integerp rho)
                (integerp k)
                (> k (- 1 (expt 2 rho))))
           (> (/ (1- k) (expt 2 rho)) -1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-8 (dmin (/ (1- k) (expt 2 rho))) (pmin -1) (h (expt 2 rho)))))))

(local-defthm converse-55
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (> k (- 1 (expt 2 rho)))
                  (>= k (lower i j rho m n))
                  (< k (expt 2 rho))
                  (> (* (/ (1- k) (expt 2 rho)) (delta0 j n))
                     (pi0 i m)))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (> p (- d))
                  (< p (* (/ (1- k) (expt 2 rho)) d)))))
  :rule-classes ()
  :hints (("Goal"
           :use ((:instance converse-54 (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))
                        (:instance converse-39 (i (i-witness rho m n table))
                                               (j (j-witness rho m n table)))
                        (:instance d4-p4-lemma (dmin (delta0 (j-witness rho m n table) n))
                                               (dmax (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                               (pmin (pi0 (i-witness rho m n table) m))
                                               (pmax (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                               (d2 (+ (delta0 (j-witness rho m n table) n) (/ (expt 2 n))))
                                               (p2 (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                               (d1 (delta0 (j-witness rho m n table) n))
                                               (p1 (pi0 (i-witness rho m n table) m))
                                               (hmax (/ (1- (lookup (i-witness rho m n table) (j-witness rho m n table) table))
                                                        (expt 2 rho)))
                                               (hmin -1)))
                  :in-theory (e/d (div-accessible-p d-witness p-witness)
                                  (;jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   acl2::default-expt-2
                                   acl2::default-minus)))))


(local-defthm converse-56
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (> k (- 1 (expt 2 rho)))
                  (>= k (lower i j rho m n))
                  (< k (expt 2 rho))
                  (> (* (/ (1- k) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
                     (pi0 i m)))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (> p (- d))
                  (< p (* (/ (1- k) (expt 2 rho)) d)))))
  :rule-classes ()
  :hints (("Goal"
           :use ((:instance converse-54 (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))
                        (:instance converse-39 (i (i-witness rho m n table))
                                               (j (j-witness rho m n table)))
                        (:instance d4-p4-lemma (dmin (delta0 (j-witness rho m n table) n))
                                               (dmax (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                               (pmin (pi0 (i-witness rho m n table) m))
                                               (pmax (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                               (d2 (+ (delta0 (j-witness rho m n table) n) (/ (expt 2 n))))
                                               (p2 (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                               (d1 (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                               (p1 (pi0 (i-witness rho m n table) m))
                                               (hmax (/ (1- (lookup (i-witness rho m n table) (j-witness rho m n table) table))
                                                        (expt 2 rho)))
                                               (hmin -1)))
                  :in-theory (e/d (div-accessible-p d-witness p-witness)
                                  (;jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   acl2::default-expt-2
                                   acl2::default-minus)))))


(local-defthm converse-57
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (< (- (expt 2 rho)) k)
                  (< k (expt 2 rho))
                  (>= k (lower i j rho m n))
                  (> k (upper i j rho m n)))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (> p (- d))
                  (< p (* (/ (1- k) (expt 2 rho)) d)))))
  :rule-classes ()
  :hints (("Goal"
           :use (converse-55
                 converse-56
                 (:instance converse-53 (i (i-witness rho m n table))
                            (j (j-witness rho m n table))
                            (k (lookup (i-witness rho m n table) (j-witness rho m n table) table))))
           :in-theory (disable ;jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4
                       acl2::default-expt-2
                       acl2::default-minus)
           )))

(local-defthm converse-58
  (implies (and (integerp a)
                (not (zp b))
                (rationalp d)
                (> d 0)
                (< a b))
           (< (* (/ a b) d) d))
  :rule-classes ())

(local-defthm converse-59
  (implies (and (rationalp d)
                (rationalp p)
                (< 0 d)
                (not (zp b))
                (integerp a)
                (< a b)
                (< p (* (/ a b) d)))
            (< p d))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable acl2::simplify-products-gather-exponents-<)
                  :use (converse-58))))

(local-defthm converse-60
  (implies (and (rationalp d)
                (rationalp p)
                (< 0 d)
                (> p (- d))
                (natp rho)
                (integerp k)
                (< k (expt 2 rho))
                (< p (* (/ (1- k) (expt 2 rho)) d)))
            (< (abs p) d))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable abs)
                  :use ((:instance converse-59 (a (1- k)) (b (expt 2 rho)))))))

(local-defthm converse-61
  (implies (and (rationalp d)
                (rationalp p)
                (natp rho)
                (integerp k)
                (< k (expt 2 rho))
                (< p (* (/ (1- k) (expt 2 rho)) d)))
            (> (abs (- (* (expt 2 rho) p) (* k d))) d))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-8 (pmin p) (dmin (* (/ (1- k) (expt 2 rho)) d)) (h (expt 2 rho)))))))



(local-defthm converse-62
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (< (- (expt 2 rho)) k)
                  (< k (expt 2 rho))
                  (>= k (lower i j rho m n))
                  (> k (upper i j rho m n)))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< (abs p) d)
                  (> (abs (- (* (expt 2 rho) p) (* k d))) d))))
  :rule-classes ()
  :hints (("Goal"
           :use (converse-57
                 (:instance converse-39 (i (i-witness rho m n table))
                            (j (j-witness rho m n table)))
                 (:instance converse-60 (p (p-witness rho m n table))
                            (d (d-witness rho m n table))
                            (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))
                 (:instance converse-61 (p (p-witness rho m n table))
                            (d (d-witness rho m n table))
                            (k (lookup (i-witness rho m n table) (j-witness rho m n table) table))))
           :in-theory (disable
                       natp
                       abs
                       jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4
                       acl2::default-expt-2
                       acl2::default-less-than-2
                       acl2::default-less-than-1
                       acl2::acl2-numberp-x
                       acl2::rationalp-x
                       acl2::NOT-INTEGERP-3A-EXPT
                       acl2::NOT-INTEGERP-4a-expt
                       acl2::NOT-INTEGERP-1a-EXPT
                       acl2::NOT-INTEGERP-2a-EXPT
                       acl2::default-minus))))

(local-defthm converse-63
  (implies (and (integerp a)
                (not (zp b))
                (rationalp d)
                (> d 0)
                (> a (- b)))
           (> (* (/ a b) d) (- d)))
  :rule-classes ())

(local-defthm converse-64
  (implies (and (rationalp d)
                (rationalp p)
                (< 0 d)
                (not (zp b))
                (integerp a)
                (> a (- b))
                (> p (* (/ a b) d)))
            (> p (- d)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable acl2::simplify-products-gather-exponents-<)
                  :use (converse-63))))

(local-defthm converse-65
  (implies (and (rationalp d)
                (rationalp p)
                (< 0 d)
                (< p d)
                (natp rho)
                (integerp k)
                (> k (- (expt 2 rho)))
                (> p (* (/ (1+ k) (expt 2 rho)) d)))
            (< (abs p) d))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable abs)
                  :use ((:instance converse-64 (a (1+ k)) (b (expt 2 rho)))))))

(local-defthm converse-66
  (implies (and (rationalp d)
                (rationalp p)
                (natp rho)
                (integerp k)
                (> k (- (expt 2 rho)))
                (> p (* (/ (1+ k) (expt 2 rho)) d)))
            (> (abs (- (* (expt 2 rho) p) (* k d))) d))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-8 (dmin p) (pmin (* (/ (1+ k) (expt 2 rho)) d)) (h (expt 2 rho)))))))

(local-defthm converse-67
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (< (- (expt 2 rho)) k)
                  (< k (expt 2 rho))
                  (< k (lower i j rho m n)))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< (abs p) d)
                  (> (abs (- (* (expt 2 rho) p) (* k d))) d))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable
                       natp
                       abs
                       jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4
                       acl2::default-expt-2
                       acl2::default-less-than-2
                       acl2::default-less-than-1
                       acl2::acl2-numberp-x
                       acl2::rationalp-x
                       acl2::NOT-INTEGERP-3A-EXPT
                       acl2::NOT-INTEGERP-4a-expt
                       acl2::NOT-INTEGERP-1a-EXPT
                       acl2::NOT-INTEGERP-2a-EXPT
                       acl2::default-minus)
           :use (converse-48
                 (:instance converse-39 (i (i-witness rho m n table))
                            (j (j-witness rho m n table)))
                 (:instance converse-65 (p (p-witness rho m n table))
                            (d (d-witness rho m n table))
                            (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))
                 (:instance converse-66 (p (p-witness rho m n table))
                            (d (d-witness rho m n table))
                            (k (lookup (i-witness rho m n table) (j-witness rho m n table) table)))))))

(local-defthm converse-68
  (let* ((i (i-witness rho m n table))
         (j (j-witness rho m n table))
         (d (d-witness rho m n table))
         (p (p-witness rho m n table))
         (k (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (div-accessible-p i j m n)
                  (not (and (< (- (expt 2 rho)) k)
                            (< k (expt 2 rho)))))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< (abs p) d))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (d-witness p-witness div-accessible-p)
                                  (;jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4
                                   acl2::default-expt-2
                                   acl2::default-minus
                                   ;natp
                                   ;abs
                                   ))
           :use ((:instance converse-39 (i (i-witness rho m n table))
                                               (j (j-witness rho m n table)))
                        (:instance d4-p4-lemma
                                   (dmin (delta0 (j-witness rho m n table) n))
                                   (dmax (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                   (pmin (pi0 (i-witness rho m n table) m))
                                   (pmax (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                   (d1 (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                   (p1 (pi0 (i-witness rho m n table) m))
                                   (d2 (+ (delta0 (j-witness rho m n table) n) (expt 2 (- n))))
                                   (p2 (+ (pi0 (i-witness rho m n table) m) (expt 2 (- 3 m))))
                                   (hmin -1)
                                   (hmax 1))))))

(defthm lemma-2-2-converse
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (not (admissible-div-table-p rho m n table)))
             (let* ((i (i-witness rho m n table))
                    (j (j-witness rho m n table))
                    (p (p-witness rho m n table))
                    (d (d-witness rho m n table))
                    (k (lookup i j table)))
               (and (natp i)
                    (< i (expt 2 m))
                    (natp j)
                    (< j (expt 2 n))
                    (rationalp d)
                    (rationalp p)
                    (< (abs p) d)
                    (<= (delta0 j n) d)
                    (< d (+ (delta0 j n) (/ (expt 2 n))))
                    (<= (pi0 i m) p)
                    (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                    (or (<= k (- (expt 2 rho)))
                        (>= k (expt 2 rho))
                        (> (abs (- (* (expt 2 rho) p) (* d k))) d)))))
  :rule-classes ()
  :hints (("Goal"
           :use (div-witness-lemma converse-62 converse-67 converse-68)
           :in-theory (disable
                       jared-disables-1
                       jared-disables-2
                       jared-disables-3
                       jared-disables-4
                       acl2::default-expt-2
                       acl2::default-minus
                       )
           )))



;;**********************************************************************************

(defund srt-entry (i j rho m n)
  (max (- 1 (expt 2 rho))
       (lower i j rho m n)))

(defund srt-row (i j rho m n)
  (declare (xargs :measure (nfix (- (expt 2 n) j))))
  (if (and (natp j)
           (natp n)
           (< j (expt 2 n)))
      (cons (srt-entry i j rho m n)
            (srt-row i (1+ j) rho m n))
    ()))

(defund srt-rows (i rho m n)
  (declare (xargs :measure (nfix (- (expt 2 m) i))))
  (if (and (natp i)
           (natp m)
           (< i (expt 2 m)))
      (cons (srt-row i 0 rho m n)
            (srt-rows (1+ i) rho m n))
    ()))

(defund srt-table (rho m n)
  (srt-rows 0 rho m n))

(defthm admissible-div-table-p-2-5-2
  (admissible-div-table-p 2 5 2 (srt-table 2 5 2))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable srt-table admissible-div-table-p))))

(defthm admissible-div-table-p-3-7-3
  (admissible-div-table-p 3 7 3 (srt-table 3 7 3))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable srt-table admissible-div-table-p))))

(defund check-exists-div-entry (i j rho m n)
  (or (not (div-accessible-p i j m n))
      (<= (lower i j rho m n)
          (upper i j rho m n))))

(defund check-exists-div-row (i j rho m n)
  (if (zp j)
      t
    (and (check-exists-div-entry i (1- j) rho m n)
         (check-exists-div-row i (1- j) rho m n))))

(defund check-exists-div-rows (i rho m n)
  (if (zp i)
      t
    (and (check-exists-div-row (1- i) (expt 2 n) rho m n)
         (check-exists-div-rows (1- i) rho m n))))

(defund exists-div-table-p (rho m n)
  (check-exists-div-rows (expt 2 m) rho m n))

(local-defthm lemma-2-3-1
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (integerp (lower i j rho m n))
                (< (lower i j rho m n) (expt 2 rho))))
  :hints (("Goal" :in-theory (enable lower)))
  :rule-classes ())

(local-defthm lemma-2-3-2
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (integerp (srt-entry i j rho m n))
                (< (srt-entry i j rho m n) (expt 2 rho))
                (> (srt-entry i j rho m n) (- (expt 2 rho)))))
  :hints (("Goal" :in-theory (enable srt-entry)
                  :use lemma-2-3-1))
  :rule-classes ())

(local-defthm lemma-2-3-3
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (check-exists-div-entry i j rho m n))
           (check-div-entry i j rho m n (srt-entry i j rho m n)))
  :hints (("Goal"
           :in-theory (e/d (upper srt-entry check-exists-div-entry check-div-entry)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
           :use (lemma-2-3-1 lemma-2-3-2))))

(defun srt-row-induct (j k)
  (if (not (zp j))
      (1+ (srt-row-induct (1- j) (1+ k)))
    k))

(local-defthm lemma-2-3-4
  (implies (and (natp k)
                (natp j)
                (natp n)
                (< (+ k j) (expt 2 n)))
           (equal (nth j (srt-row i k rho m n))
                  (srt-entry i (+ k j) rho m n)))
  :hints (("Goal" :induct (srt-row-induct j k))
          ("Subgoal *1/2" :expand ((SRT-ROW I K RHO M N)))
          ("Subgoal *1/1" :expand ((SRT-ROW I K RHO M N)))))

(local-defthm lemma-2-3-5
  (implies (and (natp k)
                (natp i)
                (natp m)
                (< (+ k i) (expt 2 m)))
           (equal (nth i (srt-rows k rho m n))
                  (srt-row (+ k i) 0 rho m n)))
  :hints (("Goal" :induct (srt-row-induct i k))
          ("Subgoal *1/2" :expand ((SRT-ROWS K RHO M N)))
          ("Subgoal *1/1" :expand ((SRT-ROWS K RHO M N)))))

(local-defthm lemma-2-3-6
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (equal (nth j (nth i (srt-table rho m n)))
                  (srt-entry i j rho m n)))
  :hints (("Goal" :in-theory (enable srt-table))))

(local-defthm integerp-srt-entry
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (<= j (expt 2 n)))
           (integerp (srt-entry i j rho m n)))
  :hints (("Goal" :in-theory (enable lower srt-entry))))

(local-defthm lemma-2-3-7
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (<= j (expt 2 n))
                (check-exists-div-row i j rho m n))
           (check-div-row i j rho m n (nth i (srt-table rho m n))))
  :hints (("Goal" :in-theory (enable check-exists-div-row check-div-row))))

(local-defthm lemma-2-3-8
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (<= i (expt 2 m))
                (check-exists-div-rows i rho m n))
           (check-div-rows i rho m n (srt-table rho m n)))
  :hints (("Goal" :in-theory (enable check-exists-div-rows check-div-rows))))

(defthm lemma-2-3-a
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (exists-div-table-p rho m n))
           (admissible-div-table-p rho m n (srt-table rho m n)))
  :hints (("Goal" :in-theory (enable exists-div-table-p admissible-div-table-p))))

(local-defthm lemma-2-3-9
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (check-div-entry i j rho m n entry))
           (check-exists-div-entry i j rho m n))
  :hints (("Goal" :in-theory (e/d (upper check-exists-div-entry check-div-entry)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
                  :use (lemma-2-3-1 lemma-2-3-2))))

(local-defthm lemma-2-3-10
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (<= j (expt 2 n))
                (check-div-row i j rho m n row))
           (check-exists-div-row i j rho m n))
  :hints (("Goal" :in-theory (enable check-exists-div-row check-div-row))))

(local-defthm lemma-2-3-11
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (<= i (expt 2 m))
                (check-div-rows i rho m n rows))
           (check-exists-div-rows i rho m n))
  :hints (("Goal" :in-theory (enable check-exists-div-rows check-div-rows))))

(defthm lemma-2-3-b
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (admissible-div-table-p rho m n table))
           (exists-div-table-p rho m n))
  :hints (("Goal" :in-theory (enable exists-div-table-p admissible-div-table-p))))

;;**********************************************************************************

(local-defthm i-bounds-1
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (< (* (expt 2 (- m 2)) p)
              (expt 2 (1- m))))
  :rule-classes ())

(local-defthm i-bounds-2
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (<= x y)
                (< y z))
           (< x z))
:rule-classes ())

(local-defthm i-bounds-3
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (< (fl (* (expt 2 (- m 2)) p))
              (expt 2 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-1
                        (:instance i-bounds-2 (x (fl (* (expt 2 (- m 2)) p)))
                                             (y (* (expt 2 (- m 2)) p))
                                             (z (expt 2 (1- m))))
                        (:instance fl-def (x (* (expt 2 (- m 2)) p)))))))

(local-defthm i-bounds-4
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (bvecp (fl (* (expt 2 (- m 2)) p)) (1- m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
                  :use i-bounds-3)))

(local-defthm i-bounds-5
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (bvecp (fl (* (expt 2 (- m 2)) p)) m))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp-monotone)
                  :use i-bounds-4)))

(local-defthm i-bounds-6
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (equal (bits (FL (* p (EXPT 2 (+ -2 M)))) (+ -1 m) 0)
                  (FL (* (EXPT 2 (+ -2 M)) P))))
  :hints (("Goal" :use (i-bounds-5))))

(local-defthm i-bounds-7
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (equal (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m)
                  (/ (FL (* (EXPT 2 (+ -2 M)) P))
                     (expt 2 (- m 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0)
                  :use (i-bounds-3))))

(local-defthm i-bounds-8
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (<= x y))
           (<= (* x (expt 2 n))
               (* y (expt 2 n))))
  :rule-classes ())

(local-defthm i-bounds-9
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (<= (/ (FL (* (EXPT 2 (+ -2 M)) P)) (expt 2 (- m 2)))
               p))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (* (EXPT 2 (+ -2 M)) P)))
                        (:instance i-bounds-8 (x (FL (* (EXPT 2 (+ -2 M)) P)))
                                              (y (* (EXPT 2 (+ -2 M)) P))
                                              (n (- 2 m)))))))

(local-defthm i-bounds-10
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (< x y))
           (< (* x (expt 2 n))
              (* y (expt 2 n))))
  :rule-classes ())

(local-defthm i-bounds-11
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (< p
              (+ (/ (FL (* (EXPT 2 (+ -2 M)) P)) (expt 2 (- m 2)))
                 (expt 2 (- 2 m)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (* (EXPT 2 (+ -2 M)) P)))
                        (:instance i-bounds-10 (y (1+ (FL (* (EXPT 2 (+ -2 M)) P))))
                                               (x (* (EXPT 2 (+ -2 M)) P))
                                               (n (- 2 m)))))))

(local-defthm i-bounds-12
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (>= p 0))
           (and (<= (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m)
                    p)
                (< p
                   (+ (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m)
                      (expt 2 (- 2 m))))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-7 i-bounds-9 i-bounds-11))))

(local-defthm i-bounds-13
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (< p 0))
           (> (* (expt 2 (- m 2)) p)
              (- (expt 2 (1- m)))))
  :rule-classes ())

(local-defthm i-bounds-14
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (< p 0))
           (> (fl (* (expt 2 (- m 2)) p))
              (1- (* (expt 2 (- m 2)) p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (* (expt 2 (- m 2)) p)))))))

(local-defthm i-bounds-15
  (implies (and (rationalp x)
                (rationalp y)
                (< x y))
           (< (1- x) (1- y)))
  :rule-classes ())

(local-defthm i-bounds-16
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (< p 0))
           (> (1- (* (expt 2 (- m 2)) p))
              (1- (- (expt 2 (1- m))))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-13
                        (:instance i-bounds-15 (x (- (expt 2 (1- m)))) (y (* (expt 2 (- m 2)) p)))))))

(local-defthm i-bounds-17
  (implies (and (rationalp p)
                (< (abs p) 2)
                (natp m)
                (< p 0))
           (> (fl (* (expt 2 (- m 2)) p))
              (1- (- (expt 2 (1- m))))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-16
                        i-bounds-14))))

(local-defthm i-bounds-18
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (>= (fl (* (expt 2 (- m 2)) p))
               (- (expt 2 (1- m)))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-17))))

(local-defthm i-bounds-19
  (implies (not (zp m))
           (< (expt 2 (1- m))
              (expt 2 m)))
  :rule-classes ())

(local-defthm i-bounds-20
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (< x y)
                (<= y z))
           (< x z))
:rule-classes ())

(local-defthm i-bounds-21
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (>= (fl (* (expt 2 (- m 2)) p))
               (- (expt 2 m))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-18
                        i-bounds-19
                        (:instance i-bounds-20 (x (- (expt 2 m))) (y (- (expt 2 (1- m)))) (z (fl (* (expt 2 (- m 2)) p))))))))

(local-defthm i-bounds-22
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (equal (bits (FL (* p (EXPT 2 (+ -2 M)))) (+ -1 m) 0)
                  (+ (expt 2 m) (FL (* (EXPT 2 (+ -2 M)) P)))))
  :hints (("Goal" :use i-bounds-21)))

(local-defthm i-bounds-23
  (implies (and (integerp m)
                (rationalp x)
                (>= (+ x (expt 2 (1- m))) 0))
           (>= (+ (expt 2 (1- m)) (expt 2 (1- m)) x) (expt 2 (1- m))))
  :rule-classes ())

(local-defthm i-bounds-24
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (= (+ y y) z)
                (>= x (- y)))
           (>= (+ z x) y))
  :rule-classes ())

(local-defthm i-bounds-25
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (>= (bits (FL (* p (EXPT 2 (+ -2 M)))) (+ -1 m) 0)
               (expt 2 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance i-bounds-24 (x (FL (* p (EXPT 2 (+ -2 M)))))
                                               (y (expt 2 (1- m)))
                                               (z (expt 2 m)))
                        i-bounds-18))))

(local-defthm i-bounds-26
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (equal (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m)
                  (- (/ (bits (FL (* p (EXPT 2 (+ -2 M)))) (+ -1 m) 0)
                        (expt 2 (- m 2)))
                     4)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0)
                  :use (i-bounds-25))))

(local-defthm i-bounds-27
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (equal (* (expt 2 (- m 2))
                     (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m))
                  (FL (* p (EXPT 2 (+ -2 M))))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-26))))

(local-defthm i-bounds-28
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (<= (* (expt 2 (- m 2))
                  (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m))
               (* (EXPT 2 (+ -2 M))
                  p)))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-27
                        (:instance fl-def (x (* p (EXPT 2 (+ -2 M)))))))))

(local-defthm i-bounds-29
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (<= (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m)
               p))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-28))))


(local-defthm i-bounds-30
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (< (* (EXPT 2 (+ -2 M))
                 p)
              (+ (* (expt 2 (- m 2))
                    (pi0 (bits (FL (* (EXPT 2 (+ -2 M)) P)) (+ -1 m) 0) m))
                 1)))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-27
                        (:instance fl-def (x (* p (EXPT 2 (+ -2 M)))))))))

(local-defthm i-bounds-31
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (< x y))
           (< (* (expt 2 n) x) (* (expt 2 n) y)))
  :rule-classes ())

(local-defthm i-bounds-32
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m))
                (< p 0))
           (< p
              (+ (pi0 (bits (FL (* p (EXPT 2 (+ -2 M)))) (+ -1 m) 0) m)
                 (expt 2 (- 2 m)))))
  :rule-classes ()
  :hints (("Goal" :use (i-bounds-30
                        i-bounds-26
                        (:instance i-bounds-31 (x (* (EXPT 2 (+ -2 M)) p))
                                               (y (+ 1 (* (EXPT 2 (+ -2 M)) (pi0 (bits (FL (* p (EXPT 2 (+ -2 M)))) (+ -1 m) 0) m))))
                                               (n (- 2 m)))))))

(defthm i-bounds
  (implies (and (rationalp p)
                (< (abs p) 2)
                (not (zp m)))
           (let ((i (bits (fl (* (expt 2 (- m 2)) p)) (1- m) 0)))
              (and (bvecp i m)
                   (<= (pi0 i m) p)
                   (< p (+ (pi0 i m) (expt 2 (- 2 m)))))))
  :hints (("Goal" :use (i-bounds-32
                        i-bounds-29
                        i-bounds-12
                        (:instance bits-bvecp (x (fl (* (expt 2 (- m 2)) p))) (i (1- m)) (j 0) (k m)))
                  :in-theory (disable BITS-BVECP-SIMPLE bits-bvecp abs natp))))

(local-defthm j-bounds-1
  (implies (and (rationalp d)
                (natp n))
           (and (<= (fl (* (expt 2 n) (1- d))) (* (expt 2 n) (1- d)))
                (< (* (expt 2 n) (1- d)) (1+ (fl (* (expt 2 n) (1- d)))))))
  :rule-classes ())

(local-defthm j-bounds-2
  (implies (and (rationalp d)
                (natp n))
           (<= (/ (fl (* (expt 2 n) (1- d))) (expt 2 n)) (1- d)))
  :hints (("Goal" :use (j-bounds-1
                        (:instance i-bounds-8 (x (fl (* (expt 2 n) (1- d)))) (y (* (expt 2 n) (1- d))) (n (- n))))))
  :rule-classes ())

(local-defthm j-bounds-3
  (implies (and (rationalp d)
                (natp n))
           (<= (delta0 (fl (* (expt 2 n) (1- d))) n) d))
  :hints (("Goal" :use (j-bounds-2)
                  :in-theory (enable delta0)))
  :rule-classes ())

(local-defthm j-bounds-4
  (implies (and (rationalp d)
                (natp n))
           (< (1- d)
              (+ (expt 2 (- n)) (/ (fl (* (expt 2 n) (1- d))) (expt 2 n)))))
  :hints (("Goal" :use (j-bounds-1
                        (:instance i-bounds-10 (y (1+ (fl (* (expt 2 n) (1- d))))) (x (* (expt 2 n) (1- d))) (n (- n))))))
  :rule-classes ())

(local-defthm j-bounds-5
  (implies (and (rationalp d)
                (natp n))
           (< d (+ (expt 2 (- n)) (delta0 (fl (* (expt 2 n) (1- d))) n))))
  :hints (("Goal" :use (j-bounds-4)
                  :in-theory (enable delta0)))
  :rule-classes ())

(local-defthm j-bounds-6
  (implies (and (rationalp d)
                (natp n)
                (<= 0 d)
                (< d 1))
           (<= 0 (fl (* (expt 2 n) d))))
  :hints (("Goal" :use (:instance fl-def (x (* (expt 2 n) d)))))
  :rule-classes ())

(local-defthm j-bounds-7
  (implies (and (rationalp x)
                (rationalp y)
                (< x y))
           (< (fl x) y))
  :hints (("Goal" :use (fl-def)))
  :rule-classes ())

(local-defthm j-bounds-8
  (implies (and (rationalp d)
                (natp n)
                (<= 0 d)
                (< d 1))
           (< (fl (* (expt 2 n) d)) (expt 2 n)))
  :hints (("Goal" :use (:instance j-bounds-7 (x (* (expt 2 n) d)) (y (expt 2 n)))))
  :rule-classes ())

(defthm j-bounds
  (implies (and (rationalp d)
                (natp n)
                (<= 1 d)
                (< d 2))
           (let ((j (fl (* (expt 2 n) (1- d)))))
              (and (bvecp j n)
                   (<= (delta0 j n) d)
                   (< d (+ (delta0 j n) (expt 2 (- n)))))))
  :hints (("Goal" :use (j-bounds-3 j-bounds-5
                        (:instance j-bounds-6 (d (1- d)))
                        (:instance j-bounds-8 (d (1- d))))
                  :in-theory (enable bvecp)))
  :rule-classes ())


(encapsulate (((rho%) => *) ((m%) => *) ((n%) => *) ((table%) => *) ((d%) => *) ((x%) => *) ((j%) => *)
              ((p% *) => *) ((h% *) => *) ((i% *) => *))

(local (defun rho% () 2))
(local (defun m% () 5))
(local (defun n% () 2))
(local (defun table% () (srt-table 2 5 2)))
(local (defun d% () 1))
(local (defun x% () 0))
(local (defun j% () (fl (* (expt 2 (n%)) (1- (d%))))))

(local (mutual-recursion

(defun p% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 2)))
  (if (zp k)
      (x%)
    (- (* (expt 2 (rho%)) (p% (1- k)))
       (* (h% k) (d%)))))

(defun h% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 1)))
  (lookup (i% k) (j%) (table%)))

(defun i% (k)
  (declare (xargs :measure (* 3 (nfix k))))
  (if (zp k)
      ()
    (bits (fl (* (expt 2 (- (m%) 2)) (p% (1- k)))) (1- (m%)) 0)))
))

(defthmd rho%-constraint
  (not (zp (rho%))))

(defthmd m%-constraint
  (not (zp (m%))))

(defthmd n%-constraint
  (not (zp (n%))))

(defthmd table%-constraint
  (admissible-div-table-p (rho%) (m%) (n%) (table%)))

(defthmd d%-constraint
  (and (rationalp (d%))
       (<= 1 (d%))
       (< (d%) 2)))

(defthmd x%-constraint
  (and (rationalp (x%))
       (< (abs (x%)) (d%))))

(defthmd p%-def
  (equal (p% k)
         (if (zp k)
             (x%)
           (- (* (expt 2 (rho%)) (p% (1- k)))
              (* (h% k) (d%)))))
  :rule-classes (:definition))

(defthmd h%-def
  (equal (h% k)
         (lookup (i% k) (j%) (table%)))
  :rule-classes (:definition))

(defthmd i%-constraint
  (implies (and (not (zp k))
                (rationalp (p% (1- k)))
                (< (abs (p% (1- k))) 2))
           (and (bvecp (i% k) (m%))
                (<= (pi0 (i% k) (m%))
                    (p% (1- k)))
                (< (p% (1- k))
                   (+ (pi0 (i% k) (m%))
                      (/ (expt 2 (- (m%) 3)))))))
  :hints (("Goal" :in-theory (disable bits-tail-gen)
           :use ((:instance i-bounds (p (p% (1- k))) (m (m%)))))))

(defthmd j%-constraint
  (and (bvecp (j%) (n%))
       (<= (delta0 (j%) (n%)) (d%))
       (< (d%) (+ (delta0 (j%) (n%)) (expt 2 (- (n%))))))
  :hints (("Goal" :use ((:instance j-bounds (d (d%)) (n (n%)))))))

)

(defund q% (k)
  (if (zp k)
      0
    (+ (q% (1- k))
       (/ (h% k) (expt 2 (* k (rho%)))))))

(local-defthm theorem-1-1
  (implies (and (not (zp k))
                (rationalp (p% (1- k)))
                (<= (- (d%)) (p% (1- k)))
                (< (p% (1- k)) (d%)))
           (and (integerp (h% k))
                (rationalp (p% k))
                (<= (- (d%)) (p% k))
                (< (p% k) (d%))))
  :rule-classes ()
  :hints (("Goal" :use (rho%-constraint
                        d%-constraint
                        i%-constraint
                        j%-constraint
                        m%-constraint
                        n%-constraint
                        table%-constraint
                        (:instance lemma-2-2 (m (m%)) (n (n%)) (rho (rho%)) (table (table%)) (d (d%)) (p (p% (1- k))) (i (i% k))
                                             (j (j%)) (k (h% k))))
                  :in-theory (e/d (p%-def h%-def bvecp)
                                  (jared-disables-1
                                       jared-disables-2
                                       jared-disables-3
                                       jared-disables-4))
                  )))

(local-defthm theorem-1-2
  (implies (zp k)
           (and (rationalp (p% k))
                (<= (- (d%)) (p% k))
                (< (p% k) (d%))))
  :rule-classes ()
  :hints (("Goal" :use (x%-constraint p%-def))))

(local-defthm theorem-1-3
  (and (rationalp (p% k))
       (<= (- (d%)) (p% k))
       (< (p% k) (d%))
       (implies (not (zp k))
                (integerp (h% k))))
  :rule-classes ()
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/2" :use theorem-1-1)
          ("Subgoal *1/1" :use theorem-1-2)))

(local-defthm theorem-1-4
  (implies (not (zp k))
           (integerp (h% k)))
  :hints (("Goal" :use (theorem-1-3))))

(local-defthm theorem-1-5
  (rationalp (p% k))
  :hints (("Goal" :use (theorem-1-3))))

(local-defthm theorem-1-6
  (and (<= (- (d%)) (p% k))
       (< (p% k) (d%)))
  :hints (("Goal" :use (theorem-1-3))))

(local-defthm theorem-1-7
  (> (d%) 0)
  :hints (("Goal" :use (d%-constraint))))

(local-defthm theorem-1-8
  (integerp (rho%))
  :hints (("Goal" :use (rho%-constraint))))

(defthm theorem-1-a
  (implies (natp k)
           (and (<= (- (/ (expt 2 (* k (rho%)))))
                    (- (/ (x%) (d%)) (q% k)))
                (< (- (/ (x%) (d%)) (q% k))
                   (/ (expt 2 (* k (rho%)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p%-def q% rho%-constraint x%-constraint d%-constraint)
                  :use ((:functional-instance lemma-2-1-corollary
                                              (rho$ rho%)
                                              (x$ x%)
                                              (d$ d%)
                                              (h$ h%)
                                              (p$ p%)
                                              (q$ q%))))))

(defthm theorem-1-b
  (< (abs (p% k)) 2)
  :rule-classes ()
  :hints (("Goal" :in-theory (disable theorem-1-6)
                  :use (d%-constraint theorem-1-6))))

(defthm theorem-1-c
  (implies (not (zp k))
           (div-accessible-p (i% k) (j%) (m%) (n%)))
  :rule-classes ()
  :hints (("Goal" :use (m%-constraint
                        n%-constraint
                        d%-constraint
                        i%-constraint
                        j%-constraint
                        (:instance theorem-1-b (k (1- k)))
                        (:instance theorem-1-3 (k (1- k)))
                        (:instance theorem-1-6 (k (1- k)))
                        (:instance div-table-1 (m (m%)) (n (n%)) (i (i% k)) (j (j%)) (p (p% (1- k))) (d (d%)))))))

