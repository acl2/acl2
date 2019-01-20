; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Micro Devices, Inc.
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

(set-enforce-redundancy t)

(local (include-book "support/srt"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From bits.lisp:

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))


;;**********************************************************************************
;; Formula for Division Partial Remainder
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

(defthmd div-remainder-formula
  (implies (natp k)
           (equal (p$ k)
                  (* (expt 2 (* k (rho$)))
                     (- (x$) (* (q$ k) (d$)))))))

(defthm div-remainder-formula-corollary
  (implies (and (natp k)
                (<= (- (d$)) (p$ k))
                (< (p$ k) (d$)))
           (and (<= (- (/ (expt 2 (* k (rho$)))))
                    (- (/ (x$) (d$)) (q$ k)))
                (< (- (/ (x$) (d$)) (q$ k))
                   (/ (expt 2 (* k (rho$)))))))
  :rule-classes ())


;;**********************************************************************************
;; admissible-div-table-p
;;**********************************************************************************

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

;;**********************************************************************************
;; First we prove that the definition of admissibility ensures the desired property.
;;**********************************************************************************

(defthm admissible-div-table-criterion
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
  :rule-classes ())


;;**********************************************************************************
;; Next we prove the converse of the above. This requires that we define witness
;; functions that produce a violation of the desired property for a given table that
;; fails to satisfy the definition.
;;**********************************************************************************

;; Assume that dmin < dmax and pmin < pmax.  Consider the closed rectangle
;;   R = {(d,p) | dmin <= d <= dmax and pmin <= p <= pmax}
;; and the halh-open rectangle
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
;; in R' with p1 > h*d1:

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
;; and entry = (nth j (nth i table)
;; Then 0 <= i < 2^m, 0 <= j < 2^n, and
;; (check-div-entry i j rho m n entry) = NIL.
;; Let d = (d-witness rho m n table) and p = (p-witness rho m n table).
;; If -2^rho < entry < 2^rho, then (d,p) is in S_ij, |p| <= d, and
;;   |2^rho * p - entry * d| > d:

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

(defthm admissible-div-table-criterion-converse
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
  :rule-classes ())

;;**********************************************************************************
;; Existence of SRT Table for Division
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
  :rule-classes ())

(defthm admissible-div-table-p-3-7-3
  (admissible-div-table-p 3 7 3 (srt-table 3 7 3))
  :rule-classes ())

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

(defthm div-table-existence-a
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (exists-div-table-p rho m n))
           (admissible-div-table-p rho m n (srt-table rho m n))))

(defthm div-table-existence-b
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (admissible-div-table-p rho m n table))
           (exists-div-table-p rho m n)))


;;**********************************************************************************
;; Main Theorem on Division
;;**********************************************************************************

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
  :hints (("Goal"  :in-theory (disable bits-tail-gen)
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

(defthm srt-div-theorem-a
  (implies (natp k)
           (and (<= (- (/ (expt 2 (* k (rho%)))))
                    (- (/ (x%) (d%)) (q% k)))
                (< (- (/ (x%) (d%)) (q% k))
                   (/ (expt 2 (* k (rho%)))))))
  :rule-classes ())

(defthm srt-div-theorem-b
  (< (abs (p% k)) 2)
  :rule-classes ())

(defthm srt-div-theorem-c
  (implies (not (zp k))
           (div-accessible-p (i% k) (j%) (m%) (n%)))
  :rule-classes ())


;;**********************************************************************************
;; Formula for Square Root Partial Remainder
;;**********************************************************************************

(encapsulate (((rho$$) => *) ((x$$) => *) ((h$$ *) => *))
  (local (defun rho$$ () 1))
  (local (defun x$$ () 0))
  (local (defun h$$ (k) (declare (ignore k)) 0))
  (defthm rho$$-constraint
    (integerp (rho$$))
    :rule-classes (:rewrite :type-prescription))
  (defthm x$$-constraint
    (rationalp (x$$))
    :rule-classes (:rewrite :type-prescription))
  (defthm integerp-h$$
    (implies (not (zp k))
             (integerp (h$$ k)))
    :rule-classes (:rewrite :type-prescription)))

(defund q$$ (k)
  (if (zp k)
      0
    (+ (q$$ (1- k))
       (/ (h$$ k) (expt 2 (* k (rho$$)))))))

(defund p$$ (k)
  (if (zp k)
      (x$$)
    (- (* (expt 2 (rho$$)) (p$$ (1- k)))
       (* (h$$ k)
          (+ (* 2 (q$$ (1- k)))
             (/ (h$$ k) (expt 2 (* k (rho$$)))))))))

(defthmd sqrt-remainder-formula
  (implies (natp k)
           (equal (p$$ k)
                  (* (expt 2 (* k (rho$$)))
                     (- (x$$) (* (q$$ k) (q$$ k)))))))

;;**********************************************************************************
;; Equivalent Bounds on Partial Remainder
;;**********************************************************************************

(defthm equiv-bounds-a-b
  (implies (not (zp k))
           (iff (and (<= (* (- (q$$ k) (expt 2 (- (* k (rho$$))))) (- (q$$ k) (expt 2 (- (* k (rho$$))))))
                         (x$$))
                     (< (x$$)
                        (* (+ (q$$ k) (expt 2 (- (* k (rho$$))))) (+ (q$$ k) (expt 2 (- (* k (rho$$))))))))
                (and (<= (- (* 2 (q$$ k)))
                         (- (p$$ k) (expt 2 (- (* k (rho$$))))))
                     (< (- (p$$ k) (expt 2 (- (* k (rho$$)))))
                        (* 2 (q$$ k))))))
  :rule-classes ())

(defthm equiv-bounds-b-c
  (implies (not (zp k))
           (iff (and (<= (- (* 2 (q$$ k)))
                         (- (p$$ k) (expt 2 (- (* k (rho$$))))))
                     (< (- (p$$ k) (expt 2 (- (* k (rho$$)))))
                        (* 2 (q$$ k))))
                (and (<= (* (expt 2 (- (rho$$)))
                            (1- (h$$ k))
                            (+ (* 2 (q$$ (1- k)))
                               (* (1- (h$$ k)) (expt 2 (- (* k (rho$$)))))))
                         (p$$ (1- k)))
                     (< (p$$ (1- k))
                        (* (expt 2 (- (rho$$)))
                           (1+ (h$$ k))
                           (+ (* 2 (q$$ (1- k)))
                              (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$)))))))))))
  :rule-classes ())


;;**********************************************************************************
;; Lemma 3.3
;;**********************************************************************************

(defthm sqrt-partial-remainder-bounds
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (<= (* (- (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))) (- (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))))
                    (x$$))
                (< (x$$)
                   (* (+ (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))) (+ (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))))))
           (< (abs (p$$ (1- k))) 2))
  :rule-classes())

(defthm partial-root-bounds
  (implies (and (not (zp (rho$$)))
                (> (x$$) 1/4)
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (< (h$$ k) (expt 2 (rho$$)))
                (> (h$$ k) (- (expt 2 (rho$$))))
                (<= (x$$) (* (+ (q$$ k) (expt 2 (- (* k (rho$$)))))
                             (+ (q$$ k) (expt 2 (- (* k (rho$$))))))))
           (and (<= 1/2 (q$$ k))
                (< (q$$ k) 1)))
  :rule-classes())


;;**********************************************************************************
;; admissible-for-iteration-p
;;**********************************************************************************

(defund sqrt-accessible-p (i j k rho m n)
  (and (< (- (expt 2 (* (- 1 k) rho)) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
          (pi0 i m))
       (< (pi0 i m)
          (+ (delta0 j n) (/ (expt 2 n)) (expt 2 (* (- 1 k) rho))))))

(defund check-upper-bound (entry i j k rho m n)
  (or (= entry (1- (expt 2 rho)))
      (<= (+ (pi0 i m) (expt 2 (- 3 m)))
          (if (or (< i (expt 2 (1- m)))
                  (= i (1- (expt 2 m))))
              (* (/ (1+ entry) (expt 2 rho))
                 (+ (delta0 j n) (* (1+ entry) (expt 2 (- (* k rho))))))
            (* (/ (1+ entry) (expt 2 rho))
               (+ (delta0 j n) (expt 2 (- n)) (* (1+ entry) (expt 2 (- (* k rho))))))))))

(defund check-lower-bound (entry i j k rho m n)
  (or (= entry (- 1 (expt 2 rho)))
      (>= (pi0 i m)
          (if (< i (expt 2 (1- m)))
              (* (/ (1- entry) (expt 2 rho))
                 (+ (delta0 j n) (expt 2 (- n)) (* (1- entry) (expt 2 (- (* k rho))))))
            (* (/ (1- entry) (expt 2 rho))
               (+ (delta0 j n) (* (1- entry) (expt 2 (- (* k rho))))))))))

(defund check-sqrt-entry (i j k rho m n entry)
  (or (not (sqrt-accessible-p i j k rho m n))
      (and (< (- (expt 2 rho)) entry)
           (< entry (expt 2 rho))
           (check-upper-bound entry i j k rho m n)
           (check-lower-bound entry i j k rho m n))))

(defund check-sqrt-row (i j k rho m n row)
  (if (zp j)
      t
    (and (check-sqrt-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
         (check-sqrt-row i (1- j) k rho m n row))))

(defund check-sqrt-rows (i k rho m n rows)
  (if (zp i)
      t
    (and (check-sqrt-row (1- i) (expt 2 n) k rho m n (nth (1- i) rows))
         (check-sqrt-rows (1- i) k rho m n rows))))

(defund admissible-for-iteration-p (k rho m n table)
  (check-sqrt-rows (expt 2 m) k rho m n table))

;;**********************************************************************************
;; First we prove that the definition of admissibility ensures the desired property.
;;**********************************************************************************

(defthm admissible-sqrt-table-criterion
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (not (zp k))
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
          (and (< h (expt 2 rho))
               (> h (- (expt 2 rho)))
               (< p
                 (* (/ (1+ h) (expt 2 rho))
                    (+ d (* (1+ h) (expt 2 (- (* k rho)))))))
               (>= p
                  (* (/ (1- h) (expt 2 rho))
                     (+ d (* (1- h) (expt 2 (- (* k rho)))))))))
  :rule-classes ())

;;**********************************************************************************
;; Next we prove the converse of the above. This requires that we define witness
;; functions that produce a violation of the desired property for a given table that
;; fails to satisfy the definition for a given k.
;;**********************************************************************************

;; Assume that dmin < dmax and pmin < pmax.  Consider the closed rectangle
;;   R = {(d,p) | dmin <= d <= dmax and pmin <= p <= pmax},
;; the half-closed rectangle
;;   R' = {(d,p) | dmin <= d < dmax and pmin <= p < pmax},
;; and the quarter-closed rectangle
;;   R" = {(d,p) | dmin < d < dmax and pmin <= p < pmax}.
;; If there exists (d,p) in R such that p < h*d + b, then (d5,p5) is a point
;; in R" with p5 < h*d5 + b:

(defund d5 (dmin pmin dmax pmax h b)
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h))))
    ;; (d1,p1) is in R' and p1 < h*d1 + b.
    (if (> d1 dmin)
        d1
      (if (>= (+ (* h dmax) b) p1)
          (/ (+ dmin dmax) 2)
        (/ (+ (/ (- p1 b) h) dmin) 2)))))

(defund p5 (dmin pmin dmax pmax h b)
  (+ b (p1 dmin (- pmin b) dmax (- pmax b) h)))

;; If there exists (d,p) in R such that p > h*d + b, then (d6,p6) is a point
;; in R" with p6 > h*d6 + b:

(defund d6 (dmin pmin dmax pmax h b)
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h))))
    ;; (d2,p2) is in R' and p2 > h*d2 + b.
    (if (> d2 dmin)
        d2
      (if (>= p2 (+ (* h dmax) b))
          (/ (+ dmin dmax) 2)
        (/ (+ (/ (- p2 b) h) dmin) 2)))))

(defund p6 (dmin pmin dmax pmax h b)
  (+ b (p2 dmin (- pmin b) dmax (- pmax b) h)))

;; Assume h2 < h1 and h2 + b2 <= h1 + b1.  Then for all d > 1,
;
;;   (h1*d + b1) - (h2*d + b2) = (h1 - h2)*d + (b1 - b2)
;;                             > (h1 - h2) + (b1 - b2)
;;                             >= 0.
;;
;; Assume dmin >= 1.  If there exist (d1,p1) and (d2,p2) in R such that
;; p1 < h1*d1 + b1 and p2 > h2*d2 + b2, then (d7,p7) is in R" and
;; h2*d7 + b2 < p7 < h1*d7 + b1:

(defund d7 (dmin pmin dmax pmax h1 b1 h2 b2)
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2)))
    (if (> p5 (+ (* h2 d5) b2))
        d5
      (if (< p6 (+ (* h1 d6) b1))
          d6
        (if (<= p5 (+ (* h2 d6) b2))
            d6
          (if (>= p5 (+ (* h1 d6) b1))
              (/ (+ (/ (- p5 b1) h1) (/ (- p5 b2) h2)) 2)
            d6))))))

(defund p7 (dmin pmin dmax pmax h1 b1 h2 b2)
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2)))
    (if (> p5 (+ (* h2 d5) b2))
        p5
      (if (< p6 (+ (* h1 d6) b1))
          p6
        (if (<= p5 (+ (* h2 d6) b2))
            (/ (+ (* (+ h1 h2) d6) b1 b2) 2)
          p5)))))

;; We have p5 < h1*d5 + b1 and p6 > h2*d6 + b2.
;; The claim is proved by the following case analysis:

;; Case 1: p5 > h2*d5 + b2.
;;   (d7,p7) = (d5,p5).
;;   h2*d7 + b2 = h2*d5 + b2  < p5 = p7 < h1*d7 + b1.

;; Case 2: p6 < h1*d6 + b1.
;;   (d7,p7) = (d6,p6).
;;   h2*d7 + b2 = h2*d6 + b2 < p6 = p7 < h1*d6 + b1.

;; Case 3: p6 >= h1*d6 + b1, p5 <= h2*d6 + b2.
;;   (d7,p7) = (d6,((h1+h2)*d6+b1+b1)/2).
;;   Let y1 = h1*d6 + b1 and y2 = h2*d6 + b2.  Then p7 = (y1+y2)/2 and
;;   h2*d7 + b2 = h2*d6 + b2 < h1*d6 + b1 = h1*d7 + b1.
;;   Since p5 <= y2 < y1 <= p6, pmin < p5 < p7 < p6 < pmax.

;; Case 4: p5 <= h2*d5 + b2, p5 > h2*d6 + b2, p5 >= h1*d6 + b1.
;;   (d7,p7) = ((x1+x2)/2,p5), where x1 = (p5-b1)/h1 and x2 = (p5-b2)/h2.
;;   Since h2*d6 + b2 < p5 <= h2*d5 + b2, h2*(d5 - d6) > 0.

;;   Case 4a: d5 > d6.
;;     h1 > h2 > 0.
;;     Since h2*d6 + b2 < p5 <= h2*d5 + b2, d6 < (p5-b2)/h2 = x2 < d5.
;;     Since p5 >= h1*d6 + b1, x1 = (p5-b1)/h1 >= d6.
;;     Since h1*(x2 - x1) = h1*x2 - p5 + b1
;;                        = h1*x2 - (h2*x2 + b2) + b1
;;                        = (h1*x2 + b1) - (h2*x2 + b2)
;;                        > 0,
;;     x2 > x1.
;;     Thus, dmin < d6 <= x1 < x2 < d5 < dmax and
;;     (p5-b1)/h1 = x1 < d7 < x2 = (p5-b2)/h2, which implies
;;     h2*d7 + b2 < p5 < h1*d7 + b1.

;;   Case 4b: d5 < d6.
;;     h2 < 0 and d5 <= (p5-b2)/h2 = x2 < d6.
;;     Since h1*d5 + b1 > h2*d5 + b2 >= p5 >= h1*d6 + b1,
;;     h1*(d6 - d5) < 0, which implies h1 < 0.
;;     Since p5 >= h1*d6 + b1, x1 = (p5-b1)/h1 <= d6.
;;     Since p5 <= h2*d5 + b2 < h1*d5 + b1, (p5-b1)/h1 > d5 > 1.
;;     Since h2*(x1-x2) = h2*x1 - p5 + b2
;;                      = h2*x1 - (h2*x1 + b2) + b1
;;                      = (h2*x1 + b1) - (h2*x1 + b2)
;;                      < 0,
;;     x1 > x2.
;;     Thus, dmin < d5 <= x2 < x1 <= d6 < dmax and
;;     (p5-b2)/h2 = x2 < d7 < x1 = (p5-b1)/h1, which implies
;;     h2*d7 + b2 < p5 < h1*d7 + b1.

;;   Case 5: p5 > h2*d6 + b2, p5 < h1*d6 + b1.
;;     (d7,p7) = (d6,p5).
;;     h2*d7 + b2 = h2*d6 + b2 > p5 = p7 < h1*d7 + b1 = h1*d6 + b1.


;; Suppose that (admissible-for-iteration-p k rho m n table) = NIL.
;; Let i = (i-sqrt k rho m n table), j = (j-sqrt k rho m n table),
;; and h = (lookup i j table).
;; Then 0 <= i < 2^m, 0 <= j < 2^n, and
;; (check-sqrt-entry i j k rho m n h) = NIL.
;; Let d = (d-sqrt k rho m n table) and p = (p-sqrt k rho m n table).
;; Then (d,p) is in S_ij and |p - 2^((1-k)*rho)| < d.
;; If -2^rho < h < 2^rho, then either
;;   p < ((h-1)/2^rho)*(d + (h-1)2^(-k*rho))
;; or
;;   p > ((h+1)/2^rho)*(d + (h+1)2^(-k*rho)).

(defund i-sqrt-aux (i k rho m n table)
  (if (zp i)
      ()
    (if (check-sqrt-row (1- i) (expt 2 n) k rho m n (nth (1- i) table))
        (i-sqrt-aux (1- i) k rho m n table)
      (1- i))))

(defund i-sqrt (k rho m n table)
  (i-sqrt-aux (expt 2 m) k rho m n table))

(defund j-sqrt-aux (i j k rho m n row)
  (if (zp j)
      ()
    (if (check-sqrt-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
        (j-sqrt-aux i (1- j) k rho m n row)
      (1- j))))

(defund j-sqrt (k rho m n table)
  (let ((i (i-sqrt k rho m n table)))
    (j-sqrt-aux i (expt 2 n) k rho m n (nth i table))))

(defund d-sqrt (k rho m n table)
  (let* ((i (i-sqrt k rho m n table))
         (j (j-sqrt k rho m n table))
         (h (lookup i j table)))
    (if (or (not (integerp h))
            (>= h (expt 2 rho))
            (<= h (- (expt 2 rho))))
        (d7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            1
            (expt 2 (* (- 1 k) rho))
            -1
            (expt 2 (* (- 1 k) rho)))
      (if (not (check-upper-bound h i j k rho m n))
          (d7 (delta0 j n)
              (pi0 i m)
              (+ (delta0 j n) (expt 2 (- n)))
              (+ (pi0 i m) (expt 2 (- 3 m)))
              1
              (expt 2 (* (- 1 k) rho))
              (/ (1+ h) (expt 2 rho))
              (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
        (d7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            (/ (1- h) (expt 2 rho))
            (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
            -1
            (expt 2 (* (- 1 k) rho)))))))

(defund p-sqrt (k rho m n table)
  (let* ((i (i-sqrt k rho m n table))
         (j (j-sqrt k rho m n table))
         (h (lookup i j table)))
    (if (or (not (integerp h))
            (>= h (expt 2 rho))
            (<= h (- (expt 2 rho))))
        (p7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            1
            (expt 2 (* (- 1 k) rho))
            -1
            (expt 2 (* (- 1 k) rho)))
      (if (not (check-upper-bound h i j k rho m n))
          (p7 (delta0 j n)
              (pi0 i m)
              (+ (delta0 j n) (expt 2 (- n)))
              (+ (pi0 i m) (expt 2 (- 3 m)))
              1
              (expt 2 (* (- 1 k) rho))
              (/ (1+ h) (expt 2 rho))
              (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
        (p7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            (/ (1- h) (expt 2 rho))
            (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
            -1
            (expt 2 (* (- 1 k) rho)))))))

(defthm admissible-sqrt-table-criterion-converse
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (h (lookup i j table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (/ (expt 2 n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                  (< (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                  (or (<= h (- (expt 2 rho)))
                      (>= h (expt 2 rho))
                      (< p (* (/ (1- h) (expt 2 rho))
                              (+ d (* (1- h) (expt 2 (- (* k rho)))))))
                      (> p (* (/ (1+ h) (expt 2 rho))
                              (+ d (* (1+ h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ())


;;**********************************************************************************
;; Main Theorem on Square Root
;;**********************************************************************************

(defthm admissible-for-iteration-p-2-2-6-2
  (implies (and (natp k)
                (> k 2))
           (admissible-for-iteration-p k 2 6 2 (srt-table 2 6 2))))

(encapsulate (((rho%%) => *) ((m%%) => *) ((n%%) => *) ((k%%) => *) ((table%%) => *))

(local (defun rho%% () 2))
(local (defun m%% () 6))
(local (defun n%% () 2))
(local (defun k%% () 2))
(local (defun table%% () (srt-table 2 6 2)))

(defthmd rho%%-constraint
  (not (zp (rho%%))))

(defthmd m%%-constraint
  (not (zp (m%%))))

(defthmd n%%-constraint
  (not (zp (n%%))))

(defthmd k%%-constraint
  (and (natp (k%%)) (> (k%%) 1)))

(defthm table%%-constraint
  (implies (and (natp k)
                (> k (k%%)))
           (admissible-for-iteration-p k (rho%%) (m%%) (n%%) (table%%)))
  :hints (("Goal" :in-theory (disable srt-table (table%%) (srt-table)))))

)

(encapsulate (((x%%) => *) ((p%% *) => *) ((q%% *) => *) ((h%% *) => *) ((i%% *) => *) ((j%% *) => *))

(local (defun x%% () 1/2))

(local (mutual-recursion

(defun p%% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 2)))
  (if (zp k)
      (x%%)
    (- (* (expt 2 (rho%%)) (p%% (1- k)))
       (* (h%% k) (+ (* 2 (q%% (1- k))) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))))

(defun q%% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 2)))
  (if (zp k)
      0
    (+ (q%% (1- k)) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))

(defun h%% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 1)))
  (lookup (i%% k) (j%% k) (table%%)))

(defun i%% (k)
  (declare (xargs :measure (* 3 (nfix k))))
  (if (zp k)
      ()
    (bits (fl (* (expt 2 (- (m%%) 2)) (p%% (1- k)))) (1- (m%%)) 0)))

(defun j%% (k)
  (declare (xargs :measure (* 3 (nfix k))))
  (if (zp k)
      ()
    (fl (* (expt 2 (n%%)) (1- (* 2 (q%% (1- k))))))))

))

(defthmd x%%-constraint
  (and (rationalp (x%%))
       (< 1/4 (x%%))
       (< (x%%) 1)))

(defthm p%%-def
  (equal (p%% k)
         (if (zp k)
             (x%%)
           (- (* (expt 2 (rho%%)) (p%% (1- k)))
              (* (h%% k) (+ (* 2 (q%% (1- k))) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))))
  :rule-classes (:definition))

(defthm q%%-def
  (equal (q%% k)
         (if (zp k)
             0
           (+ (q%% (1- k)) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))
  :rule-classes (:definition))

(defthm integerp-h%%
  (integerp (h%% k))
  :rule-classes (:rewrite :type-prescription))

(defthmd h%%-def
  (implies (and (natp k)
                (> k (k%%)))
           (equal (h%% k)
                  (lookup (i%% k) (j%% k) (table%%))))
  :rule-classes (:definition))

(defun all-sqrt-accessible-p%% (k)
  (if (or (zp k) (<= k (k%%)))
      t
    (and (sqrt-accessible-p (i%% k) (j%% k) k (rho%%) (m%%) (n%%))
         (all-sqrt-accessible-p%% (1- k)))))

(defthmd i%%-constraint
  (implies (and (natp k)
                (> k (k%%))
                (rationalp (p%% (1- k)))
                (< (abs (p%% (1- k))) 2)
                (all-sqrt-accessible-p%% (1- k)))
           (and (bvecp (i%% k) (m%%))
                (<= (pi0 (i%% k) (m%%))
                    (p%% (1- k)))
                (< (p%% (1- k))
                   (+ (pi0 (i%% k) (m%%))
                      (/ (expt 2 (- (m%%) 3)))))))
  :hints (("Goal" :use (m%%-constraint
                        k%%-constraint
                        (:instance i-bounds (p (p%% (1- k))) (m (m%%)))
                        (:instance local-lemma (x (P%% (+ -1 K)))
                                               (y1 (EXPT 2 (+ 2 (- (M%%)))))
                                               (y2 (EXPT 2 (+ 3 (- (M%%)))))
                                               (z (pi0 (i%% k) (m%%))))))))

(defthmd j%%-constraint
  (implies (and (natp k)
                (> k (k%%))
                (rationalp (q%% (1- k)))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1))
           (and (bvecp (j%% k) (n%%))
                (<= (delta0 (j%% k) (n%%)) (* 2 (q%% (1- k))))
                (< (* 2 (q%% (1- k))) (+ (delta0 (j%% k) (n%%)) (expt 2 (- (n%%)))))))
  :hints (("Goal" :use (n%%-constraint (:instance j-bounds (d (* 2 (q%% (1- k)))) (n (n%%)))))))

)

(defthm srt-sqrt-theorem-a
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                            (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (>= k (k%%)))
           (and (< (x%%) (* (+ (q%% k) (expt 2 (- (* k (rho%%)))))
                            (+ (q%% k) (expt 2 (- (* k (rho%%)))))))
                (>= (x%%) (* (- (q%% k) (expt 2 (- (* k (rho%%)))))
                             (- (q%% k) (expt 2 (- (* k (rho%%)))))))))
  :rule-classes ())

(defthm srt-sqrt-theorem-b
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (>= k (k%%)))
           (< (abs (p%% k)) 2))
  :rule-classes ())

(defthmd srt-sqrt-theorem-c
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                            (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (> k (k%%)))
           (sqrt-accessible-p (i%% k) (j%% k) k (rho%%) (m%%) (n%%))))


;;**********************************************************************************
;; An Admissible Square Root Table is Also an Admissible Division Table
;;**********************************************************************************

(defthm sqrt-table-is-div-table
  (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%))
  :rule-classes ())

;;**********************************************************************************
;; Admissible SRT Tables
;;**********************************************************************************

(defund accessible-p (i j k rho m n)
  (and (< (- (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
          (pi0 i m))
       (< (pi0 i m)
          (+ (delta0 j n) (/ (expt 2 n)) (expt 2 (- (* k rho)))))))

(defthm div-accessible-accessible
  (implies (and (integerp m)
                (integerp n)
                (integerp rho)
                (integerp k)
                (integerp i)
                (integerp j)
                (div-accessible-p i j m n))
           (accessible-p i j k rho m n)))

(defthm sqrt-accessible-accessible
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (bvecp i m)
                (bvecp j n)
                (natp k1)
                (> k1 k)
                (sqrt-accessible-p i j k1 rho m n))
           (accessible-p i j k rho m n))
  :rule-classes ())

(defund check-entry (i j k rho m n entry)
  (or (not (accessible-p i j k rho m n))
      (and (< (- (expt 2 rho)) entry)
           (< entry (expt 2 rho))
           (>= entry (lower i j rho m n))
           (check-lower-bound entry i j (1+ k) rho m n))))

(defund check-row (i j k rho m n row)
  (if (zp j)
      t
    (and (check-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
         (check-row i (1- j) k rho m n row))))

(defund check-rows (i k rho m n rows)
  (if (zp i)
      t
    (and (check-row (1- i) (expt 2 n) k rho m n (nth (1- i) rows))
         (check-rows (1- i) k rho m n rows))))

(defund admissible-srt-table-p (k rho m n table)
  (check-rows (expt 2 m) k rho m n table))

;;**********************************************************************************
;; Equivalence of Admissibility Definitions
;;**********************************************************************************

(defthm admissibility-equivalence-a
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp k1)
                (> k1 k)
                (admissible-srt-table-p k rho m n table))
           (admissible-for-iteration-p k1 rho m n table))
  :rule-classes ())

(encapsulate (((xtable%%) => *))

(local (defund xtable-entry (i j)
  (if (and (> (pi0 i (m%%))
              (- (+ (delta0 j (n%%))
                    (expt 2 (- (n%%)))
                    (expt 2 (- 3 (m%%))))))
           (<= (pi0 i (m%%))
               (- (expt 2 (- (* (k%%) (rho%%))))
                  (+ (delta0 j (n%%))
                     (expt 2 (- (n%%)))
                     (expt 2 (- 3 (m%%)))))))
      (- 1 (expt 2 (rho%%)))
    (lookup i j (table%%)))))

(local (defun xtable-row (i j)
  (declare (xargs :measure (nfix (- (expt 2 (n%%)) j))))
  (if (and (natp j)
           (< j (expt 2 (n%%))))
      (cons (xtable-entry i j)
            (xtable-row i (1+ j)))
    ())))

(local (defun xtable-rows (i)
  (declare (xargs :measure (nfix (- (expt 2 (m%%)) i))))
  (if (and (natp i)
           (< i (expt 2 (m%%))))
      (cons (xtable-row i 0)
            (xtable-rows (1+ i)))
    ())))

(local (defund xtable%% ()
  (xtable-rows 0)))

(local (defun xtable-induct (j k)
  (if (zp j)
      k
    (xtable-induct (1- j) (1+ k)))))

(local (defthmd xtable-1
  (implies (and (natp j)
                (natp k)
                (< (+ j k) (expt 2 (n%%))))
           (equal (nth j (xtable-row i k))
                  (xtable-entry i (+ j k))))
  :hints (("Goal" :induct (xtable-induct j k))
          ("Subgoal *1/2" :expand ((xtable-row i k)))
          ("Subgoal *1/1" :expand ((xtable-row i k))))))

(local (defthmd xtable-2
  (implies (and (natp i)
                (natp k)
                (< (+ i k) (expt 2 (m%%))))
           (equal (nth i (xtable-rows k))
                  (xtable-row (+ i k) 0)))
  :hints (("Goal" :induct (xtable-induct i k))
          ("Subgoal *1/1" :expand ((xtable-rows k))))))

(local (defthmd xtable-3
  (implies (and (natp j)
                (< j (expt 2 (n%%))))
           (equal (nth j (xtable-row i 0))
                  (xtable-entry i j)))
  :hints (("Goal" :use (:instance xtable-1 (k 0))))))

(local (defthmd xtable-4
  (implies (and (natp i)
                (< i (expt 2 (m%%))))
           (equal (nth i (xtable-rows 0))
                  (xtable-row i 0)))
  :hints (("Goal" :use (:instance xtable-2 (k 0))))))

(local (defthm xtable-5
  (integerp (xtable-entry i j))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable xtable-entry)))))

(local (defthmd xtable-6
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
           (equal (lookup i j (xtable%%))
                  (xtable-entry i j)))
  :hints (("Goal" :in-theory (enable lookup xtable%%)
                  :use (xtable-4 xtable-3)))))

(defthmd xtable-def
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
           (equal (lookup i j (xtable%%))
                  (if (and (> (pi0 i (m%%))
                           (- (+ (delta0 j (n%%))
                                 (expt 2 (- (n%%)))
                                 (expt 2 (- 3 (m%%))))))
                           (<= (pi0 i (m%%))
                               (- (expt 2 (- (* (k%%) (rho%%))))
                                  (+ (delta0 j (n%%))
                                     (expt 2 (- (n%%)))
                                     (expt 2 (- 3 (m%%)))))))
                      (- 1 (expt 2 (rho%%)))
                    (lookup i j (table%%)))))
  :hints (("Goal" :in-theory (enable xtable-entry)
                  :use (xtable-6))))

)

(defthm admissibility-equivalence-b
  (admissible-srt-table-p (k%%) (rho%%) (m%%) (n%%) (xtable%%))
  :rule-classes ())

;; Examples:

(defthm admissible-srt-table-p-2-2-6-2
  (admissible-srt-table-p 2 2 6 2 (srt-table 2 6 2)))

(defthm admissible-srt-table-p-2-3-7-4
  (admissible-srt-table-p 2 3 7 4 (srt-table 3 7 4)))

(defthm admissible-srt-table-p-2-3-8-3
  (admissible-srt-table-p 2 3 8 3 (srt-table 3 8 3)))

(defthm admissible-for-iteration-p-2-2-6-2
  (implies (and (natp k)
                (> k 2))
           (admissible-for-iteration-p k 2 6 2 (srt-table 2 6 2))))


;;**********************************************************************************
;; Criterion for Existence of SRT Table
;;**********************************************************************************

(defund check-exists-entry (i j k rho m n)
  (or (not (accessible-p i j k rho m n))
      (<= (lower i j rho m n) (- 1 (expt 2 rho)))
      (check-lower-bound (lower i j rho m n) i j (1+ k) rho m n)))

(defund check-exists-row (i j k rho m n)
  (if (zp j)
      t
    (and (check-exists-entry i (1- j) k rho m n)
         (check-exists-row i (1- j) k rho m n))))

(defund check-exists-rows (i k rho m n)
  (if (zp i)
      t
    (and (check-exists-row (1- i) (expt 2 n) k rho m n)
         (check-exists-rows (1- i) k rho m n))))

(defund exists-srt-table-p (k rho m n)
  (check-exists-rows (expt 2 m) k rho m n))

(defthm exists-srt-table-p-2-2-6-2
  (exists-srt-table-p 2 2 6 2))

(defthm exists-srt-table-p-2-3-7-4
  (exists-srt-table-p 2 3 7 4))

(defthm exists-srt-table-p-2-3-8-3
  (exists-srt-table-p 2 3 8 3))

(defthm not-exists-srt-table-p-100-2-5-2
  (not (exists-srt-table-p 100 2 5 2)))

(defthm not-exists-srt-table-p-100-3-6-4
  (not (exists-srt-table-p 100 3 6 4)))

(defthm srt-table-existence-a
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (exists-srt-table-p k rho m n))
           (admissible-srt-table-p k rho m n (srt-table rho m n))))

(defthm srt-table-existence-b
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (admissible-srt-table-p k rho m n table))
           (exists-srt-table-p k rho m n)))


;;**********************************************************************************
;; Seed Table Requirements
;;**********************************************************************************

(encapsulate (((rho**) => *) ((k**) => *) ((x**) => *) ((s**) => *))

(local (defun k** () 1))

(local (defun rho** () 2))

(defthm k**-rho**-constraint
  (and (not (zp (k**)))
       (not (zp (rho**)))
       (>= (* (k**) (rho**)) 2))
  :rule-classes ())

(local (defun x** () 1/2))

(defthm x**-constraint
  (and (rationalp (x**))
       (> (x**) 1/4)
       (< (x**) 1))
  :rule-classes ())

(defun l** () (fl (* (expt 2 (* (k**) (rho**))) (x**))))

(local (defun s** () 3))

(defthm s**-constraint
  (and (integerp (s**))
       (<= (expt 2 (1- (* (k**) (rho**)))) (s**))
       (< (s**) (expt 2 (* (k**) (rho**))))
       (<= (* (expt 2 (- (* (k**) (rho**)))) (expt (1- (s**)) 2))
           (l**))
       (>= (* (expt 2 (- (* (k**) (rho**)))) (expt (1+ (s**)) 2))
           (1+ (l**))))
  :rule-classes ())

(defun q0** () (* (expt 2 (- (* (k**) (rho**)))) (s**)))

)

(defthm seed-req-a
  (and (<= 1/2 (q0**))
       (< (q0**) 1)
       (>= (x**) (expt (- (q0**) (expt 2 (- (* (k**) (rho**))))) 2))
       (< (x**) (expt (+ (q0**) (expt 2 (- (* (k**) (rho**))))) 2)))
  :rule-classes ())

(defun s1** ()
  (if (or (= (mod (s**) 2) 1)
          (>= (x**) (* (q0**) (q0**))))
      (s**)
    (1- (s**))))

(defun q1** () (* (expt 2 (- (* (k**) (rho**)))) (s1**)))

(defthm seed-req-b
  (and (<= 1/2 (q1**))
       (< (q1**) 1)
       (>= (x**) (expt (- (q1**) (expt 2 (- (* (k**) (rho**))))) 2))
       (< (x**) (expt (+ (q1**) (expt 2 (- (* (k**) (rho**))))) 2)))
  :rule-classes ())

(encapsulate (((h** *) => *) ((q** *) => *))

(local (defun h** (k) (declare (ignore k)) 0))

(defthm h**-constraint
  (implies (and (not (zp k))
                (> k (k**)))
           (and (integerp (h** k))
                (< (abs (h** k)) (expt 2 (rho**)))))
  :rule-classes ())

(local (defun q** (k)
  (if (or (zp k)
          (<= k (k**)))
      (q1**)
    (+ (q** (1- k))
       (* (expt 2 (- (* k (rho**))))
          (h** k))))))

(defthm q**-constraint
  (and (= (q** (k**)) (q1**))
       (implies (and (not (zp k))
                     (> k (k**)))
                (= (q** k)
                   (+ (q** (1- k))
                      (* (expt 2 (- (* k (rho**))))
                         (h** k))))))
  :hints (("Goal" :use (q** s**-constraint k**-rho**-constraint
                        (:instance q** (k (k**))))))
  :rule-classes ())

)

(defthm seed-req-c
  (implies (and (not (zp k))
                (>= k (k**))
                (< (x**) (expt (+ (q** k) (expt 2 (- (* k (rho**))))) 2)))
           (= (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** k)))
              (fl (* (expt 2 (1- (* (k**) (rho**)))) (q1**)))))
  :rule-classes ())


;;**********************************************************************************
;; A Compliant Seed Table
;;**********************************************************************************

(defun cg-sqrt (x min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (natp min)
           (natp max)
           (<= min max))
      (if (>= (* min min) x)
          min
        (cg-sqrt x (1+ min) max))
    0))

(defun seed (l k rho)
  (1- (cg-sqrt (* (expt 2 (* k rho)) (1+ l))
               (if (= (* k rho) 1)
                   1
                 (expt 2 (- (* k rho) 2)))
               (expt 2 (* k rho)))))

(defthm cg-sqrt-lemma
  (implies (and (rationalp x)
                (not (zp min))
                (not (zp max))
                (<= (* min min) x)
                (<= x (* max max)))
           (let ((y (cg-sqrt x min max)))
             (and (<= x (* y y))
                  (< (* (1- y) (1- y)) x))))
  :rule-classes ())

(defthm seed-compliance
  (implies (and (not (zp k))
                (not (zp rho))
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (and (integerp (seed l k rho))
                (<= (expt 2 (1- (* k rho))) (seed l k rho))
                (< (seed l k rho) (expt 2 (* k rho)))
                (<= (* (expt 2 (- (* k rho))) (expt (1- (seed l k rho)) 2))
                    l)
                (>= (* (expt 2 (- (* k rho))) (expt (1+ (seed l k rho)) 2))
                    (1+ l))))
  :rule-classes ())


;;**********************************************************************************
;; Initial K Iterations
;;**********************************************************************************

(defund digit (i seed k rho )
  (bits seed (1- (* (- (1+ k) i) rho)) (* (- k i) rho)))

(defund root (i seed k rho)
  (if (zp i)
      0
    (+ (root (1- i) seed k rho)
       (* (expt 2 (- (* i rho)))
          (digit i seed k rho)))))

(defthm seed-digits
  (implies (and (not (zp k))
                (not (zp rho))
                (natp seed)
                (<= (expt 2 (- (* k rho) 2)) seed)
                (< seed (expt 2 (* k rho))))
           (= (root k seed k rho)
              (* (expt 2 (- (* k rho))) seed)))
  :rule-classes ())
