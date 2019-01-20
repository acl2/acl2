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

(include-book "bits-new")
(include-book "rtl-new")
(local (include-book "../lib2/top"))



(local
 (encapsulate ()
              (local (include-book "bits-new-proofs"))

             (defthm bits_alt-is-bits
               (equal (bits_alt x i j)
                      (bits x i j)))


             (defthm bitn_alt-is-bitn
               (equal (bitn_alt x n)
                      (bitn x n)))


             (defthm binary-cat_alt-is-binary-cat
               (equal (binary-cat_alt x m y n)
                      (binary-cat x m y n)))

             ))




;;;**********************************************************************
;;;                     LNOT_ALT
;;;**********************************************************************

(defund lnot_alt (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits_alt x (1- n) 0)))
    0))

(local
 (defthm lnot_alt-is-lnot
   (equal (lnot_alt x n)
          (lnot x n))
   :hints (("Goal" :in-theory (e/d (lnot lnot_alt) ())))))

(defthm lnot_alt-nonnegative-integer-type
  (and (integerp (lnot_alt x n))
       (<= 0 (lnot_alt x n)))
  :rule-classes ((:type-prescription :typed-term (lnot_alt x n))))

(in-theory (disable (:type-prescription lnot_alt)))

(defthmd lnot_alt-bits_alt-1
  (equal (lnot_alt (bits_alt x (1- n) 0) n)
         (lnot_alt x n))
  :hints (("Goal" :use lnot-bits-1)))

(defthm lnot_alt-bvecp
  (implies (and (<= n k)
		(case-split (integerp k)))
	   (bvecp (lnot_alt x n) k)))

(defthm lnot_alt-x-0
  (equal (lnot_alt x 0) 0)
  :hints (("Goal" :use lnot-x-0)))

(defthmd lnot_alt-shift
  (implies (and (case-split (integerp x))
                (case-split (natp n))
                (natp k))
           (equal (lnot_alt (* (expt 2 k) x) n)
                  (if (<= k n)
                      (+ (* (expt 2 k) (lnot_alt x (- n k)))
                         (1- (expt 2 k)))
                    (1- (expt 2 n)))))
  :hints (("Goal" :use lnot-shift)))

(defthmd lnot_alt-shift-2
  (implies (and (syntaxp (not (quotep x))) ;prevents loops
                (case-split (integerp x))
                (case-split (< 0 n))
                (case-split (integerp n)))
           (equal (lnot_alt (* 2 x) n)
                  (+ 1 (* 2 (lnot_alt x (1- n))))))
  :hints (("Goal" :use lnot-shift-2)))

(defthmd lnot_alt-fl
  (implies (and (natp n)
                (natp k))
           (equal (fl (* (/ (expt 2 k)) (lnot_alt x (+ n k))))
                  (lnot_alt (fl (/ x (expt 2 k))) n)))
  :hints (("Goal" :use lnot-fl)))

(defthm mod-lnot_alt
  (implies (and (<= k n)
                (natp k)
                (integerp n))
           (equal (mod (lnot_alt x n) (expt 2 k))
                  (lnot_alt (mod x (expt 2 k)) k)))
  :hints (("Goal" :use mod-lnot)))

(defthmd bits_alt-lnot_alt
  (implies (and (case-split (natp j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits_alt (lnot_alt x n) i j)
                  (if (< i n)
                      (lnot_alt (bits_alt x i j)
                            (1+ (- i j)))
                    (lnot_alt (bits_alt x (1- n) j)
                          (- n j)))))
  :hints (("Goal" :use bits-lnot)))

(defthmd bitn_alt-lnot_alt
  (implies (and (case-split (natp k))
		(case-split (natp n)))
	   (equal (bitn_alt (lnot_alt x n) k)
		  (if (< k n)
		      (lnot_alt (bitn_alt x k) 1)
		    0)))
  :hints (("Goal" :use bitn-lnot)))

(defthmd lnot_alt-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(equal l (+ m n)))
	   (equal (lnot_alt (cat_alt x m y n) l)
		  (cat_alt (lnot_alt x m) m (lnot_alt y n) n)))
  :hints (("Goal" :use lnot-cat)))


;;;**********************************************************************
;;;                LAND_ALT, LIOR_ALT, and LXOR_ALT
;;;**********************************************************************


(defun lognop-2-induct (x y)
  (if (or (zp x) (zp y))
      ()
    (lognop-2-induct (fl (/ x 2)) (fl (/ y 2)))))

(defun lognop-2-n-induct (x y n)
  (if (zp n)
      (cons x y)
    (lognop-2-n-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))

(defun lognop-3-induct (x y z)
  (declare (xargs :measure (+ (nfix x) (nfix y) (nfix z))))
  (if (and (natp x) (natp y) (natp z))
      (if (and (zp x) (zp y) (zp z))
	  t
	(lognop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))


(local (include-book "log-new"))

(defund binary-land_alt (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (and (equal (bitn_alt x 0) 1)
                       (equal (bitn_alt y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-land_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-land_alt (mod x 2) (mod y 2) 1))))
       :exec
       (logand (bits_alt x (1- n) 0)
               (bits_alt y (1- n) 0))))

(local
 (defthm land_alt-is-land
   (equal (binary-land_alt x y n)
          (binary-land x y n))
   :hints (("Goal" :in-theory (e/d (binary-land_alt
                                    binary-land) ())))))

(defmacro land_alt (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x))
         `(binary-land_alt ,@x))
        (t
         `(binary-land_alt ,(car x)
                       (land_alt ,@(cdr x))
                       ,(car (last x))))))

(defthm land_alt-nonnegative-integer-type
  (and (integerp (land_alt x y n))
       (<= 0 (land_alt x y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-land_alt)))

(defund binary-lior_alt (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (or (equal (bitn_alt x 0) 1)
                      (equal (bitn_alt y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-lior_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lior_alt (mod x 2) (mod y 2) 1))))
       :exec
       (logior (bits_alt x (1- n) 0)
               (bits_alt y (1- n) 0))))


(local
 (defthm lior_alt-is-lior
   (equal (binary-lior_alt x y n)
          (binary-lior x y n))
   :hints (("Goal" :in-theory (e/d (binary-lior_alt
                                    binary-lior) ())))))

(defmacro lior_alt (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior_alt x y n) -- the base case
         `(binary-lior_alt ,@x))
        (t
         `(binary-lior_alt ,(car x)
                       (lior_alt ,@(cdr x))
                       ,(car (last x))))))

(defthm lior_alt-nonnegative-integer-type
  (and (integerp (lior_alt x y n))
       (<= 0 (lior_alt x y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-lior_alt)))

(defund binary-lxor_alt (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (iff (equal (bitn_alt x 0) 1)
                       (equal (bitn_alt y 0) 1))
                  0
                1))
             (t (+ (* 2 (binary-lxor_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lxor_alt (mod x 2) (mod y 2) 1))))
       :exec
       (logxor (bits_alt x (1- n) 0)
               (bits_alt y (1- n) 0))))


(local
 (defthm lxor_alt-is-lxor
   (equal (binary-lxor_alt x y n)
          (binary-lxor x y n))
   :hints (("Goal" :in-theory (e/d (binary-lxor_alt
                                    binary-lxor) ())))))


(defmacro lxor_alt (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x))
         `(binary-lxor_alt ,@x))
        (t
         `(binary-lxor_alt ,(car x)
                       (lxor_alt ,@(cdr x))
                       ,(car (last x))))))

(defthm lxor_alt-nonnegative-integer-type
  (and (integerp (lxor_alt x y n))
       (<= 0 (lxor_alt x y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-lxor_alt)))

;; (defun lognop-2-induct (x y)
;;   (if (or (zp x) (zp y))
;;       ()
;;     (lognop-2-induct (fl (/ x 2)) (fl (/ y 2)))))

;; (defun lognop-2-n-induct (x y n)
;;   (if (zp n)
;;       (cons x y)
;;     (lognop-2-n-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))

;; (defun lognop-3-induct (x y z)
;;   (declare (xargs :measure (:? x y z)))
;;   (if (and (natp x) (natp y) (natp z))
;;       (if (and (zp x) (zp y) (zp z))
;; 	  t
;; 	(lognop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
;;     t))

(defthm land_alt-x-y-0
    (equal (land_alt x y 0) 0)
    :hints (("Goal" :use land-x-y-0)))

(defthm lior_alt-x-y-0
    (equal (lior_alt x y 0) 0)
    :hints (("Goal" :use lior-x-y-0)))

(defthm lxor_alt-x-y-0
    (equal (lxor_alt x y 0) 0)
    :hints (("Goal" :use lxor-x-y-0)))

(defthmd land_alt-bits_alt-1
  (equal (land_alt (bits_alt x (1- n) 0) y n)
         (land_alt x y n))
    :hints (("Goal" :use land-bits-1)))

(defthmd land_alt-bits_alt-2
  (equal (land_alt x (bits_alt y (1- n) 0) n)
         (land_alt x y n))
    :hints (("Goal" :use land-bits-2)))

(defthmd lior_alt-bits_alt-1
  (equal (lior_alt (bits_alt x (1- n) 0) y n)
         (lior_alt x y n))
    :hints (("Goal" :use lior-bits-1)))

(defthmd lior_alt-bits_alt-2
  (equal (lior_alt x (bits_alt y (1- n) 0) n)
         (lior_alt x y n))
    :hints (("Goal" :use lior-bits-2)))

(defthmd lxor_alt-bits_alt-1
  (equal (lxor_alt (bits_alt x (1- n) 0) y n)
         (lxor_alt x y n))
    :hints (("Goal" :use lxor-bits-1)))

(defthmd lxor_alt-bits_alt-2
  (equal (lxor_alt x (bits_alt y (1- n) 0) n)
         (lxor_alt x y n))
    :hints (("Goal" :use lxor-bits-2)))

(defthm land_alt-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (land_alt x y n) k))
    :hints (("Goal" :use land-bvecp)))

(defthm lior_alt-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (lior_alt x y n) k))
    :hints (("Goal" :use lior-bvecp)))

(defthm lxor_alt-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (lxor_alt x y n) k))
    :hints (("Goal" :use lxor-bvecp)))

(defthm land_alt-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (land_alt x y n) m))
    :hints (("Goal" :use land-bvecp-2)))

(defthm lior_alt-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (lior_alt x y n) m))
    :hints (("Goal" :use lior-bvecp-2)))

(defthm lxor_alt-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (lxor_alt x y n) m))
    :hints (("Goal" :use lxor-bvecp-2)))

(defthmd land_alt-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land_alt x y m) (land_alt x y n)))
    :hints (("Goal" :use land-reduce)))

(defthmd lior_alt-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (< n m)
		  (natp n)
		  (natp m))
	     (equal (lior_alt x y m) (lior_alt x y n)))
    :hints (("Goal" :use lior-reduce)))

(defthmd lxor_alt-reduce
  (implies (and (bvecp x n)
		(bvecp y n)
		(< n m)
		(case-split (integerp m)))
	   (equal (lxor_alt x y m) (lxor_alt x y n)))
    :hints (("Goal" :use lxor-reduce)))

(defthmd land_alt-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (land_alt x y n)
                  (+ (* 2 (land_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land_alt (bitn_alt x 0) (bitn_alt y 0) 1))))
    :hints (("Goal" :use land-def)))

(defthmd lior_alt-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (lior_alt x y n)
                  (+ (* 2 (lior_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lior_alt (bitn_alt x 0) (bitn_alt y 0) 1))))
    :hints (("Goal" :use lior-def)))

(defthmd lxor_alt-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (lxor_alt x y n)
                  (+ (* 2 (lxor_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lxor_alt (bitn_alt x 0) (bitn_alt y 0) 1))))
    :hints (("Goal" :use lxor-def)))

(defthm land_alt-0
  (equal (land_alt 0 y n)
	 0)
    :hints (("Goal" :use land-0)))

(defthmd land_alt-equal-0
  (implies (and (bvecp i 1)
		(bvecp j 1))
	   (equal (equal 0 (land_alt i j 1))
		  (or (equal i 0)
		      (equal j 0))))
    :hints (("Goal" :use land-equal-0)))

(defthm lior_alt-0
  (implies (case-split (bvecp y n))
	   (equal (lior_alt 0 y n) y))
    :hints (("Goal" :use lior-0)))

(defthmd lior_alt-equal-0
  (implies (and (case-split (bvecp x n))
		(case-split (bvecp y n))
		(case-split (integerp n)))
	   (equal (equal 0 (lior_alt x y n))
		  (and (equal x 0)
		       (equal y 0))))
    :hints (("Goal" :use lior-equal-0)))

(defthm lxor_alt-0
  (implies (case-split (bvecp y n))
	   (equal (lxor_alt 0 y n) y))
    :hints (("Goal" :use lxor-0)))

(defthm land_alt-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (land_alt (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (land_alt x y (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use land-shift)))

(defthm lxor_alt-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (lxor_alt (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (lxor_alt x y (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use lxor-shift)))

(defthm lior_alt-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (lior_alt (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (lior_alt x y (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use lior-shift)))

(defthmd fl-land_alt
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (land_alt x y (+ n k)) (expt 2 k)))
                  (land_alt (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :use fl-land)))

(defthmd fl-lior_alt
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (lior_alt x y (+ n k)) (expt 2 k)))
                  (lior_alt (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :use fl-lior)))

(defthmd fl-lxor_alt
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (lxor_alt x y (+ n k)) (expt 2 k)))
                  (lxor_alt (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :use fl-lxor)))

(defthmd mod-land_alt
  (implies (and (integerp n)
                (integerp k)
                (<= k n))
           (equal (mod (land_alt x y n) (expt 2 k))
                  (land_alt x y k)))
  :hints (("Goal" :use mod-land)))

(defthmd mod-lior_alt
  (implies (and (integerp n)
                (<= k n))
           (equal (mod (lior_alt x y n) (expt 2 k))
                  (lior_alt x y k)))
  :hints (("Goal" :use mod-lior)))

(defthmd mod-lxor_alt
  (implies (and (integerp n)
                (integerp k)
                (<= k n))
           (equal (mod (lxor_alt x y n) (expt 2 k))
                  (lxor_alt x y k)))
  :hints (("Goal" :use mod-lxor)))

(defthm bits_alt-land_alt
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits_alt (land_alt x y n) i j)
		  (land_alt (bits_alt x i j)
			(bits_alt y i j)
			(+ (min n (1+ i)) (- j)))))
  :hints (("Goal" :use bits-land)))

(defthm bits_alt-lior_alt
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits_alt (lior_alt x y n) i j)
		  (lior_alt (bits_alt x i j)
			(bits_alt y i j)
			(+ (min n (1+ i)) (- j)))))
  :hints (("Goal" :use bits-lior)))

(defthm bits_alt-lxor_alt
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits_alt (lxor_alt x y n) i j)
		  (lxor_alt (bits_alt x i j)
			(bits_alt y i j)
			(+ (min n (1+ i)) (- j)))))
  :hints (("Goal" :use bits-lxor)))

(defthm bitn_alt-land_alt
  (implies (and (case-split (<= 0 k))
		(case-split (integerp n)))
	   (equal (bitn_alt (land_alt x y n) k)
		  (if (< k n)
		      (land_alt (bitn_alt x k)
			    (bitn_alt y k)
			    1)
		    0)))
  :hints (("Goal" :use bitn-land)))

(defthm bitn_alt-lior_alt
  (implies (and (case-split (<= 0 k))
		(case-split (integerp n)))
	   (equal (bitn_alt (lior_alt x y n) k)
		  (if (< k n)
		      (lior_alt (bitn_alt x k)
			    (bitn_alt y k)
			    1)
		    0)))
  :hints (("Goal" :use bitn-lior)))

(defthm bitn_alt-lxor_alt
  (implies (and (case-split (<= 0 k))
		(case-split (integerp n)))
	   (equal (bitn_alt (lxor_alt x y n) k)
		  (if (< k n)
		      (lxor_alt (bitn_alt x k)
			    (bitn_alt y k)
			    1)
		    0)))
  :hints (("Goal" :use bitn-lxor)))

(defthmd land_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (integerp m))
		(> m 0)
		(equal l (+ m n)))
	   (equal (land_alt (cat_alt x1 m y1 n) (cat_alt x2 m y2 n) l)
		  (cat_alt (land_alt x1 x2 m) m (land_alt y1 y2 n) n)))
  :hints (("Goal" :use land-cat)))

(defthm land_alt-cat_alt-constant
  (implies (and (case-split (integerp n))
		(case-split (integerp m))
		(syntaxp (quotep c))
		(> n 0)
		(> m 0)
		(equal l (+ m n)))
	   (equal (land_alt c (cat_alt x2 m y2 n) l)
		  (cat_alt (land_alt (bits_alt c (+ -1 m n) n) x2 m)
		       m
		       (land_alt (bits_alt c (1- n) 0) y2 n)
		       n)))
  :hints (("Goal" :use land-cat-constant)))

(defthmd lior_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (integerp m))
		(> m 0)
		(equal l (+ m n)))
	   (equal (lior_alt (cat_alt x1 m y1 n) (cat_alt x2 m y2 n) l)
		  (cat_alt (lior_alt x1 x2 m) m (lior_alt y1 y2 n) n)))
  :hints (("Goal" :use lior-cat)))

(defthm lior_alt-cat_alt-constant
  (implies (and (case-split (integerp n))
		(case-split (integerp m))
		(syntaxp (quotep c))
		(> n 0)
		(> m 0)
		(equal l (+ m n)))
	   (equal (lior_alt c (cat_alt x2 m y2 n) l)
		  (cat_alt (lior_alt (bits_alt c (+ -1 m n) n) x2 m)
		       m
		       (lior_alt (bits_alt c (1- n) 0) y2 n)
		       n)))
  :hints (("Goal" :use lior-cat-constant)))

(defthmd lxor_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (integerp m))
		(> m 0)
		(equal l (+ m n)))
	   (equal (lxor_alt (cat_alt x1 m y1 n) (cat_alt x2 m y2 n) l)
		  (cat_alt (lxor_alt x1 x2 m) m (lxor_alt y1 y2 n) n)))
  :hints (("Goal" :use lxor-cat)))

(defthm lxor_alt-cat_alt-constant
  (implies (and (case-split (integerp n))
		(case-split (integerp m))
		(syntaxp (quotep c))
		(> n 0)
		(> m 0)
		(equal l (+ m n)))
	   (equal (lxor_alt c (cat_alt x2 m y2 n) l)
		  (cat_alt (lxor_alt (bits_alt c (+ -1 m n) n) x2 m)
		       m
		       (lxor_alt (bits_alt c (1- n) 0) y2 n)
		       n)))
  :hints (("Goal" :use lxor-cat-constant)))

(defthm land_alt-bnd
    (implies (case-split (<= 0 x))
	     (<= (land_alt x y n) x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use land-bnd)))

(defthm lior_alt-bnd
  (implies (case-split (bvecp x n))
	   (<= x (lior_alt x y n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use lior-bnd)))

(defthm lxor_alt-bnd
  (<= (lxor_alt x y n) (lior_alt x y n))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use lxor-bnd)))

(defthmd land_alt-with-shifted-arg
  (implies (and (integerp x)
		(rationalp y)
		(integerp m)
		(integerp n)
		(<= 0 m))
	   (equal (land_alt (* (expt 2 m) x) y n)
		  (* (expt 2 m) (land_alt x (bits_alt y (1- n) m) (+ n (-
                                                                        m))))))
  :hints (("Goal" :use land-with-shifted-arg)))

(defthm lior_alt-with-shifted-arg
  (implies (and (bvecp y m)
                (bvecp x (- n m))
                (<= m n)
                (natp m)
                (integerp n))
           (= (lior_alt (* (expt 2 m) x) y n)
              (+ (* (expt 2 m) x) y)))
  :rule-classes ()
  :hints (("Goal" :use lior-with-shifted-arg)))

(defthmd land_alt-expt
  (implies (and (natp n)
		(natp k)
		(< k n))
	   (equal (land_alt x (expt 2 k) n)
		  (* (expt 2 k) (bitn_alt x k))))
  :hints (("Goal" :use land-expt)))

(defthm lior_alt-expt
    (implies (and (natp n)
		  (natp k)
		  (< k n))
	     (= (lior_alt x (expt 2 k) n)
		(+ (bits_alt x (1- n) 0)
		   (* (expt 2 k) (- 1 (bitn_alt x k))))))
  :rule-classes ()
  :hints (("Goal" :use lior-expt)))

(defthmd lxor_alt-expt
  (implies (and (natp n)
		(natp k)
		(< k n))
	   (equal (lxor_alt x (expt 2 k) n)
		  (+ (bits_alt x (1- n) 0)
                     (* (expt 2 k) (- 1 (* 2 (bitn_alt x k)))))))
  :hints (("Goal" :use lxor-expt)))

(defthm land_alt-ones
  (equal (land_alt (1- (expt 2 n)) x n)
	 (bits_alt x (1- n) 0))
  :rule-classes nil
  :hints (("Goal" :use land-ones)))

(defthm land_alt-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
		(equal k (1- (expt 2 n))))
	   (equal (land_alt k x n)
		  (bits_alt x (1- n) 0)))
  :hints (("Goal" :use land-ones-rewrite)))

(defthm lior_alt-ones
  (implies (and (case-split (bvecp x n))
		(case-split (natp n)))
	   (equal (lior_alt (1- (expt 2 n)) x n)
		  (1- (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use lior-ones)))

(defthm lior_alt-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
			      (quotep n)
			      (equal (cadr k) (1- (expt 2 (cadr n))))))
		(force (equal k (1- (expt 2 n))))
		(case-split (natp n))
		(case-split (bvecp x n)))
	   (equal (lior_alt k x n)
		  (1- (expt 2 n))))
  :hints (("Goal" :use lior-ones-rewrite)))

(defthm lxor_alt-ones
  (implies (case-split (bvecp x n))
	   (equal (lxor_alt (1- (expt 2 n)) x n)
		  (lnot_alt x n)))
  :rule-classes ()
  :hints (("Goal" :use lxor-ones)))

(defthm lxor_alt-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
			      (quotep n)
			      (equal (cadr k) (1- (expt 2 (cadr n))))))
		(force (equal k (1- (expt 2 n))))
		(case-split (bvecp x n)))
	   (equal (lxor_alt k x n)
		  (lnot_alt x n)))
  :hints (("Goal" :use lxor-ones-rewrite)))


;;;**********************************************************************
;;;                Algebraic Properties
;;;**********************************************************************

(defthm lnot_alt-lnot_alt
  (implies (and (case-split (natp n))
		(case-split (bvecp x n)))
	   (equal (lnot_alt (lnot_alt x n) n)
		  x))
    :hints (("Goal" :use lnot-lnot)))

(defthm land_alt-commutative
  (equal (land_alt y x n)
	 (land_alt x y n))
    :hints (("Goal" :use land-commutative)))

(defthm lior_alt-commutative
  (equal (lior_alt y x n)
	 (lior_alt x y n))
    :hints (("Goal" :use lior-commutative)))

(defthm lxor_alt-commutative
  (equal (lxor_alt y x n)
	 (lxor_alt x y n))
    :hints (("Goal" :use lxor-commutative)))

(defthm land_alt-associative
  (equal (land_alt (land_alt x y n) z n)
	 (land_alt x (land_alt y z n) n))
    :hints (("Goal" :use land-associative)))

(defthm lior_alt-associative
  (equal (lior_alt (lior_alt x y n) z n)
	 (lior_alt x (lior_alt y z n) n))
    :hints (("Goal" :use lior-associative)))

(defthm lxor_alt-associative
  (equal (lxor_alt (lxor_alt x y n) z n)
	 (lxor_alt x (lxor_alt y z n) n))
    :hints (("Goal" :use lxor-associative)))

(defthm land_alt-commutative-2
  (equal (land_alt y (land_alt x z n) n)
	 (land_alt x (land_alt y z n) n))
    :hints (("Goal" :use land-commutative-2)))

(defthm lior_alt-commutative-2
  (equal (lior_alt y (lior_alt x z n) n)
	 (lior_alt x (lior_alt y z n) n))
    :hints (("Goal" :use lior-commutative-2)))

(defthm lxor_alt-commutative-2
  (equal (lxor_alt y (lxor_alt x z n) n)
	 (lxor_alt x (lxor_alt y z n) n))
    :hints (("Goal" :use lxor-commutative-2)))

(defthm land_alt-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (land_alt x (land_alt y z n) n)
		  (land_alt (land_alt x y n) z n)))
    :hints (("Goal" :use land-combine-constants)))

(defthm lior_alt-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (lior_alt x (lior_alt y z n) n)
		  (lior_alt (lior_alt x y n) z n)))
    :hints (("Goal" :use lior-combine-constants)))

(defthm lxor_alt-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (lxor_alt x (lxor_alt y z n) n)
		  (lxor_alt (lxor_alt x y n) z n)))
    :hints (("Goal" :use lxor-combine-constants)))

(defthm land_alt-self
  (equal (land_alt x x n)
	 (bits_alt x (1- n) 0))
    :hints (("Goal" :use land-self)))

(defthm lior_alt-self
  (implies (and (case-split (bvecp x n))
		(case-split (integerp n)))
	   (equal (lior_alt x x n) x))
    :hints (("Goal" :use lior-self)))

(defthm lxor_alt-self
  (implies (case-split (bvecp x n))
	   (equal (lxor_alt x x n) 0))
    :hints (("Goal" :use lxor-self)))

(defthmd lior_alt-land_alt-1
  (equal (lior_alt x (land_alt y z n) n)
	 (land_alt (lior_alt x y n) (lior_alt x z n) n))
    :hints (("Goal" :use lior-land-1)))

(defthmd lior_alt-land_alt-2
  (equal (lior_alt (land_alt y z n) x n)
	 (land_alt (lior_alt x y n) (lior_alt x z n) n))
    :hints (("Goal" :use lior-land-2)))

(defthmd land_alt-lior_alt-1
  (equal (land_alt x (lior_alt y z n) n)
	 (lior_alt (land_alt x y n) (land_alt x z n) n))
    :hints (("Goal" :use land-lior-1)))

(defthmd land_alt-lior_alt-2
  (equal (land_alt (lior_alt y z n) x n)
	 (lior_alt (land_alt x y n) (land_alt x z n) n))
    :hints (("Goal" :use land-lior-2)))

(defthmd lior_alt-land_alt-lxor_alt
  (equal (lior_alt (land_alt x y n) (lior_alt (land_alt x z n) (land_alt y z n) n) n)
	 (lior_alt (land_alt x y n) (land_alt (lxor_alt x y n) z n) n))
    :hints (("Goal" :use lior-land-lxor)))

(defthmd lxor_alt-rewrite
  (equal (lxor_alt x y n)
	 (lior_alt (land_alt x (lnot_alt y n) n)
	       (land_alt y (lnot_alt x n) n)
	       n))
    :hints (("Goal" :use lxor-rewrite)))

(defthmd lnot_alt-lxor_alt
  (equal (lnot_alt (lxor_alt x y n) n)
	 (lxor_alt (lnot_alt x n) y n))
    :hints (("Goal" :use lnot-lxor)))
