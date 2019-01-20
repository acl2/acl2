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

(include-book "bits")
(include-book "rtl")

(local (include-book "logn-new"))




(local
 (defthm bits-is-bits_alt
   (equal (bits x i j)
          (bits_alt x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))

(local
 (defthm bitn-is-bitn_alt
   (equal (bitn x n)
          (bitn_alt x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt bitn) ())))))

(local
 (defthm binary-cat_alt-is-binary-cat
   (equal (binary-cat x m y n)
          (binary-cat_alt x m y n))
   :hints (("Goal" :in-theory (e/d (binary-cat_alt binary-cat) ())))))

(local
 (defthm mulcat_alt-is-mulcat
   (equal (mulcat l n x)
          (mulcat_alt l n x))
   :hints (("Goal" :in-theory (e/d (mulcat_alt mulcat) ())))))





;;;**********************************************************************
;;;                     LNOT
;;;**********************************************************************

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

(local
 (defthm lnot-is-lnot_alt
   (equal (lnot x n)
          (lnot_alt x n))
   :hints (("Goal" :in-theory (e/d (lnot lnot_alt) ())))))

(defthm lnot-nonnegative-integer-type
  (and (integerp (lnot x n))
       (<= 0 (lnot x n)))
  :rule-classes ((:type-prescription :typed-term (lnot x n))))

(in-theory (disable (:type-prescription lnot)))

(defthmd lnot-bits-1
  (equal (lnot (bits x (1- n) 0) n)
         (lnot x n))
  :hints (("Goal" :use lnot_alt-bits_alt-1)))

(defthm lnot-bvecp
  (implies (and (<= n k)
		(case-split (integerp k)))
	   (bvecp (lnot x n) k)))

(defthm lnot-x-0
  (equal (lnot x 0) 0)
  :hints (("Goal" :use lnot_alt-x-0)))

(defthmd lnot-shift
  (implies (and (case-split (integerp x))
                (case-split (natp n))
                (natp k))
           (equal (lnot (* (expt 2 k) x) n)
                  (if (<= k n)
                      (+ (* (expt 2 k) (lnot x (- n k)))
                         (1- (expt 2 k)))
                    (1- (expt 2 n)))))
  :hints (("Goal" :use lnot_alt-shift)))

(defthmd lnot-shift-2
  (implies (and (syntaxp (not (quotep x))) ;prevents loops
                (case-split (integerp x))
                (case-split (< 0 n))
                (case-split (integerp n)))
           (equal (lnot (* 2 x) n)
                  (+ 1 (* 2 (lnot x (1- n))))))
  :hints (("Goal" :use lnot_alt-shift-2)))

(defthmd lnot-fl
  (implies (and (natp n)
                (natp k))
           (equal (fl (* (/ (expt 2 k)) (lnot x (+ n k))))
                  (lnot (fl (/ x (expt 2 k))) n)))
  :hints (("Goal" :use lnot_alt-fl)))

(defthm mod-lnot
  (implies (and (<= k n)
                (natp k)
                (integerp n))
           (equal (mod (lnot x n) (expt 2 k))
                  (lnot (mod x (expt 2 k)) k)))
  :hints (("Goal" :use mod-lnot_alt)))

(defthmd bits-lnot
  (implies (and (case-split (natp j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (lnot x n) i j)
                  (if (< i n)
                      (lnot (bits x i j)
                            (1+ (- i j)))
                    (lnot (bits x (1- n) j)
                          (- n j)))))
  :hints (("Goal" :use bits_alt-lnot_alt)))

(defthmd bitn-lnot
  (implies (and (case-split (natp k))
		(case-split (natp n)))
	   (equal (bitn (lnot x n) k)
		  (if (< k n)
		      (lnot (bitn x k) 1)
		    0)))
  :hints (("Goal" :use bitn_alt-lnot_alt)))

(defthmd lnot-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(equal l (+ m n)))
	   (equal (lnot (cat x m y n) l)
		  (cat (lnot x m) m (lnot y n) n)))
  :hints (("Goal" :use lnot_alt-cat)))


;;;**********************************************************************
;;;                LAND, LIOR, and LXOR
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

(defund binary-land (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (and (equal (bitn x 0) 1)
                       (equal (bitn y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-land (mod x 2) (mod y 2) 1))))
       :exec
       (logand (bits x (1- n) 0)
               (bits y (1- n) 0))))

(local
 (defthm land-is-land
   (equal (binary-land x y n)
          (binary-land_alt x y n))
   :hints (("Goal" :in-theory (e/d (binary-land_alt
                                    binary-land) ())))))

(defmacro land (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x))
         `(binary-land ,@x))
        (t
         `(binary-land ,(car x)
                       (land ,@(cdr x))
                       ,(car (last x))))))

(defthm land-nonnegative-integer-type
  (and (integerp (land x y n))
       (<= 0 (land x y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-land)))

(defund binary-lior (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (or (equal (bitn x 0) 1)
                      (equal (bitn y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lior (mod x 2) (mod y 2) 1))))
       :exec
       (logior (bits x (1- n) 0)
               (bits y (1- n) 0))))


(local
 (defthm lior-is-lior
   (equal (binary-lior x y n)
          (binary-lior_alt x y n))
   :hints (("Goal" :in-theory (e/d (binary-lior_alt
                                    binary-lior) ())))))

(defmacro lior (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior x y n) -- the base case
         `(binary-lior ,@x))
        (t
         `(binary-lior ,(car x)
                       (lior ,@(cdr x))
                       ,(car (last x))))))

(defthm lior-nonnegative-integer-type
  (and (integerp (lior x y n))
       (<= 0 (lior x y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-lior)))

(defund binary-lxor (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (iff (equal (bitn x 0) 1)
                       (equal (bitn y 0) 1))
                  0
                1))
             (t (+ (* 2 (binary-lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lxor (mod x 2) (mod y 2) 1))))
       :exec
       (logxor (bits x (1- n) 0)
               (bits y (1- n) 0))))


(local
 (defthm lxor-is-lxor
   (equal (binary-lxor x y n)
          (binary-lxor_alt x y n))
   :hints (("Goal" :in-theory (e/d (binary-lxor_alt
                                    binary-lxor) ())))))


(defmacro lxor (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x))
         `(binary-lxor ,@x))
        (t
         `(binary-lxor ,(car x)
                       (lxor ,@(cdr x))
                       ,(car (last x))))))

(defthm lxor-nonnegative-integer-type
  (and (integerp (lxor x y n))
       (<= 0 (lxor x y n)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription binary-lxor)))

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

(defthm land-x-y-0
    (equal (land x y 0) 0)
    :hints (("Goal" :use land_alt-x-y-0)))

(defthm lior-x-y-0
    (equal (lior x y 0) 0)
    :hints (("Goal" :use lior_alt-x-y-0)))

(defthm lxor-x-y-0
    (equal (lxor x y 0) 0)
    :hints (("Goal" :use lxor_alt-x-y-0)))

(defthmd land-bits-1
  (equal (land (bits x (1- n) 0) y n)
         (land x y n))
    :hints (("Goal" :use land_alt-bits_alt-1)))

(defthmd land-bits-2
  (equal (land x (bits y (1- n) 0) n)
         (land x y n))
    :hints (("Goal" :use land_alt-bits_alt-2)))

(defthmd lior-bits-1
  (equal (lior (bits x (1- n) 0) y n)
         (lior x y n))
    :hints (("Goal" :use lior_alt-bits_alt-1)))

(defthmd lior-bits-2
  (equal (lior x (bits y (1- n) 0) n)
         (lior x y n))
    :hints (("Goal" :use lior_alt-bits_alt-2)))

(defthmd lxor-bits-1
  (equal (lxor (bits x (1- n) 0) y n)
         (lxor x y n))
    :hints (("Goal" :use lxor_alt-bits_alt-1)))

(defthmd lxor-bits-2
  (equal (lxor x (bits y (1- n) 0) n)
         (lxor x y n))
    :hints (("Goal" :use lxor_alt-bits_alt-2)))

(defthm land-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (land x y n) k))
    :hints (("Goal" :use land_alt-bvecp)))

(defthm lior-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (lior x y n) k))
    :hints (("Goal" :use lior_alt-bvecp)))

(defthm lxor-bvecp
  (implies (and (<= n k) (case-split (integerp k)))
	   (bvecp (lxor x y n) k))
    :hints (("Goal" :use lxor_alt-bvecp)))

(defthm land-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (land x y n) m))
    :hints (("Goal" :use land_alt-bvecp-2)))

(defthm lior-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (lior x y n) m))
    :hints (("Goal" :use lior_alt-bvecp-2)))

(defthm lxor-bvecp-2
    (implies (and (bvecp x m)
		  (bvecp y m))
	     (bvecp (lxor x y n) m))
    :hints (("Goal" :use lxor_alt-bvecp-2)))

(defthmd land-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land x y m) (land x y n)))
    :hints (("Goal" :use land_alt-reduce)))

(defthmd lior-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (< n m)
		  (natp n)
		  (natp m))
	     (equal (lior x y m) (lior x y n)))
    :hints (("Goal" :use lior_alt-reduce)))

(defthmd lxor-reduce
  (implies (and (bvecp x n)
		(bvecp y n)
		(< n m)
		(case-split (integerp m)))
	   (equal (lxor x y m) (lxor x y n)))
    :hints (("Goal" :use lxor_alt-reduce)))

(defthmd land-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (land x y n)
                  (+ (* 2 (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land (bitn x 0) (bitn y 0) 1))))
    :hints (("Goal" :use land_alt-def)))

(defthmd lior-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (lior x y n)
                  (+ (* 2 (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lior (bitn x 0) (bitn y 0) 1))))
    :hints (("Goal" :use lior_alt-def)))

(defthmd lxor-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (lxor x y n)
                  (+ (* 2 (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lxor (bitn x 0) (bitn y 0) 1))))
    :hints (("Goal" :use lxor_alt-def)))

(defthm land-0
  (equal (land 0 y n)
	 0)
    :hints (("Goal" :use land_alt-0)))

(defthmd land-equal-0
  (implies (and (bvecp i 1)
		(bvecp j 1))
	   (equal (equal 0 (land i j 1))
		  (or (equal i 0)
		      (equal j 0))))
    :hints (("Goal" :use land_alt-equal-0)))

(defthm lior-0
  (implies (case-split (bvecp y n))
	   (equal (lior 0 y n) y))
    :hints (("Goal" :use lior_alt-0)))

(defthmd lior-equal-0
  (implies (and (case-split (bvecp x n))
		(case-split (bvecp y n))
		(case-split (integerp n)))
	   (equal (equal 0 (lior x y n))
		  (and (equal x 0)
		       (equal y 0))))
    :hints (("Goal" :use lior_alt-equal-0)))

(defthm lxor-0
  (implies (case-split (bvecp y n))
	   (equal (lxor 0 y n) y))
    :hints (("Goal" :use lxor_alt-0)))

(defthm land-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (land (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (land x y (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use land_alt-shift)))

(defthm lxor-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (lxor (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (lxor x y (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use lxor_alt-shift)))

(defthm lior-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (lior (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (lior x y (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use lior_alt-shift)))

(defthmd fl-land
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (land x y (+ n k)) (expt 2 k)))
                  (land (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :use fl-land_alt)))

(defthmd fl-lior
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (lior x y (+ n k)) (expt 2 k)))
                  (lior (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :use fl-lior_alt)))

(defthmd fl-lxor
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (lxor x y (+ n k)) (expt 2 k)))
                  (lxor (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :use fl-lxor_alt)))

(defthmd mod-land
  (implies (and (integerp n)
                (integerp k)
                (<= k n))
           (equal (mod (land x y n) (expt 2 k))
                  (land x y k)))
  :hints (("Goal" :use mod-land_alt)))

(defthmd mod-lior
  (implies (and (integerp n)
                (<= k n))
           (equal (mod (lior x y n) (expt 2 k))
                  (lior x y k)))
  :hints (("Goal" :use mod-lior_alt)))

(defthmd mod-lxor
  (implies (and (integerp n)
                (integerp k)
                (<= k n))
           (equal (mod (lxor x y n) (expt 2 k))
                  (lxor x y k)))
  :hints (("Goal" :use mod-lxor_alt)))

(defthm bits-land
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (land x y n) i j)
		  (land (bits x i j)
			(bits y i j)
			(+ (min n (1+ i)) (- j)))))
  :hints (("Goal" :use bits_alt-land_alt)))

(defthm bits-lior
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (lior x y n) i j)
		  (lior (bits x i j)
			(bits y i j)
			(+ (min n (1+ i)) (- j)))))
  :hints (("Goal" :use bits_alt-lior_alt)))

(defthm bits-lxor
  (implies (and (case-split (<= 0 j))
		(case-split (integerp n))
		(case-split (integerp i)))
	   (equal (bits (lxor x y n) i j)
		  (lxor (bits x i j)
			(bits y i j)
			(+ (min n (1+ i)) (- j)))))
  :hints (("Goal" :use bits_alt-lxor_alt)))

(defthm bitn-land
  (implies (and (case-split (<= 0 k))
		(case-split (integerp n)))
	   (equal (bitn (land x y n) k)
		  (if (< k n)
		      (land (bitn x k)
			    (bitn y k)
			    1)
		    0)))
  :hints (("Goal" :use bitn_alt-land_alt)))

(defthm bitn-lior
  (implies (and (case-split (<= 0 k))
		(case-split (integerp n)))
	   (equal (bitn (lior x y n) k)
		  (if (< k n)
		      (lior (bitn x k)
			    (bitn y k)
			    1)
		    0)))
  :hints (("Goal" :use bitn_alt-lior_alt)))

(defthm bitn-lxor
  (implies (and (case-split (<= 0 k))
		(case-split (integerp n)))
	   (equal (bitn (lxor x y n) k)
		  (if (< k n)
		      (lxor (bitn x k)
			    (bitn y k)
			    1)
		    0)))
  :hints (("Goal" :use bitn_alt-lxor_alt)))

(defthmd land-cat
  (implies (and (case-split (natp n))
		(case-split (integerp m))
		(> m 0)
		(equal l (+ m n)))
	   (equal (land (cat x1 m y1 n) (cat x2 m y2 n) l)
		  (cat (land x1 x2 m) m (land y1 y2 n) n)))
  :hints (("Goal" :use land_alt-cat_alt)))

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
  :hints (("Goal" :use land_alt-cat_alt-constant)))

(defthmd lior-cat
  (implies (and (case-split (natp n))
		(case-split (integerp m))
		(> m 0)
		(equal l (+ m n)))
	   (equal (lior (cat x1 m y1 n) (cat x2 m y2 n) l)
		  (cat (lior x1 x2 m) m (lior y1 y2 n) n)))
  :hints (("Goal" :use lior_alt-cat_alt)))

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
  :hints (("Goal" :use lior_alt-cat_alt-constant)))

(defthmd lxor-cat
  (implies (and (case-split (natp n))
		(case-split (integerp m))
		(> m 0)
		(equal l (+ m n)))
	   (equal (lxor (cat x1 m y1 n) (cat x2 m y2 n) l)
		  (cat (lxor x1 x2 m) m (lxor y1 y2 n) n)))
  :hints (("Goal" :use lxor_alt-cat_alt)))

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
  :hints (("Goal" :use lxor_alt-cat_alt-constant)))

(defthm land-bnd
    (implies (case-split (<= 0 x))
	     (<= (land x y n) x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use land_alt-bnd)))

(defthm lior-bnd
  (implies (case-split (bvecp x n))
	   (<= x (lior x y n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use lior_alt-bnd)))

(defthm lxor-bnd
  (<= (lxor x y n) (lior x y n))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use lxor_alt-bnd)))

(defthmd land-with-shifted-arg
  (implies (and (integerp x)
		(rationalp y)
		(integerp m)
		(integerp n)
		(<= 0 m))
	   (equal (land (* (expt 2 m) x) y n)
		  (* (expt 2 m) (land x (bits y (1- n) m) (+ n (-
                                                                        m))))))
  :hints (("Goal" :use land_alt-with-shifted-arg)))

(defthm lior-with-shifted-arg
  (implies (and (bvecp y m)
                (bvecp x (- n m))
                (<= m n)
                (natp m)
                (integerp n))
           (= (lior (* (expt 2 m) x) y n)
              (+ (* (expt 2 m) x) y)))
  :rule-classes ()
  :hints (("Goal" :use lior_alt-with-shifted-arg)))

(defthmd land-expt
  (implies (and (natp n)
		(natp k)
		(< k n))
	   (equal (land x (expt 2 k) n)
		  (* (expt 2 k) (bitn x k))))
  :hints (("Goal" :use land_alt-expt)))

(defthm lior-expt
    (implies (and (natp n)
		  (natp k)
		  (< k n))
	     (= (lior x (expt 2 k) n)
		(+ (bits x (1- n) 0)
		   (* (expt 2 k) (- 1 (bitn x k))))))
  :rule-classes ()
  :hints (("Goal" :use lior_alt-expt)))

(defthmd lxor-expt
  (implies (and (natp n)
		(natp k)
		(< k n))
	   (equal (lxor x (expt 2 k) n)
		  (+ (bits x (1- n) 0)
                     (* (expt 2 k) (- 1 (* 2 (bitn x k)))))))
  :hints (("Goal" :use lxor_alt-expt)))

(defthm land-ones
  (equal (land (1- (expt 2 n)) x n)
	 (bits x (1- n) 0))
  :rule-classes nil
  :hints (("Goal" :use land_alt-ones)))

(defthm land-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
		(equal k (1- (expt 2 n))))
	   (equal (land k x n)
		  (bits x (1- n) 0)))
  :hints (("Goal" :use land_alt-ones-rewrite)))

(defthm lior-ones
  (implies (and (case-split (bvecp x n))
		(case-split (natp n)))
	   (equal (lior (1- (expt 2 n)) x n)
		  (1- (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use lior_alt-ones)))

(defthm lior-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
			      (quotep n)
			      (equal (cadr k) (1- (expt 2 (cadr n))))))
		(force (equal k (1- (expt 2 n))))
		(case-split (natp n))
		(case-split (bvecp x n)))
	   (equal (lior k x n)
		  (1- (expt 2 n))))
  :hints (("Goal" :use lior_alt-ones-rewrite)))

(defthm lxor-ones
  (implies (case-split (bvecp x n))
	   (equal (lxor (1- (expt 2 n)) x n)
		  (lnot x n)))
  :rule-classes ()
  :hints (("Goal" :use lxor_alt-ones)))

(defthm lxor-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
			      (quotep n)
			      (equal (cadr k) (1- (expt 2 (cadr n))))))
		(force (equal k (1- (expt 2 n))))
		(case-split (bvecp x n)))
	   (equal (lxor k x n)
		  (lnot x n)))
  :hints (("Goal" :use lxor_alt-ones-rewrite)))


;;;**********************************************************************
;;;                Algebraic Properties
;;;**********************************************************************

(defthm lnot-lnot
  (implies (and (case-split (natp n))
		(case-split (bvecp x n)))
	   (equal (lnot (lnot x n) n)
		  x))
    :hints (("Goal" :use lnot_alt-lnot_alt)))

(defthm land-commutative
  (equal (land y x n)
	 (land x y n))
    :hints (("Goal" :use land_alt-commutative)))

(defthm lior-commutative
  (equal (lior y x n)
	 (lior x y n))
    :hints (("Goal" :use lior_alt-commutative)))

(defthm lxor-commutative
  (equal (lxor y x n)
	 (lxor x y n))
    :hints (("Goal" :use lxor_alt-commutative)))

(defthm land-associative
  (equal (land (land x y n) z n)
	 (land x (land y z n) n))
    :hints (("Goal" :use land_alt-associative)))

(defthm lior-associative
  (equal (lior (lior x y n) z n)
	 (lior x (lior y z n) n))
    :hints (("Goal" :use lior_alt-associative)))

(defthm lxor-associative
  (equal (lxor (lxor x y n) z n)
	 (lxor x (lxor y z n) n))
    :hints (("Goal" :use lxor_alt-associative)))

(defthm land-commutative-2
  (equal (land y (land x z n) n)
	 (land x (land y z n) n))
    :hints (("Goal" :use land_alt-commutative-2)))

(defthm lior-commutative-2
  (equal (lior y (lior x z n) n)
	 (lior x (lior y z n) n))
    :hints (("Goal" :use lior_alt-commutative-2)))

(defthm lxor-commutative-2
  (equal (lxor y (lxor x z n) n)
	 (lxor x (lxor y z n) n))
    :hints (("Goal" :use lxor_alt-commutative-2)))

(defthm land-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (land x (land y z n) n)
		  (land (land x y n) z n)))
    :hints (("Goal" :use land_alt-combine-constants)))

(defthm lior-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (lior x (lior y z n) n)
		  (lior (lior x y n) z n)))
    :hints (("Goal" :use lior_alt-combine-constants)))

(defthm lxor-combine-constants
  (implies (syntaxp (and (quotep x) (quotep y) (quotep n)))
	   (equal (lxor x (lxor y z n) n)
		  (lxor (lxor x y n) z n)))
    :hints (("Goal" :use lxor_alt-combine-constants)))

(defthm land-self
  (equal (land x x n)
	 (bits x (1- n) 0))
    :hints (("Goal" :use land_alt-self)))

(defthm lior-self
  (implies (and (case-split (bvecp x n))
		(case-split (integerp n)))
	   (equal (lior x x n) x))
    :hints (("Goal" :use lior_alt-self)))

(defthm lxor-self
  (implies (case-split (bvecp x n))
	   (equal (lxor x x n) 0))
    :hints (("Goal" :use lxor_alt-self)))

(defthmd lior-land-1
  (equal (lior x (land y z n) n)
	 (land (lior x y n) (lior x z n) n))
    :hints (("Goal" :use lior_alt-land_alt-1)))

(defthmd lior-land-2
  (equal (lior (land y z n) x n)
	 (land (lior x y n) (lior x z n) n))
    :hints (("Goal" :use lior_alt-land_alt-2)))

(defthmd land-lior-1
  (equal (land x (lior y z n) n)
	 (lior (land x y n) (land x z n) n))
    :hints (("Goal" :use land_alt-lior_alt-1)))

(defthmd land-lior-2
  (equal (land (lior y z n) x n)
	 (lior (land x y n) (land x z n) n))
    :hints (("Goal" :use land_alt-lior_alt-2)))

(defthmd lior-land-lxor
  (equal (lior (land x y n) (lior (land x z n) (land y z n) n) n)
	 (lior (land x y n) (land (lxor x y n) z n) n))
    :hints (("Goal" :use lior_alt-land_alt-lxor_alt)))

(defthmd lxor-rewrite
  (equal (lxor x y n)
	 (lior (land x (lnot y n) n)
	       (land y (lnot x n) n)
	       n))
    :hints (("Goal" :use lxor_alt-rewrite)))

(defthmd lnot-lxor
  (equal (lnot (lxor x y n) n)
	 (lxor (lnot x n) y n))
    :hints (("Goal" :use lnot_alt-lxor_alt)))
