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

; (set-enforce-redundancy t)

(include-book "bits-new")

(local (include-book "log-new-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
;;
;; (local (in-theory nil))




;;;**********************************************************************
;;;                       LOGNOT, LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(in-theory (disable lognot logand logior logxor))


(defthmd lognot-def
    (implies (integerp x)
	     (equal (lognot x)
		    (1- (- x)))))

(defthmd logand-def
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (logand i j)
		    (+ (* 2 (logand (fl (* 1/2 i)) (fl (* 1/2 j))))
		       (logand (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logand t t)))))

(defthmd logior-def
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (logior i j)
		    (+ (* 2 (logior (fl (* 1/2 i)) (fl (* 1/2 j))))
		       (logior (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logior t t)))))


(defthmd logxor-def
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (logxor i j)
		    (+ (* 2 (logxor (fl (* 1/2 i)) (fl (* 1/2 j))))
		       (logxor (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logxor t t)))))


(defthm logand-natp
    (implies (and (natp i)
		  (integerp j))
	     (natp (logand i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm logand-natp-2
    (implies (and (integerp i)
		  (natp j))
	     (natp (logand i j)))
  :rule-classes (:type-prescription :rewrite))

;;;

(defthm logand-bvecp-g
    (implies (and (natp n)
		  (bvecp x n)
		  (integerp y))
	     (bvecp (logand x y) n)))

(defthm logior-natp
    (implies (and (natp i)
		  (natp j))
	     (natp (logior i j)))
  :rule-classes (:type-prescription :rewrite))


(defthm logior-bvecp
     (implies (and (bvecp x n)
                   (bvecp y n))
 	     (bvecp (logior x y) n)))

(defthm logxor-natp
    (implies (and (natp i)
		  (natp j))
	     (natp (logxor i j)))
  :rule-classes (:type-prescription :rewrite))

(defthm logxor-bvecp
    (implies (and (bvecp x n)
 		  (bvecp y n)
                  (natp n))
 	     (bvecp (logxor x y) n)))

(defun logop-2-induct-g (x y)
  (declare (xargs :measure (+ (nfix (abs x)) (nfix (abs y)))))
  (if (and (integerp x) (integerp y))
      (if (and (or (equal x 0)
                   (equal x -1))
               (or (equal y 0)
                   (equal y -1)))
          t
        (logop-2-induct-g (fl (/ x 2)) (fl (/ y 2))))
    t))

(defun logop-2-n-induct (x y n)
  (if (zp n)
      (cons x y)
    (logop-2-n-induct (fl (/ x 2)) (fl (/ y 2)) (1- n))))



;; (defun logop-3-induct (x y z)
;;   (DECLARE (XARGS :MEASURE (:? X Y Z)))
;;   (if (and (natp x) (natp y) (natp z))
;;       (if (and (zp x) (zp y) (zp z))
;; 	  t
;; 	(logop-3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
;;     t))


(defun logop-3-induct-g (x y z)
  (declare (xargs :measure (+ (nfix (abs x)) (nfix (abs y)) (nfix (abs z)))))
  (if (and (integerp x) (integerp y) (integerp z))
      (if (and (or (equal x 0)
                   (equal x -1))
               (or (equal y 0)
                   (equal y -1))
               (or (equal z 0)
                   (equal z -1)))
	  t
	(logop-3-induct-g (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    t))


(defthmd logand-fl-2-rewrite
    (implies (and (natp x)
		  (natp y))
	     (equal (fl (* 1/2 (logand x y)))
		    (logand (fl (* 1/2 x)) (fl (* 1/2 y))))))

(defthmd logior-fl-2-rewrite
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (* 1/2 (logior i j)))
		    (logior (fl (* 1/2 i)) (fl (* 1/2 j))))))

(defthmd logxor-fl-2-rewrite
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (* 1/2 (logxor i j)))
		    (logxor (fl (* 1/2 i)) (fl (* 1/2 j))))))

(defthm logior-not-0
    (implies (and (integerp x)
		  (integerp y)
		  (= (logior x y) 0))
	     (and (= x 0) (= y 0)))
  :rule-classes ())


(defthm logior-expt-g
  (implies (and (natp n)
                (integerp x)
                (bvecp y n))
           (= (logior (* (expt 2 n) x) y)
              (+ (* (expt 2 n) x) y)))
  :rule-classes ())


(defthm logior-expt-2-g
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n) (logior x y))))
  :rule-classes ())



(defthm logand-bnd
    (implies (<= 0 x)
	     (<= (logand x y) x))
  :rule-classes :linear)

(defthm logand-expt-g
    (implies (and (integerp x)
		  (integerp y)
		  (natp n))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ())

(defthmd bitn_alt-lognot
    (implies (and (integerp x)
		  (integerp n)
		  (> n 0)) ;; ?? n = 0?
	     (not (equal (bitn_alt (lognot x) n)
			 (bitn_alt x n)))))

(defthmd bitn_alt-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn_alt (logand x y) n)
		    (logand (bitn_alt x n) (bitn_alt y n)))))


(defthmd bits_alt-logand
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i)
		  (integerp j))
	     (equal (bits_alt (logand x y) i j)
		    (logand (bits_alt x i j) (bits_alt y i j)))))


(defthmd bitn_alt-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n))
	     (equal (bitn_alt (logior x y) n)
		    (logior (bitn_alt x n) (bitn_alt y n)))))


(defthmd bits_alt-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i)
		  (integerp j))
	     (equal (bits_alt (logior x y) i j)
		    (logior (bits_alt x i j) (bits_alt y i j)))))



(defthmd bitn_alt-logxor
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                (case-split (integerp n)))
           (equal (bitn_alt (logxor x y) n)
                  (logxor (bitn_alt x n) (bitn_alt y n)))))


(defthmd bits_alt-logxor
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                (case-split (integerp i))
                (case-split (integerp j)))
           (equal (bits_alt (logxor x y) i j)
                  (logxor (bits_alt x i j) (bits_alt y i j)))))



(defthmd logand-expt-2-g
    (implies (and (integerp x)
		  (natp k))
	     (equal (logand x (expt 2 k))
		    (* (expt 2 k) (bitn_alt x k)))))

(defthmd logior-expt-3-g
    (implies (and (integerp x)
		  (natp k))
	     (equal (logior x (expt 2 k))
		    (+ x
		       (* (expt 2 k)
			  (- 1 (bitn_alt x k)))))))

;; (defthmd logand-expt-3-g
;;     (implies (and (integerp x)
;; 		  (natp n)
;; 		  (natp k)
;; 		  (< k n))
;; 	     (equal (logand x (- (expt 2 n) (expt 2 k)))
;; 		    (* (expt 2 k) (bits_alt x (1- n) k)))))

(defthmd logand-expt-3-g
    (implies (and (integerp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (equal (logand x (+ (expt 2 n) (- (expt 2 k))))
		    (* (expt 2 k) (bits_alt x (1- n) k)))))



;;; not very good. as a rewrite rule.

;; (defthmd lognot-shift
;;   (implies (and (integerp x)
;;                 (natp k))
;;            (equal (lognot (* (expt 2 k) x))
;; 		  (+ (* (expt 2 k) (lognot x))
;; 		     (1- (expt 2 k)))))


(defthmd lognot-shift
  (implies (and (integerp x)
                (natp k))
           (equal (lognot (* (expt 2 k) x))
		  (+ (* (expt 2 k) (lognot x))
		     (1- (expt 2 k))))))

(defthmd logand-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logand (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logand x y)))))

(defthmd logxor-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logxor (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logxor x y)))))

(defthmd logior-shift
    (implies (and (integerp x)
		  (integerp y)
		  (natp k))
	     (equal (logior (* (expt 2 k) x)
			    (* (expt 2 k) y))
		    (* (expt 2 k) (logior x y)))))

(defthmd fl-lognot
    (implies (case-split (integerp i))
	     (= (fl (* 1/2 (lognot i)))
                (lognot (fl (* 1/2 i))))))

(defthmd fl-logand
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k))
           (equal (fl (/ (logand x y) (expt 2 k)))
                  (logand (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k)))))))

(defthmd fl-logior
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k))
           (equal (fl (/ (logior x y) (expt 2 k)))
                  (logior (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k)))))))

(defthmd fl-logxor
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (natp k))
           (equal (fl (/ (logxor x y) (expt 2 k)))
                  (logxor (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k)))))))


;;;**********************************************************************
;;;                Algebraic Properties
;;;**********************************************************************

(defthm lognot-lognot
    (implies (case-split (integerp i))
	     (equal (lognot (lognot i))
		    i)))

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logior-x-0
    (implies (integerp x)
	     (equal (logior x 0) x)))

(defthm logior-0-y
    (implies (integerp y)
	     (equal (logior 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logand-self
  (implies (case-split (integerp i))
           (equal (logand i i) i)))

(defthm logior-self
    (implies (case-split (integerp i))
	     (equal (logior i i) i)))

(defthm logxor-self
  (equal (logxor i i) 0))

(defthm logand-x-m1
    (implies (integerp x)
	     (equal (logand x -1) x)))

(defthm logand-m1-y
    (implies (integerp y)
	     (equal (logand -1 y) y)))

(defthm logand-x-1
    (implies (bvecp x 1)
	     (equal (logand x 1) x)))

(defthm logand-1-x
    (implies (bvecp x 1)
	     (equal (logand 1 x) x)))

(defthm logior-x-m1
    (implies (integerp x)
	     (equal (logior x -1) -1)))

(defthm logior-m1-y
    (implies (integerp y)
	     (equal (logior -1 y) -1)))

(defthm logior-1-x
  (implies (bvecp x 1)
           (equal (logior 1 x) 1)))

;;; not really necessary.
(defthm logior-x-1
  (implies (bvecp x 1)
           (equal (logior x 1) 1)))

(defthm logxor-m1
    (implies (integerp x)
	     (equal (logxor x -1)
		    (lognot x))))

(defthm logand-commutative
    (equal (logand j i) (logand i j)))

(defthm logior-commutative
    (equal (logior j i) (logior i j)))

(defthm logxor-commutative
    (equal (logxor j i) (logxor i j)))

(defthm logand-associative
    (equal (logand (logand i j) k)
           (logand i (logand j k))))

(defthm logior-associative
    (equal (logior (logior i j) k)
	   (logior i (logior j k))))

(defthm logxor-associative
    (equal (logxor (logxor i j) k)
	   (logxor i (logxor j k))))

(defthm logand-commutative-2
  (equal (logand j i k)
	 (logand i j k)))


(defthm logior-commutative-2
  (equal (logior j i k)
	 (logior i j k)))

(defthm logxor-commutative-2
  (equal (logxor j i k)
	 (logxor i j k)))

(defthmd lognot-logxor
  (and (equal (logxor (lognot i) j)
              (lognot (logxor i j)))
       (equal (logxor j (lognot i))
              (lognot (logxor i j)))))


(defthmd logior-logand-g
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logior x (logand y z))
	   (logand (logior x y) (logior x z)))))

(defthmd logand-logior-g
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logand x (logior y z))
                  (logior (logand x y) (logand x z)))))

(defthmd logior-logand-2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (logand  (logior y z) x)
                  (logior (logand y x) (logand z x)))))

(defthmd log3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
    (equal (logior (logand x y) (logior (logand x z) (logand y z)))
	   (logior (logand x y) (logand (logxor x y) z)))))

(defthmd logxor-rewrite-2-g
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand y (lognot x))))))





