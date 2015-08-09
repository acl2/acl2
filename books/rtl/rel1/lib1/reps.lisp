;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/proofs"))

(include-book "float")

(defun bitn (x n)
  (if (logbitp n x) 1 0))

(in-theory (disable bitn))


;;;**********************************************************************
;;;                    Floating-Point Representation
;;;**********************************************************************

(defun plistp (x)
  (if (consp x)
      (plistp (cdr x))
    (equal x ())))

(defun formatp (phi)
  (and (plistp phi)
       (= (len phi) 2)
       (integerp (car phi))
       (integerp (cadr  phi))
       (> (car phi) 0)
       (> (cadr phi) 0)))

(defun get-sbits (phi) (ifix (car phi)))
(defun get-ebits (phi) (ifix (cadr phi)))

(defun sgnf (z phi) (bitn z (+ (get-sbits phi) (get-ebits phi))))
(defun expf (z phi) (bits z (+ (get-sbits phi) (get-ebits phi) -1) (get-sbits phi)))
(defun sigf (z phi) (bits z (1- (get-sbits phi)) 0))

(defun normal-encoding-p (z phi)
  (and (integerp z)
       (>= z 0)
       (>= (sigf z phi) (expt 2 (1- (get-sbits phi))))))

(defthm normal-encoding-lemma
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (and (or (= (sgnf z phi) 0)
		      (= (sgnf z phi) 1))
		  (integerp (expf z phi))
		  (>= (expf z phi) 0)
		  (< (expf z phi) (expt 2 (get-ebits phi)))
		  (integerp (sigf z phi))
		  (>= (sigf z phi) 0)
		  (< (sigf z phi) (expt 2 (get-sbits phi)))))
  :rule-classes ())

(defun decode (z phi)
  (* (if (= (sgnf z phi) 0) 1 -1)
     (sigf z phi)
     (expt 2 (+ (expf z phi) (- (expt 2 (1- (get-ebits phi)))) (- (get-sbits phi)) 2))))

(defun repp (x phi)
  (and (exactp x (get-sbits phi))
       (<= (- 1 (expt 2 (1- (get-ebits phi))))
	   (expo x))
       (<= (expo x)
	   (expt 2 (1- (get-ebits phi))))))

(defun cat (x y n)
  (+ (* (expt 2 n) x) y))

(defun encode (x phi)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    (+ (expo x) (1- (expt 2 (1- (get-ebits phi)))))
	    (get-ebits phi))
       (* (sig x) (expt 2 (1- (get-sbits phi))))
       (get-sbits phi)))

(defthm normal-non-zero
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (not (equal (decode z phi) 0))))

(defthm code-a
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (sgn (decode z phi))
		(if (= (sgnf z phi) 0) 1 -1)))
  :rule-classes ())

(defthm code-b
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (sig (decode z phi))
		(* (sigf z phi) (expt 2 (- 1 (get-sbits phi))))))
  :rule-classes ())

(defthm code-c
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (expo (decode z phi))
		(- (expf z phi) (1- (expt 2 (1- (get-ebits phi)))))))
  :rule-classes ())

(defthm exactp-decode
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (exactp (decode z phi) (get-sbits phi)))
  :rule-classes ())

(defthm code-d
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (repp (decode z phi) phi))
  :rule-classes ())
