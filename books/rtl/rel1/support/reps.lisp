;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "logdefs")

(include-book "float")

(defun PLISTP (x)
  (if (consp x)
      (plistp (cdr x))
    (equal x ())))

(defun FORMATP (phi)
  (and (plistp phi)
       (= (len phi) 2)
       (integerp (car phi))
       (integerp (cadr  phi))
       (> (car phi) 0)
       (> (cadr phi) 0)))

(defun GET-SBITS (phi) (ifix (car phi)))
(defun GET-EBITS (phi) (ifix (cadr phi)))

(defun sgnf (z phi) (bitn z (+ (get-sbits phi) (get-ebits phi))))
(defun expf (z phi) (bits z (+ (get-sbits phi) (get-ebits phi) -1) (get-sbits phi)))
(defun sigf (z phi) (bits z (1- (get-sbits phi)) 0))

(defun NORMAL-ENCODING-P (z phi)
  (and (integerp z)
       (>= z 0)
       (>= (sigf z phi) (expt 2 (1- (get-sbits phi))))))

(local (defthm BITN-0-1
    (or (= (bitn x n) 0) (= (bitn x n) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn)))))

(local (defthm BITS-NAT
    (implies (and (integerp x) (>= x 0)
		  (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (bits x i j))
		  (>= (bits x i j) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance integerp-expt (n (1+ i)))
			(:instance integerp-expt (n j))
			(:instance expt-pos (x (1+ i)))
			(:instance expt-pos (x j))
			(:instance rem>=0 (m x) (n (expt 2 (1+ i))))
			(:instance fl-def (x (/ (rem x (expt 2 (1+ i))) (expt 2 j)))))))))

(local (defthm BITS<
    (implies (and (integerp x) (>= x 0)
		  (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (< (bits x i j) (expt 2 (- (1+ i) j))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance rem<n (m x) (n (expt 2 (1+ i))))
			(:instance expt-pos (x (- j)))
			(:instance expt-pos (x (1+ i)))
			(:instance integerp-expt (n (1+ i)))
			(:instance *-strongly-monotonic
				   (x (expt 2 (- j)))
				   (y (rem x (expt 2 (1+ i))))
				   (y+ (expt 2 (1+ i))))
			(:instance expo+ (m (1+ i)) (n (- j)))
			(:instance fl-def (x (/ (rem x (expt 2 (1+ i))) (expt 2 j)))))))))

(defthm NORMAL-ENCODING-LEMMA
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
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-0-1 (x z) (n (+ (get-sbits phi) (get-ebits phi))))
			(:instance bits<
				   (x z)
				   (i (+ (get-sbits phi) (get-ebits phi) -1))
				   (j (get-sbits phi)))
			(:instance bits-nat
				   (x z)
				   (i (+ (get-sbits phi) (get-ebits phi) -1))
				   (j (get-sbits phi)))
			(:instance bits<
				   (x z)
				   (i (1- (get-sbits phi)))
				   (j 0))
			(:instance bits-nat
				   (x z)
				   (i (1- (get-sbits phi)))
				   (j 0))))))

(defun DECODE (z phi)
  (* (if (= (sgnf z phi) 0) 1 -1)
     (sigf z phi)
     (expt 2 (+ (expf z phi) (- (expt 2 (1- (get-ebits phi)))) (- (get-sbits phi)) 2))))

(defun REPP (x phi)
  (and (exactp x (get-sbits phi))
       (<= (- 1 (expt 2 (1- (get-ebits phi))))
	   (expo x))
       (<= (expo x)
	   (expt 2 (1- (get-ebits phi))))))

(defun ENCODE (x phi)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    (+ (expo x) (1- (expt 2 (1- (get-ebits phi)))))
	    (get-ebits phi))
       (* (sig x) (expt 2 (1- (get-sbits phi))))
       (get-sbits phi)))

(local
(defthm code-1
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (decode z phi)
		(* (if (= (sgnf z phi) 0) 1 -1)
		   (* (sigf z phi) (expt 2 (- 1 (get-sbits phi))))
		   (expt 2 (- (expf z phi) (1- (expt 2 (1- (get-ebits phi)))))))))
  :rule-classes ()))

(local
(defthm code-2
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (abs (decode z phi))
		(* (* (sigf z phi) (expt 2 (- 1 (get-sbits phi))))
		   (expt 2 (- (expf z phi) (1- (expt 2 (1- (get-ebits phi)))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable decode)
		  :use (code-1 normal-encoding-lemma)))))

(local
(defthm code-3
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (<= 1 (* (sigf z phi) (expt 2 (- 1 (get-sbits phi))))))
  :rule-classes ()))

(local
(defthm code-4
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (> 2 (* (sigf z phi) (expt 2 (- 1 (get-sbits phi))))))
  :rule-classes ()
  :hints (("Goal" :use (normal-encoding-lemma)))))

(defthm NORMAL-NON-ZERO
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (not (equal (decode z phi) 0)))
  :hints (("Goal" :use (normal-encoding-lemma))))

(local
(defthm code-5
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (and (= (sig (decode z phi)) (* (sigf z phi) (expt 2 (- 1 (get-sbits phi)))))
		  (= (expo (decode z phi)) (- (expf z phi) (1- (expt 2 (1- (get-ebits phi))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable decode normal-encoding-p)
		  :use ((:instance fp-rep-unique
				   (x (decode z phi))
				   (m (* (sigf z phi) (expt 2 (- 1 (get-sbits phi)))))
				   (e (- (expf z phi) (1- (expt 2 (1- (get-ebits phi)))))))
			(:instance code-4)
			(:instance code-2)
			(:instance code-3))))))

(local (IN-THEORY (disable expf get-ebits sigf get-sbits sgnf)))

(local
(defthm code-6
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (decode z phi)
		(* (if (= (sgnf z phi) 0) 1 -1)
		   (sig (decode z phi))
		   (expt 2 (expo (decode z phi))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo a15 a2 formatp normal-encoding-p decode)
		  :use (normal-encoding-lemma
			code-1
			code-5
			(:instance expo+
				   (m (+ 1 (- (GET-SBITS PHI))))
				   (n (+ (- (+ -1 (EXPT 2 (+ -1 (GET-EBITS PHI)))))
					 (EXPF Z PHI)))))))))

(defthm CODE-A
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (sgn (decode z phi))
		(if (= (sgnf z phi) 0) 1 -1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable decode formatp normal-non-zero normal-encoding-p)
		  :use ((:instance fp-rep (x (decode z phi)))
			(:instance normal-non-zero)
			(:instance code-6)))))

(defthm CODE-B
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (sig (decode z phi))
		(* (sigf z phi) (expt 2 (- 1 (get-sbits phi))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable decode formatp normal-encoding-p)
		  :use ((:instance code-5)))))

(defthm CODE-C
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (= (expo (decode z phi))
		(- (expf z phi) (1- (expt 2 (1- (get-ebits phi)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable decode formatp normal-encoding-p)
		  :use ((:instance code-5)))))

(defthm EXACTP-DECODE
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (exactp (decode z phi) (get-sbits phi)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable formatp normal-encoding-p decode)
		  :use ((:instance code-b)
			(:instance exactp (x (decode z phi)) (n (get-sbits phi)))))))

(local (in-theory (disable expo)))

(local
(defthm expt+expt
    (implies (integerp n)
	     (= (expt 2 n) (+ (expt 2 (1- n)) (expt 2 (1- n)))))
  :rule-classes ()))

(local
(defthm bad-hack
    (implies (and (integerp e)
		  (integerp h)
		  (integerp z)
		  (< e (* 2 h))
		  (= (+ h z) (+ 1 e)))
	     (<= z h))
  :rule-classes ()))

(local (in-theory (enable get-ebits get-sbits)))

(defthm CODE-D
    (implies (and (formatp phi)
		  (normal-encoding-p z phi))
	     (repp (decode z phi) phi))
  :rule-classes ()
  :hints (("Goal" :in-theory  (disable normal-encoding-p decode)
		  :use ((:instance exactp-decode)
			(:instance bad-hack
				   (h (expt 2 (1- (get-ebits phi))))
				   (e (expf z phi))
				   (z (expo (decode z phi))))
			(:instance expt+expt (n (get-ebits phi)))
			(:instance normal-encoding-lemma)
			(:instance code-c)))))