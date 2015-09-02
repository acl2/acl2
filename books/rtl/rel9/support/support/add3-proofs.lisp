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

(include-book "merge")
(local (include-book "bitn"))
(local (include-book "bits"))
(local (include-book "../../arithmetic/top"))
;(local (include-book "../../arithmetic/mod"))

(defun add3-measure (x y z)
  (acl2-count (+ x y z)))

(defthm add3-1
    (implies (and (integerp x)
		  (> x 0))
	     (and (>= (fl (/ x 2)) 0)
		  (< (fl (/ x 2)) x)))
  :rule-classes ())

(defthm recursion-by-add3-measure
    (IMPLIES (AND (INTEGERP X)
		  (<= 0 X)
		  (INTEGERP Y)
		  (<= 0 Y)
		  (INTEGERP Z)
		  (<= 0 Z)
		  (NOT (AND (EQUAL X 0)
			    (EQUAL Y 0)
			    (EQUAL Z 0))))
	     (e0-ord-< (ADD3-MEASURE (FL (* 1/2 x))
				     (FL (* 1/2 y))
				     (FL (* 1/2 z)))
		       (ADD3-MEASURE X Y Z)))
  :hints (("Goal" :use ((:instance add3-1)
			(:instance add3-1 (x y))
			(:instance add3-1 (x z))))))

(in-theory (disable add3-measure))

(include-book "ordinals/e0-ordinal" :dir :system)

(set-well-founded-relation e0-ord-<)

(defun add3-induct (x y z)
  (declare (xargs :measure (add3-measure x y z)))
  (if (and (integerp x) (>= x 0)
	   (integerp y) (>= y 0)
	   (integerp z) (>= z 0))
      (if (and (= x 0) (= y 0) (= z 0))
	  ()
	(add3-induct (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
    ()))

(in-theory (disable logand logior logxor))

(defthm add3-2
    (implies (and (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
;		  (<= 0 Y)
		  (INTEGERP Z)
	;	  (<= 0 Z)
                  )
	     (= (LOGXOR (FL (* X 1/2))
			(LOGXOR (FL (* Y 1/2)) (FL (* Z 1/2))))
		(fl (/ (logxor x (logxor y z)) 2))))
  :rule-classes())

(defthm add3-3
    (implies (and (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
	;	  (<= 0 Y)
		  (INTEGERP Z)
		;  (<= 0 Z)
                  )
	     (= (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Y 1/2)))
			(LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Z 1/2)))
				(LOGAND (FL (* Y 1/2)) (FL (* Z 1/2)))))
		(fl (/ (logior (logand x y)
			       (logior (logand x z) (logand y z)))
		       2))))
  :rule-classes())

(defthm add3-4
    (IMPLIES (AND (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
;		  (<= 0 Y)
		  (INTEGERP Z)
;		  (<= 0 Z)
;		  (NOT (AND (= X 0) (= Y 0) (= Z 0)))
		  (IMPLIES (AND (INTEGERP (FL (* X 1/2)))
;				(<= 0 (FL (* X 1/2)))
				(INTEGERP (FL (* Y 1/2)))
;				(<= 0 (FL (* Y 1/2)))
				(INTEGERP (FL (* Z 1/2)))
	;			(<= 0 (FL (* Z 1/2)))
                                )
			   (= (+ (FL (* X 1/2))
				 (FL (* Y 1/2))
				 (FL (* Z 1/2)))
			      (+ (LOGXOR (FL (* X 1/2))
					 (LOGXOR (FL (* Y 1/2)) (FL (* Z 1/2))))
				 (* 2
				    (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Y 1/2)))
					    (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Z 1/2)))
						    (LOGAND (FL (* Y 1/2))
							    (FL (* Z 1/2))))))))))
	     (= (+ (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2)))
		(+ (fl (/ (logxor x (logxor y z)) 2))
		   (* 2 (fl (/ (logior (logand x y) (logior (logand x z) (logand y z))) 2))))))
  :rule-classes ()
  :hints (("Goal" :use (add3-2 add3-3))))

(defthm add3-5
    (IMPLIES (AND (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
	;	  (<= 0 Y)
		  (INTEGERP Z)
;		  (<= 0 Z)
                  )
	     (= (fl (/ (+ (bitn x 0) (bitn y 0) (bitn z 0)) 2))
		(bitn (logior (logand x y) (logior (logand x z) (logand y z))) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-logior)
           :use ((:instance bitn-0-1 (n 0))
			(:instance bitn-0-1 (n 0) (x y))
			(:instance bitn-0-1 (n 0) (x z))
			(:instance bitn-0-1 (n 0))
                        ))))

(defthm add3-6
    (IMPLIES (AND (INTEGERP X)
		;  (<= 0 X)
		  (INTEGERP Y)
;		  (<= 0 Y)
		  (INTEGERP Z)
;		  (<= 0 Z)
                  )
	     (= (bitn (+ x y z) 0)
		(bitn (logxor x (logxor y z)) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-logxor-0 (a x) (b (+ y z)))
			(:instance bitn-logxor-0 (a y) (b z))
			(:instance bitn-logxor (n 0) (y (+ y z)))
			(:instance bitn-logxor (n 0) (y (logxor y z)))
	;		(:instance logxor-nat (i y) (j z))
                        ))))

(defthm add3-7
    (IMPLIES (AND (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
;		  (<= 0 Y)
		  (INTEGERP Z)
	;	  (<= 0 Z)
                  )
	     (= (fl (/ (+ x y z) 2))
		(fl (+ (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2)) (/ (+ (bitn x 0) (bitn y 0) (bitn z 0)) 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-def)
		  :use ((:instance quot-mod (n 2) (m x))
			(:instance quot-mod (n 2) (m y))
			(:instance quot-mod (n 2) (m z))))))

(defthm add3-8
    (IMPLIES (AND (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
	;	  (<= 0 Y)
		  (INTEGERP Z)
		;  (<= 0 Z)
                  )
	     (= (fl (/ (+ x y z) 2))
		(+ (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))
		   (fl (/ (+ (bitn x 0) (bitn y 0) (bitn z 0)) 2)))))
  :rule-classes ()
  :hints (("Goal" :use (add3-7
			(:instance fl+int-rewrite
				   (x (/ (+ (bitn x 0) (bitn y 0) (bitn z 0)) 2))
				   (n (+ (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2)))))))))

(defthm add3-9
    (IMPLIES (AND (INTEGERP X)
;		  (<= 0 X)
		  (INTEGERP Y)
	;	  (<= 0 Y)
		  (INTEGERP Z)
		;  (<= 0 Z)
;		  (NOT (AND (= X 0) (= Y 0) (= Z 0)))
		  (IMPLIES (AND (INTEGERP (FL (* X 1/2)))
			;	(<= 0 (FL (* X 1/2)))
				(INTEGERP (FL (* Y 1/2)))
				;(<= 0 (FL (* Y 1/2)))
				(INTEGERP (FL (* Z 1/2)))
;(<= 0 (FL (* Z 1/2)))
                                )
			   (= (+ (FL (* X 1/2))
				 (FL (* Y 1/2))
				 (FL (* Z 1/2)))
			      (+ (LOGXOR (FL (* X 1/2))
					 (LOGXOR (FL (* Y 1/2)) (FL (* Z 1/2))))
				 (* 2
				    (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Y 1/2)))
					    (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Z 1/2)))
						    (LOGAND (FL (* Y 1/2))
							    (FL (* Z 1/2))))))))))
	     (= (fl (/ (+ x y z) 2))
		(+ (fl (/ (logxor x (logxor y z)) 2))
		   (* 2 (fl (/ (logior (logand x y) (logior (logand x z) (logand y z))) 2)))
		   (bitn (logior (logand x y) (logior (logand x z) (logand y z))) 0))))
  :rule-classes ()
  :hints (("Goal" :use (add3-4 add3-5 add3-8))))

(defthm add3-10
    (IMPLIES (AND (INTEGERP X)
	;	  (<= 0 X)
		  (INTEGERP Y)
;		  (<= 0 Y)
		  (INTEGERP Z)
	;	  (<= 0 Z)
;		  (NOT (AND (= X 0) (= Y 0) (= Z 0)))
		  (IMPLIES (AND (INTEGERP (FL (* X 1/2)))
;				(<= 0 (FL (* X 1/2)))
				(INTEGERP (FL (* Y 1/2)))
;				(<= 0 (FL (* Y 1/2)))
				(INTEGERP (FL (* Z 1/2)))
	;			(<= 0 (FL (* Z 1/2)))
                                )
			   (= (+ (FL (* X 1/2))
				 (FL (* Y 1/2))
				 (FL (* Z 1/2)))
			      (+ (LOGXOR (FL (* X 1/2))
					 (LOGXOR (FL (* Y 1/2)) (FL (* Z 1/2))))
				 (* 2
				    (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Y 1/2)))
					    (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Z 1/2)))
						    (LOGAND (FL (* Y 1/2))
							    (FL (* Z 1/2))))))))))
	     (= (fl (/ (+ x y z) 2))
		(+ (fl (/ (logxor x (logxor y z)) 2))
		   (logior (logand x y) (logior (logand x z) (logand y z))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-def)
		  :use (add3-9
			(:instance quot-mod
				   (m (logior (logand x y) (logior (logand x z) (logand y z))))
				   (n 2))
                                   ))))

(defthm add3-11
  (IMPLIES (AND (INTEGERP X)
                (INTEGERP Y)
                (INTEGERP Z)
;                (NOT (AND (= X 0) (= Y 0) (= Z 0)))
                (IMPLIES (AND (INTEGERP (FL (* X 1/2)))
                              (INTEGERP (FL (* Y 1/2)))
                              (INTEGERP (FL (* Z 1/2)))
                              )
                         (= (+ (FL (* X 1/2))
                               (FL (* Y 1/2))
                               (FL (* Z 1/2)))
                            (+ (LOGXOR (FL (* X 1/2))
                                       (LOGXOR (FL (* Y 1/2)) (FL (* Z 1/2))))
                               (* 2
                                  (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Y 1/2)))
                                          (LOGIOR (LOGAND (FL (* X 1/2)) (FL (* Z 1/2)))
                                                  (LOGAND (FL (* Y 1/2))
                                                          (FL (* Z 1/2))))))))))
           (= (+ X Y Z)
              (+ (LOGXOR X (LOGXOR Y Z))
                 (* 2
                    (LOGIOR (LOGAND X Y)
                            (LOGIOR (LOGAND X Z)
                                    (LOGAND Y Z)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bitn-def)
           :use (add3-10
                 add3-6
                 (:instance quot-mod (n 2) (m (+ x y z)))
;			(:instance logxor-nat (i x) (j (logxor y z)))
;		(:instance logxor-nat (i y) (j z))
                 (:instance quot-mod (n 2) (m (logxor x (logxor y z))))))))


;begin Eric's additions
(defun add3-measure-neg (x y z)
  (acl2-count (+ (abs x) (abs y) (abs z))))

(local (include-book "../../arithmetic/arith2"))

(defthm fl-sum-non-neg
  (implies (and (<= 0 x)
                (<= 0 y)
                (<= 0 z)
                (rationalp x)
                (rationalp y)
                (rationalp z)
                )
           (<= 0
           (+ (FL (* 1/2 X))
              (FL (* 1/2 Y))
              (FL (* 1/2 Z))))))

#|
(defthm add3-1-neg
    (implies (and (integerp x)
		  (< x 0))
	     (and (<= (fl (/ x 2)) 0)
		  (>= (fl (/ x 2)) x)))
  :rule-classes ())
|#

;BOZO contains the seed of a nice rule?
(defthm add3-1-neg-2
    (implies (and (< x 0)
                  (integerp x)
		  )
	     (and (<= (fl (* 1/2 x)) 0)
		  (>= (fl (* 1/2 x)) x)))
  :rule-classes :linear)



;why so many cases?
(defthm recursion-by-add3-measure-neg
    (IMPLIES (AND (INTEGERP X)
		  (INTEGERP Y)
		  (INTEGERP Z)
		  (not (and (or (EQUAL X 0) (EQUAL X -1))
                            (or (EQUAL y 0) (EQUAL y -1))
                            (or (EQUAL z 0) (EQUAL z -1))
                       )))
	     (e0-ord-< (ADD3-MEASURE-neg (FL (* 1/2 x))
                                         (FL (* 1/2 y))
                                         (FL (* 1/2 z)))
		       (ADD3-MEASURE-neg X Y Z)))
    :otf-flg t
  :hints (("Goal" :in-theory (disable ;FL-STRONG-MONOTONE ;BOZO these disables are unfortunate..
                                      ;FL-WEAK-MONOTONE
;                                      FL-<=-Y
                        ;              FL->-INTEGER ;for efficiency
                         ;             fl-<-integer
                                      ;fl-def-linear-part-1
                                      )

           :use (;(:instance add3-1-neg) ;BOZO if these are put back, things get really slow..
                 ;(:instance add3-1-neg (x y))
                 ;(:instance add3-1-neg (x z))
                 ))))

(DEFUN ADD3-INDUCT-allow-negatives (X Y Z)
  (DECLARE (XARGS   :hints (("Goal" :use recursion-by-add3-measure-neg
                             ))
                    :MEASURE (ADD3-MEASURE-neg X Y Z)))
  (IF (AND (INTEGERP X)
           (INTEGERP Y)
           (INTEGERP Z)
           )
      (IF (and (or (EQUAL X 0) (EQUAL X -1))
               (or (EQUAL y 0) (EQUAL y -1))
               (or (EQUAL z 0) (EQUAL z -1))
               )
          NIL
          (ADD3-INDUCT-allow-negatives
           (FL (/ X 2))
           (FL (/ Y 2))
           (FL (/ Z 2))))
      NIL)

  )


(defthm add-3-old
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                )
           (equal (+ x y z)
                  (+ (logxor x (logxor y z))
                     (* 2 (logior (logand x y)
                                  (logior (logand x z)
                                          (logand y z)))))))
  :rule-classes ()
  :hints (("Goal" :induct (ADD3-INDUCT-allow-negatives x y z))
	  ("Subgoal *1/2" :use (add3-11))))

(include-book "land0")
(include-book "lior0")
(include-book "lxor0")

(in-theory (enable bits-tail))

(defthm add-3-original
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n)
                (bvecp z n))
           (equal (+ x y z)
                  (+ (lxor0 x (lxor0 y z n) n)
                     (* 2 (lior0 (land0 x y n)
                                (lior0 (land0 x z n)
                                      (land0 y z n)
                                      n)
                                n)))))
  :rule-classes ()
  :hints (("Goal" :use (add-3-old)
           :in-theory (enable lxor0 lior0 land0 bvecp))))

(defthm add-2-original
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n))
           (equal (+ x y)
                  (+ (lxor0 x y n)
                     (* 2 (land0 x y n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
           :use ((:instance add-3-original (z 0))))))
