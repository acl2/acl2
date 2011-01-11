#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "super-ihs")

(defund carry (n x y)
  (logtail n (+ (loghead n x) (loghead n y))))

(local
 (encapsulate
  ()

(defun sum (x y c)
  (+ x y c))

(defthm sum-type
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c))
   (integerp (sum x y c)))
  :hints (("Goal" :in-theory (enable sum))))

(defun sumn (n x y c)
  (+ (loghead n x) (loghead n y) (loghead 1 c)))

(defthm sum-0
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c)
    (zp n))
   (equal (sumn n x y c) (logcar c)))
  :hints (("Goal" :in-theory (enable zp))))

(defun carry3 (n x y c)
  (logtail n (sumn n x y c)))

(defthm carry3-0
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c)
    (zp n))
   (equal (carry3 n x y c) (logcar c)))
  :hints (("Goal" :in-theory (enable zp))))

(defthm open-logtail
  (implies
   (and
    (integerp x)
    (not (zp n)))
   (equal (logtail n x)
	  (LOGTAIL (1- n) (LOGCDR x))))
  :hints (("Goal" :in-theory (enable logtail*))))

(defthm imod-2-reduction
  (implies
   (not (equal (imod x 2) 1))
   (equal (imod x 2) 0)))

(defthm oddp-implies-imod=1
  (implies
   (and
    (integerp x)
    (oddp x))
   (equal (imod x 2) 1))
  :hints (("Goal" :in-theory (enable ODDP ifix))))

(defthm evenp-implies-imod=0
  (implies
   (and
    (integerp x)
    (not (oddp x)))
   (equal (imod x 2) 0))
  :hints (("Goal" :in-theory (enable ODDP ifix))))

(defthmd carry1-reduction
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c))
   (equal (carry3 1 x y c)
	  (IF (OR (AND (ODDP x) (ODDP c))
		  (AND (ODDP X) (ODDP Y))
		  (AND (ODDP Y) (ODDP C))) 1 0)))
  :hints (("Goal" :in-theory (e/d (b-xor logcar loghead)
				  (imod)))))

(in-theory (disable carry3))

(defthmd logcdr-sumn-carry
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c))
   (equal (logcdr (sumn n x y c))
	  (if (zp n) 0
	    (sumn (1- n) (logcdr x) (logcdr y) (carry3 1 (logcar x) (logcar y) (logcar c))))))
  :hints (("Goal" :in-theory (enable ODDP-TO-LOGCAR zp carry1-reduction LOGCDR-OF-SUM))))

(defthmd logcdr-sum-carry
  (implies
   (and
    (integerp x)
    (integerp y)
    (unsigned-byte-p 1 c))
   (equal (logcdr (sum x y c))
	  (sum (logcdr x) (logcdr y) (carry3 1 (logcar x) (logcar y) (logcar c)))))
  :hints (("Goal" :in-theory (enable ODDP-TO-LOGCAR zp carry1-reduction LOGCDR-OF-SUM))))

(in-theory (disable sum sumn))
(in-theory (disable LOGTAIL-OF-LOGCDR))

(defthm open-carry
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c)
    (syntaxp (not (quotep n)))
    (not (zp n)))
   (equal (carry3 n x y c)
	  (carry3 (1- n) (logcdr x) (logcdr y) (carry3 1 (logcar x) (logcar y) (logcar c)))))
  :hints (("Goal" :in-theory (enable logcdr-sumn-carry logtail*)
	   :expand ((carry3 n x y c)
		    (carry3 (1- n) (logcdr x) (logcdr y) (carry3 1 (logcar x) (logcar y) (logcar c)))))))

(defun carry-type-induction (n x y c)
  (if (zp n) (list x y c)
    (carry-type-induction (1- n) (logcdr x) (logcdr y) (carry3 1 (logcar x) (logcar y) (logcar c)))))

(defthm carry3-type
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c)
    (natp n))
   (unsigned-byte-p 1 (carry3 n x y c)))
  :hints (("Goal" :induct (carry-type-induction n x y c))))

(defun loghead-sum-induction (m x y c)
  (if (zp m) (list x y c)
    (loghead-sum-induction (1- m) (logcdr x) (logcdr y) (carry3 1 (logcar x) (logcar y) (logcar c)))))

(defthm logtail-sum-carry
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp c)
    (unsigned-byte-p 1 c)
    (natp m))
   (equal (logtail m (sum x y c))
	  (sum (logtail m x) (logtail m y) (carry3 m (loghead m x) (loghead m y) (logcar c)))))
  :hints (("Goal" :in-theory (enable zp LOGCAR-IDENTITY logcdr-sum-carry)
	   :induct (loghead-sum-induction m x y c))))

))

(defthm carry-type
  (implies
   (and
    (integerp x)
    (integerp y)
    (natp n))
   (unsigned-byte-p 1 (carry n x y)))
  :hints (("Goal" :in-theory (enable carry carry3 sumn sum)
	   :use (:instance carry3-type
			   (c 0)))))

(defthm logtail-+-carry
  (implies
   (and
    (integerp x)
    (integerp y)
    (natp m))
   (equal (logtail m (+ x y))
	  (+ (logtail m x) (logtail m y)
	     (carry m x y))))
  :hints (("Goal" :in-theory (enable sum sumn carry carry3)
	   :use (:instance logtail-sum-carry
			   (c 0)))))

(theory-invariant
 (incompatible
  (:rewrite logtail-+-carry)
  (:definition carry)
  ))

(defthm carry-0
  (implies
   (natp n)
   (and
    (equal (carry n 0 y) 0)
    (equal (carry n x 0) 0)))
  :hints (("Goal" :in-theory (e/d (carry)
				  (logtail-+-carry)))))


#|

;; You will also want this nary congruence rule to simplify
;; expressions involving carry.

(defcongp+ carry-loghead-ctx
  (carry n x y)
  :cong ((x (equal a (loghead-ctx x :n n)))
	 (y (equal b (loghead-ctx y :n n))))
  :hyps (and (integerp x)
	     (integerp y)
	     (natp n))
  :hints (("Goal" :in-theory (e/d (carry)
				  (logtail-+-carry)))))

|#

