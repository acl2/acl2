(in-package "ACL2")

(include-book "polynomial-defuns")

(local (include-book "arithmetic-5/top" :dir :system))

(defthmd eval-polynomial-expt-correct-lemma
  (implies (and (real-polynomial-p poly)
		(realp x)
		(integerp n)
		(<= 0 n))
	   (equal (eval-polynomial-expt-aux poly x n)
		  (* (expt x n)
		     (eval-polynomial poly x)))))

(defthmd eval-polynomial-expt-correct
  (implies (and (real-polynomial-p poly)
		(realp x))
	   (equal (eval-polynomial-expt poly x)
		  (eval-polynomial poly x)))
  :hints (("Goal"
	   :use ((:instance eval-polynomial-expt-correct-lemma
			    (n 0))))))

(defthm real-polynomial-scale-polynomial
  (implies (and (real-polynomial-p poly)
		(realp c))
	   (real-polynomial-p (scale-polynomial poly c))))

(defthm eval-scale-polynomial
  (implies (and (real-polynomial-p poly)
		(realp c))
	   (equal (eval-polynomial (scale-polynomial poly c) x)
		  (* c (eval-polynomial poly x)))))

(defthm eval-scale-expt-polynomial
  (implies (and (real-polynomial-p poly)
		(realp c)
		(realp x))
	   (equal (eval-polynomial-expt (scale-polynomial poly c) x)
		  (* c (eval-polynomial-expt poly x))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (eval-polynomial-expt-correct)
			   (eval-polynomial-expt
			    scale-polynomial)))))


(defthm consp-scale-polnomial
  (equal (consp (scale-polynomial poly c))
	 (consp poly)))

(defthm real-polynomial-+
  (implies (and (real-polynomial-p poly1)
		(real-polynomial-p poly2))
	   (real-polynomial-p (polynomial-+ poly1 poly2))))

(defthm eval-polynomial-+
  (implies (and (real-polynomial-p poly1)
		(real-polynomial-p poly2)
		(realp x))
	   (equal (eval-polynomial (polynomial-+ poly1 poly2) x)
		  (+ (eval-polynomial poly1 x)
		     (eval-polynomial poly2 x)))))

(defthm eval-polynomial-expt-+
  (implies (and (real-polynomial-p poly1)
		(real-polynomial-p poly2)
		(realp x))
	   (equal (eval-polynomial-expt (polynomial-+ poly1 poly2) x)
		  (+ (eval-polynomial-expt poly1 x)
		     (eval-polynomial-expt poly2 x))))
  :hints (("Goal"
	   :in-theory (e/d (eval-polynomial-expt-correct)
			   (eval-polynomial-expt
			    polynomial-+)))))

(defthm consp-polnomial-+
  (equal (consp (polynomial-+ poly1 poly2))
	 (or (consp poly1)
	     (consp poly2))))

(defthm real-polynomial-*
  (implies (and (real-polynomial-p poly1)
		(real-polynomial-p poly2))
	   (real-polynomial-p (polynomial-* poly1 poly2))))

(defthm eval-polynomial-*
  (implies (and (real-polynomial-p poly1)
		(real-polynomial-p poly2)
		(realp x))
	   (equal (eval-polynomial (polynomial-* poly1 poly2) x)
		  (* (eval-polynomial poly1 x)
		     (eval-polynomial poly2 x)))))


(defthm eval-polynomial-expt-*
  (implies (and (real-polynomial-p poly1)
		(real-polynomial-p poly2)
		(realp x))
	   (equal (eval-polynomial-expt (polynomial-* poly1 poly2) x)
		  (* (eval-polynomial-expt poly1 x)
		     (eval-polynomial-expt poly2 x))))
  :hints (("Goal"
	   :in-theory (e/d (eval-polynomial-expt-correct)
			   (eval-polynomial-expt
			    polynomial-*)))))

(defthm consp-polnomial-*
  (equal (consp (polynomial-* poly1 poly2))
	 (consp poly1)))

(defthm numberp-car-poly
  (implies (real-polynomial-p poly)
	   (equal (acl2-numberp (car poly))
		  (consp poly))))
