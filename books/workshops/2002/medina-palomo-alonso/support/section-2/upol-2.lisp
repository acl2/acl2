;;; ------------------------
;;; Unnormalized polynomials
;;; ------------------------

(in-package "UPOL")

(encapsulate

  ;;; ----------
  ;;; Signatures
  ;;; ----------

  ((polynomialp (p) t)
   (nf (p) t)
   (nfp (p) t)
   (= (p q) t)
   (+ (p q) t)
   (* (p q) t)
   (- (p) t)
   (null () t)
   (identity () t))

  ;;; ---------------
  ;;; Local witnesses
  ;;; ---------------

  (local
    (defun polynomialp (p)
      (acl2-numberp p)))

  (local
    (defun nf (p)
      (fix p)))

  (local
    (defun nfp (p)
      (equal (nf p) p)))

  (local
    (defun = (p q)
      (equal (nf p) (nf q))))

  (local
    (defun + (p q)
      (ACL2::+ p q)))

  (local
    (defun * (p q)
      (ACL2::* p q)))

  (local
    (defun - (p)
      (ACL2::- p)))

  (local
    (defun null ()
      0))

  (local
    (defun identity ()
      1))

  ;;; ------
  ;;; Axioms
  ;;; ------

  ;;; Normal form.

  (defthm |nfp(p) <=> nf(p) = p|
    (iff (nfp p) (equal (nf p) p)))

  (defthm |nf(0) = 0|
    (equal (nf (null)) (null)))

  (defthm |nf(1) = 1|
    (equal (nf (identity)) (identity)))

  ;;; Equivalence.

  (defequiv =)

  ;;; Compatibility.

  (defthm |p + nf(q) = p + q|
    (= (+ p (nf q)) (+ p q)))

  (defthm |p * nf(q) = p * q|
    (= (* p (nf q)) (* p q)))

  ;;; Congruence.

  (defcong = equal (nf p) 1)

  ;;; Ring.

  (defthm |p + q = q + p|
    (= (+ p q) (+ q p)))

  (defthm |(p + q) + r = p + (q + r)|
    (= (+ (+ p q) r) (+ p (+ q r))))

  (defthm |p * q = q * p|
    (= (* p q) (* q p)))

  (defthm |(p * q) * r = p * (q * r)|
    (= (* (* p q) r) (* p (* q r))))

  (defthm |p * (q + r) = (p * q) + (p * r)|
    (= (* p (+ q r)) (+ (* p q) (* p r))))

  (defthm |p + (- p) = 0|
    (= (+ p (- p)) (null)))

  (defthm |0 + p = p|
    (implies (polynomialp p)
	     (= (+ (null) p) p)))

  (defthm |1 * p = p|
    (implies (polynomialp p)
	     (= (* (identity) p) p))))

;;; ----------
;;; Properties
;;; ----------

(defmacro not-nf-syntaxp (p)
  `(syntaxp (not (and (consp ,p) (eq (first ,p) 'nf)))))

(defthm |p + q = p + nf(q)|
  (implies (not-nf-syntaxp q)
	   (= (+ p q) (+ p (nf q)))))

(defcong = = (+ p q) 2
  :hints (("Goal" :in-theory (disable |p + nf(q) = p + q|))))

(defthm |p * q = p * nf(q)|
  (implies (not-nf-syntaxp q)
	   (= (* p q) (* p (nf q)))))

(defcong = = (* p q) 2
  :hints (("Goal" :in-theory (disable |p * nf(q) = p * q|))))

;;; These rules are not useful any more.

(in-theory (disable |p + q = p + nf(q)| |p * q = p * nf(q)|))

;;; Completion of congruences.

(defcong = = (+ p q) 1
  :hints (("Goal"
	   :in-theory (disable |p + q = q + p|)
	   :use (|p + q = q + p|
		 (:instance |p + q = q + p| (p p-equiv))))))

(defcong = = (* p q) 1
  :hints (("Goal"
	   :in-theory (disable |p * q = q * p|)
	   :use (|p * q = q * p|
		 (:instance |p * q = q * p| (p p-equiv))))))

;;; Completion of commutativity and associativity rules.

(defthm |p + (q + r) = q + (p + r)|
  (= (+ p (+ q r)) (+ q (+ p r)))
  :hints (("Goal"
	   :in-theory (disable |(p + q) + r = p + (q + r)|)
	   :use (|(p + q) + r = p + (q + r)|
		 (:instance |(p + q) + r = p + (q + r)| (p q) (q p))))))

(defthm |p * (q * r) = q * (p * r)|
  (= (* p (* q r)) (* q (* p r)))
  :hints (("Goal"
	   :in-theory (disable |(p * q) * r = p * (q * r)|)
	   :use (|(p * q) * r = p * (q * r)|
		 (:instance |(p * q) * r = p * (q * r)| (p q) (q p))))))
