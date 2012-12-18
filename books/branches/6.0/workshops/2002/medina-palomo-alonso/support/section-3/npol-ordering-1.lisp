;;; ----------------------
;;; Normalized polynomials
;;; ----------------------

(in-package "NPOL")

(include-book "upol")
(include-book "ordinal-ordering")
(include-book "../../../../../ordinals/ordinals-without-arithmetic")

;;; ---------
;;; Functions
;;; ---------

;;; Recognizer.

(defun polynomialp (p)
  (declare (xargs :guard t))
  (and (UPOL::polynomialp p) (UPOL::nfp p)))

;;; ...

;;; Polynomial ordering.

(defun < (p q)
  (declare (xargs :guard (and (polynomialp p) (polynomialp q))))
  (cond ((or (endp p) (endp q))
         (not (endp q)))
	((MON::=T (first p) (first q))
         (< (rest p) (rest q)))
        (t
         (MON::< (first p) (first q)))))

;;; Ordinal embedding.

(defun polynomial->o-p (p)
  (declare (xargs :guard (polynomialp p)))
  (if (endp p)
      0
    (make-ord (monomial->o-p (first p))
	      1
	      (polynomial->o-p (rest p)))))

;;; ----------
;;; Properties
;;; ----------

;;; ...

;;; The polynomial ordering is a partial strict order.

(defthm |~(p < p)|
  (not (< p p)))

(defthm |p < q & q < r => p < r|
  (implies (and (< p q) (< q r))
	   (< p r)))

;;; Antisymmetry of the polynomial ordering.

(defthm |p < q => ~(q < p)|
  (implies (< p q)
	   (not (< q p)))
  :hints (("Goal"
	   :in-theory (disable |p < q & q < r => p < r|)
	   :use (:instance |p < q & q < r => p < r| (r p)))))

;;; Correctness of the ordinal embedding.

(defthm correctness-of-polynomial->o-p
  (implies (polynomialp p)
           (o-p (polynomial->o-p p))))

;;; Well-foundedness of the polynomial ordering.

(defthm well-foundedness-of-<
  (and (implies (polynomialp p)
                (o-p (polynomial->o-p p)))
       (implies (and (polynomialp p) (polynomialp q)
                     (< p q))
                (o< (polynomial->o-p p)
                    (polynomial->o-p q))))
  :hints (("Goal" :in-theory (enable acl2::|a < b  =>  ~(a = b)|)))
  :rule-classes :well-founded-relation)
