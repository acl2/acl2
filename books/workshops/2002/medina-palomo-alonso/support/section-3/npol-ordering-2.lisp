;;; ----------------------
;;; Normalized polynomials
;;; ----------------------

; Includes mods for v2-8 for ordinal changes.

(in-package "NPOL")

(include-book "upol")
(include-book "ordinal-ordering")
(include-book "../../../../../ordinals/ordinals-without-arithmetic")

;;; NOTE:
;;;
;;; From now on we won't assume that the ordinal embedding of a
;;; term/monomial is not zero. Instead, it will be shown that it is
;;; always possible to build a modified ordinal embedding holding this
;;; property without imposing any additional constraint. This approach
;;; has the advantage of separating two concerns: the development of
;;; monomial orderings and the development of induced polynomial
;;; orderings.

(in-theory (disable TER::|~(term->o-p(a) = 0)|
		    MON::|~(monomial->o-p(a) = 0)|))

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

;;; Modified monomial ordinal embedding.

(defun modified-monomial->o-p (a)
  (declare (xargs :guard (monomialp a)
		  :guard-hints (("goal"
				 :in-theory (enable monomialp)))))
  (acl2::o+ (monomial->o-p a) 1))

;;; Polynomial ordinal embedding.

(defun polynomial->o-p (p)
  (declare (xargs :guard (polynomialp p)))
  (if (endp p)
      0
    (make-ord (modified-monomial->o-p (first p))
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

;;; Congruence.

(defcong MON::=T equal (modified-monomial->o-p a) 1)

;;; The monomial ordinal embedding does not produce 0.

(defthm |~(modified-monomial->o-p(a) = 0)|
  (implies (monomialp a)
	   (not (equal (modified-monomial->o-p a) 0))))

;;; Well-foundedness of the monomial ordering w.r.t. the modified
;;; monomial ordinal embedding.

(defthm modified-well-foundedness-of-<
  (and (implies (monomialp a)
		(o-p (modified-monomial->o-p a)))
       (implies (and (monomialp a) (monomialp b)
		     (MON::< a b))
		(o< (modified-monomial->o-p a)
			  (modified-monomial->o-p b))))
  :rule-classes (:rewrite :well-founded-relation))

;;; Correctness of the polynomial ordinal embedding.

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
