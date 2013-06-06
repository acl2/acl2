;;; ---------
;;; Monomials
;;; ---------

(in-package "MON")

(include-book "term")

;;; ---------
;;; Functions
;;; ---------

(deflabel start-of-functions)

;;; Recognizer.

(defun monomialp (a)
  (declare (xargs :guard t))
  (and (consp a)
       (acl2-numberp (first a))
       (termp (rest a))))

;;; ...

;;; Coefficient.

(defun coefficient (a)
  (declare (xargs :guard (consp a)))
  (first a))

;;; Term.

(defun term (a)
  (declare (xargs :guard (consp a)))
  (rest a))

;;; Recognizer for null monomials.

(defun nullp (a)
  (declare (xargs :guard (consp a)))
  (equal (coefficient a) 0))

;;; Term equality.

(defun =T (a b)
  (declare (xargs :guard (and (consp a) (consp b))))
  (equal (term a) (term b)))

;;; Monomial ordering.

(defun < (a b)
  (declare (xargs :guard (and (consp a) (consp b))))
  (TER::< (term a) (term b)))

;;; Ordinal embedding.

(defun monomial->o-p (a)
  (declare (xargs :guard (consp a)))
  (term->o-p (term a)))

;;; The theory of monomial functions.

(deftheory functions
  (set-difference-theories (universal-theory :here)
                           (universal-theory 'start-of-functions)))

;;; ----------
;;; Properties
;;; ----------

;;; Equivalence and congruences.

(defequiv =T)

(defcong =T equal (term a) 1)
(defcong =T equal (< a b) 1)
(defcong =T equal (< a b) 2)
(defcong =T equal (monomial->o-p a) 1)

;;; ...

;;; The monomial ordering is a partial strict order.

(defthm |~(a < a)|
  (not (< a a)))

(defthm |a < b & b < c => a < c|
  (implies (and (< a b) (< b c)) (< a c)))

;;; Antisymmetry of the monomial ordering.

(defthm |a < b => ~(b < a)|
  (implies (< a b)
	   (not (< b a)))
  :hints (("Goal"
	   :in-theory (disable |a < b & b < c => a < c|)
	   :use (:instance |a < b & b < c => a < c| (c a)))))

;;; The ordinal embedding does not produce 0.

(defthm |~(monomial->o-p(a) = 0)|
  (not (equal (monomial->o-p a) 0)))

;;; Well-foundedness of the monomial ordering.

(defthm well-foundedness-of-<
  (and (implies (monomialp a)
		(o-p (monomial->o-p a)))
       (implies (and (monomialp a) (monomialp b)
		     (< a b))
		(o< (monomial->o-p a)
		    (monomial->o-p b))))
  :rule-classes (:rewrite :well-founded-relation))

;;; +++++++++++++++++++
;;; Abstraction barrier
;;; +++++++++++++++++++

(in-theory (disable functions))
