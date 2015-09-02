(in-package "TER")

(include-book "term")
(include-book "../../../../ordinals/ordinals-without-arithmetic")

;;; ----------------------------------------
;;; Strict lexicographical ordering on terms
;;; ----------------------------------------

(defun < (a b)
  (declare (xargs :guard (and (termp a) (termp b))))
  (cond ((COMMON-LISP::< (len a) (len b))
	 t)
	((COMMON-LISP::> (len a) (len b))
	 nil)
	((or (endp a) (endp b))
	 (not (endp b)))
	((equal (first a) (first b))
	 (< (rest a) (rest b)))
	(t
	 (COMMON-LISP::< (first a) (first b)))))

;;; Examples:

#|
(< '(1 2) '(1 2 3))
(< '(1 2 2) '(1 2 3))
(not (< '(1 2 3) '(1 2 3))
(not (< '(1 2 2) '(1 2)))
|#

;;; Relation is irreflexive.

(defthm irreflexivity-of-<
  (not (< a a)))

;;; Relation is transitive.

(defthm transitivity-of-<
  (implies (and (< a b) (< b c)) (< a c)))

;;; Relation is anti-symmetric.

(defthm anti-symmetry-of-<
  (implies (< a b) (not (< b a))))

;;; Relation is trichotomic (strict lexicographical ordering is total).

(defthm trichotomy-of-<
  (implies (and (termp a) (termp b))
	   (or (< a b) (< b a) (= a b)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (termp a) (termp b)
			   (not (= a b)) (not (< a b)))
		      (< b a)))))

;;; ------------------------------------------------
;;; Well-founding of strict lexicographical ordering
;;; ------------------------------------------------

;;; Term embedding in e0-ordinals.

#| Changed to the definition below for the ordinals changes in v2-8.
(defun term->e0-ordinal (a)
  (declare (xargs :guard (termp a)))
  (cond ((endp a)
	 0)
	(t
	 (cons (cons (len a) (first a))
	       (term->e0-ordinal (rest a))))))
|#

(defun term->o-p (a)
  (declare (xargs :guard (termp a)
		  :verify-guards nil))
  (cond ((endp a)
	 0)
	(t
	 (make-ord (len a)
		   (1+ (first a))
		   (term->o-p (rest a))))))

(defthm term->o-p-o-first-expt
  (equal (o-first-expt (term->o-p a))
	 (len a)))

(verify-guards term->o-p)

;;; Examples:

#|
(equal (term->e0-ordinal '(1)) '((1 . 1) . 0))
(equal (term->e0-ordinal '(8 0)) '((2 . 8) (1 . 0) . 0))
(equal (term->e0-ordinal '(4 3 5)) '((3 . 4) (2 . 3) (1 . 5) . 0))
|#

;;; Term embedding produces an e0-ordinal.

#| ; Changed to the form below for v2-8 ordinals changes.
(encapsulate ()
  (local
    (defthm technical-lemma
      (implies (and (termp a)
		    (e0-ordinalp (term->e0-ordinal (rest a))))
	       (e0-ordinalp (term->e0-ordinal a)))
      :otf-flg t))

    (defthm e0-ordinalp-term->e0-ordinal
      (implies (termp a)
	       (e0-ordinalp (term->e0-ordinal a)))
      :hints (("Goal"
	       :in-theory (disable e0-ordinalp term->e0-ordinal)))))
|#

(encapsulate ()
  (local
    (defthm technical-lemma
      (implies (and (termp a)
		    (o-p (term->o-p (rest a))))
	       (o-p (term->o-p a)))
      :otf-flg t))

    (defthm o-p-term->o-p
      (implies (termp a)
	       (o-p (term->o-p a)))
      :hints (("Goal"
	       :in-theory (disable o-p term->o-p)))))

;;; Relation is well-founded.

(defthm well-ordering-of-<
  (and (implies (termp a)
		(o-p (term->o-p a)))
       (implies (and (termp a) (termp b)
		     (< a b))
		(o< (term->o-p a) (term->o-p b))))
  :rule-classes :well-founded-relation)

;;; ------------------------------------------------
;;; Admissibility of strict lexicographical ordering
;;; ------------------------------------------------

;;; Strict lexicographical ordering has a first element (the null term).

(defthm <-has-first
  (implies (and (termp a) (termp b)
		(compatiblep a b)
		(nullp a) (not (nullp b)))
	   (< a b)))

;;; Strict lexicographical ordering is compatible with multiplication.

(defthm <-compatible-*-1
  (implies (and (termp a) (termp b) (termp c)
		(compatiblep a c) (compatiblep b c)
		(< a b))
	   (< (* a c) (* b c))))

(defthm <-compatible-*-2
  (implies (and (termp a) (termp b) (termp c)
		(compatiblep a c) (compatiblep b c)
		(< a b))
	   (< (* c a) (* c b))))

;;; ----------------------------------
;;; We disable the relation definition
;;; ----------------------------------

(in-theory (disable <))
