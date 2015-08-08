;;; -----
;;; Terms
;;; -----

(in-package "TER")

(encapsulate
  ((termp (a) t)
   ;;; ...
   (< (a b) t)
   (term->o-p (a) t))

  ;;; ---------------
  ;;; Local witnesses
  ;;; ---------------

  ;;; Recognizer.

  (local
    (defun termp (a)
      (acl2-numberp a)))

  ;;; ...

  ;;; Term ordering.

  (local
    (defun < (a b)
      (o< (nfix a) (nfix b))))

  ;;; Ordinal embedding.

  (local
    (defun term->o-p (a)
      (+ (nfix a) 1)))

  ;;; ------
  ;;; Axioms
  ;;; ------

  ;;; ...

  ;;; The term ordering is a partial strict order.

  (defthm |~(a < a)|
    (not (< a a)))

  (defthm |a < b & b < c => a < c|
    (implies (and (< a b) (< b c)) (< a c)))

  ;;; The ordinal embedding does not produce 0.

  (defthm |~(term->o-p(a) = 0)|
    (not (equal (term->o-p a) 0)))

  ;;; Well-foundedness of the term ordering.

  (defthm well-foundedness-of-<
    (and (implies (termp a)
		  (o-p (term->o-p a)))
	 (implies (and (termp a) (termp b)
		       (< a b))
		  (o< (term->o-p a) (term->o-p b))))
    :rule-classes (:rewrite :well-founded-relation)))
