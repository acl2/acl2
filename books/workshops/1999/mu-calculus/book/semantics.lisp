(in-package "MODEL-CHECK")
(include-book "syntax")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defabbrev semantics-EX (m f val)
  (image (mu-semantics m (second f) val)
         (inverse-relation m)))

(defabbrev semantics-NOT (m f val)
  (set-complement (mu-semantics m (second f) val)
                  (states m)))

(defabbrev semantics-AND (m f val)
  (intersect (mu-semantics m (first f) val)
             (mu-semantics m (third f) val)))

(defabbrev semantics-OR (m f val)
  (set-union (mu-semantics m (first f) val)
             (mu-semantics m (third f) val)))

(defabbrev semantics-fix (m f val s)
  (compute-fix-point m (third f)
                     (put-assoc-equal (second f) s val)
                     (second f) (size m)))

(defabbrev semantics-MU (m f val)
  (semantics-fix m f val nil))

(defabbrev semantics-NU (m f val)
  (semantics-fix m f val (states m)))

(mutual-recursion
(defun mu-semantics (m f val)
  (declare (xargs :measure (cons (+ (acl2-count f) 1) 0)))
  (cond ((eq f 'true) (states m))
        ((eq f 'false) nil)
        ((mu-symbolp f)
         (cond ((in f (atomic-props m))
                (value-of f (a-labeling m)))
               (t (value-of f val))))
	((equal (len f) 2)
	 (cond ((equal (first f) 'EX)
		(semantics-EX m f val))
	       ((equal (first f) '~)
		(semantics-NOT m f val))))
	((equal (len f) 3)
	 (cond ((equal (second f) '&)
		(semantics-AND m f val))
	       ((equal (second f) '+)
		(semantics-OR m f val))
	       ((equal (first f) 'MU)
		(semantics-MU m f val))
	       ((equal (first f) 'NU)
		(semantics-NU m f val))))))

(defun compute-fix-point (m f val y n)
  (declare (xargs :measure (cons (+ (acl2-count f) 1) (nfix n))))
  (if (zp n)
      (value-of y val)
    (let ((x (value-of y val))
          (new-x (mu-semantics m f val)))
      (if (== x new-x)
          x
        (compute-fix-point m f (put-assoc-equal y new-x val) y (- n 1))))))
)

(defun semantics (m f)
"Returns the set of states in m satisfying f.  The \"simple\" way of
doing it is used, i.e. the semantics of the same sentence may be
recomputed."
  (if (m-calc-sentencep f (atomic-props m))
      (mu-semantics m (translate-f f) nil)
    "not a valid mu-calculus formula"))

(defun fixpointp (m f val x s)
  (== (mu-semantics m f (put-assoc-equal x s val))
      s))

(defun post-fixpointp (m f val x s)
  (=< (mu-semantics m f (put-assoc-equal x s val))
      s))

(defun pre-fixpointp (m f val x s)
  (=< s (mu-semantics m f (put-assoc-equal x s val))))

