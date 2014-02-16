(in-package "MODEL-CHECK")

(include-book "syntax")
(include-book "fixpoints")
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
"The semantics of f in m given that val is the valuation of the variables in v."
  (declare (xargs :guard (and (modelp m) (relationp val))
                  :verify-guards nil
                  :measure (cons (+ (acl2-count f) 1) 0)))
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
  (declare (xargs :guard (and (modelp m) (relationp val)
                              (integerp n) (>= n 0))
                  :verify-guards nil
                  :measure (cons (+ (acl2-count f) 1) (nfix n))))
  (if (zp n)
      (value-of y val)
    (let ((x (value-of y val))
          (new-x (mu-semantics m f val)))
      (if (== x new-x)
          x
        (compute-fix-point m f (put-assoc-equal y new-x val) y (- n 1))))))
)

(defmacro if-zpn (a)
  `(if (zp n)
       ,a
     (list ,a
           (semantics-ind m f val y (1- n))
           (semantics-ind m f (put-assoc-equal y (mu-semantics m f val) val)
                          y (1- n)))))

(defun semantics-ind (m f val y n)
  (declare (xargs :measure (cons (+ (acl2-count f) 1) (nfix n))))
  (cond ((symbolp f) (if-zpn (list m f val y n)))
	((equal (len f) 2)
	 (if-zpn (semantics-ind m (second f) val y n)))
	((equal (len f) 3)
	 (cond
	  ((in (second f) '(& +))
	   (if-zpn (list (semantics-ind m (first f) val y n)
			 (semantics-ind m (third f) val y n))))
	  ((equal (first f) 'MU)
	   (if-zpn (semantics-ind m (third f)
				  (put-assoc-equal (second f) nil val)
				  (second f) (size m))))
	  ((equal (first f) 'NU)
	   (if-zpn (semantics-ind m (third f)
				  (put-assoc-equal (second f) (states m) val)
				  (second f) (size m))))
	  (t (if-zpn nil))))
	(t (if-zpn nil))))

(defthm add-semantics-ind-to-mu-semantics
  t
  :rule-classes
  ((:induction :pattern (compute-fix-point m f val y n)
               :scheme (semantics-ind m f val y n))))

(defthm open-EX
  (implies (and (equal (car f) 'ex)
                (equal (len f) 2))
           (equal (mu-semantics m f val)
                  (semantics-EX m f val))))

(defthm open-NOT
  (implies (and (equal (car f) '~)
                (equal (len f) 2))
           (equal (mu-semantics m f val)
                  (semantics-NOT m f val))))

(defthm open-AND
  (implies (and (equal (cadr f) '&)
                (equal (len f) 3))
           (equal (mu-semantics m f val)
                  (semantics-AND m f val))))

(defthm open-OR
  (implies (and (equal (cadr f) '+)
                (equal (len f) 3))
           (equal (mu-semantics m f val)
                  (semantics-OR m f val))))

(defthm open-MU
  (implies (and (equal (car f) 'MU)
                (not (equal (cadr f) '+))
                (not (equal (cadr f) '&))
                (equal (len f) 3))
           (equal (mu-semantics m f val)
                  (semantics-MU m f val))))

(defthm open-NU
  (implies (and (equal (car f) 'NU)
                (not (equal (cadr f) '+))
                (not (equal (cadr f) '&))
                (equal (len f) 3))
           (equal (mu-semantics m f val)
                  (semantics-NU m f val))))

(defthm open-compute-fix-point
  (implies
   (not (zp n))
   (equal (compute-fix-point m f val y n)
          (let ((x (value-of y val))
                (new-x (mu-semantics m f val)))
            (if (== x new-x)
                x
              (compute-fix-point m f (put-assoc-equal y new-x val) y (- n 1)))))))

(defthm sem-is-true-listp
  (implies (and (relationp val)
                (modelp m))
           (and (true-listp (mu-semantics m f val))
                (true-listp (compute-fix-point m f val y n))))
  :hints (("Goal" :in-theory (disable SETS::=<-LEN-REM-DUPS
				      SETS::|X == Y  =>  X =< Y / Y =< X|))))  ;; RBK:

(verify-guards mu-semantics)

(defun semantics (m f)
"Returns the set of states in m satisfying f.  The \"simple\" way of
doing it is used, i.e. the semantics of the same sentence may be
recomputed."
  (declare (xargs :guard (modelp m)))
  (if (m-calc-sentencep f (atomic-props m))
      (mu-semantics m (translate-f f) nil)
    "not a valid mu-calculus formula"))

(defun model-check (m s f-list)
"m is a model, s is a subset of the model's states and f-list is a list of
formulae.  A list is returned indicating which of the formulae are
true at all of the states in s."
  (declare (xargs :guard (and (modelp m) (true-listp s) (true-listp f-list))))
  (if (endp f-list)
      nil
    (let ((res (semantics m (car f-list))))
      (if (true-listp res)
          (cons (=< s res)
                (model-check m s (cdr f-list)))
        res))))

(defun model-ok (m)
  (and (modelp m)
       (= (cardinality (states m)) (size m))
       (rel-range-subset (relation m) (states m))
       (rel-range-subset (s-labeling m) (atomic-props m))
       (rel-range-subset (inverse-relation m) (states m))
       (rel-range-subset (a-labeling m) (states m))))

(defun fixpointp (m f val x s)
  (== (mu-semantics m f (put-assoc-equal x s val))
      s))

(defun post-fixpointp (m f val x s)
  (=< (mu-semantics m f (put-assoc-equal x s val))
      s))

(defun pre-fixpointp (m f val x s)
  (=< s (mu-semantics m f (put-assoc-equal x s val))))

(defthm intersect-thm
  (implies (=< x y)
           (=< (intersect z x) y)))

(defthm set-union-thm
  (implies (and (=< x z)
                (=< y z))
           (=< (set-union x y) z)))

(defthm set-minus-thm
  (implies (=< x z)
           (=< (minus x y) z)))

(defthm mu-semantics-stays-in-bounds
  (implies (and (model-ok m)
                (rel-range-subset val st)
                (=< (states m) st))
           (and (=< (compute-fix-point m f val var n)
                    st)
                (=< (mu-semantics m f val)
                    st))))

; Exercise 21
(encapsulate
 ((sem-mon-f () t)
  (good-model () t)
  (good-val () t)
  (good-var () t))
 (local (defun sem-mon-f() 'a))
 (local (defun good-model() '(nil nil (a) nil nil nil 0)))
 (local (defun good-val() nil))
 (local (defun good-var() 'b))

 (defthm good-model-is-a-model
   (model-ok (good-model)))

 (defthm good-val-range-ok
   (rel-range-subset (good-val) (states (good-model))))

 (defthm good-var-var (mu-symbolp (good-var)))

 (defthm sem-mon-f-is-sem-monotone
   (implies (=< x y)
            (=< (mu-semantics
                 (good-model) (sem-mon-f)
                 (put-assoc-equal (good-var) x (good-val)))
                (mu-semantics
                 (good-model) (sem-mon-f)
                 (put-assoc-equal (good-var) y (good-val)))))))

; Exercise 23
(defmacro defmu (name thm fn-inst &rest args)
  `(defthm ,name ,thm
     :hints
     (("goal"
       :use (:functional-instance
             ,fn-inst
             (sets::S (lambda nil (states (good-model))))
             (sets::f
              (lambda (y)
                (mu-semantics (good-model)
			      (sem-mon-f)
			      (put-assoc-equal (good-var) y (good-val)))))
             (sets::applyf
              (lambda (y n)
                (compute-fix-point (good-model)
                                   (sem-mon-f)
                                   (put-assoc-equal (good-var) y (good-val))
                                   (good-var) n)))
             (sets::cardinality cardinality)))
      ,@args)))

(defthm mu-symbol-not-+-or-&
  (implies (mu-symbolp var)
           (and (not (equal var '+))
                (not (equal var '&)))))

(defthm model-ok-cardinality
  (implies (model-ok m)
	   (equal (cadddr (cdddr m))
		  (cardinality (states m)))))

; Exercise 22, part 1
(defmu semmu-is-a-fixpoint
  (fixpointp (good-model) (sem-mon-f) (good-val) (good-var)
             (mu-semantics (good-model)
			   (list 'mu (good-var) (sem-mon-f))
			   (good-val)))
  sets::lfix-is-a-fixpoint
  ("subgoal 3"
   :use (:instance good-val-range-ok)))

; Exercise 22, part 2
(defmu semmu-is-below-all-post-fixpoints
  (implies (post-fixpointp (good-model) (sem-mon-f) (good-val) (good-var) x)
           (=< (mu-semantics (good-model) (list 'mu (good-var) (sem-mon-f))
			     (good-val)) x))
  sets::lfix-is-below-all-post-fixpoints)

; Exercise 22, part 3
(defmu semnu-is-a-fixpoint
  (fixpointp (good-model) (sem-mon-f) (good-val) (good-var)
             (mu-semantics (good-model) (list 'nu (good-var) (sem-mon-f))
			   (good-val)))
  sets::gfix-is-a-fixpoint)

; Exercise 22, part 4
(defmu semnu-is-above-all-pre-fixpoints
  (implies (and (=< x (states (good-model)))
                (pre-fixpointp (good-model) (sem-mon-f) (good-val) (good-var) x))
           (=< x (mu-semantics (good-model) (list 'nu (good-var) (sem-mon-f))
			       (good-val))))
  sets::gfix-is-above-all-pre-fixpoints)
