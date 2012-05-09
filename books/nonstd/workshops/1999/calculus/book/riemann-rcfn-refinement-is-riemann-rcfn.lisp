(in-package "ACL2")

;;; Define basic notions.
(include-book "riemann-defuns")

(include-book "riemann-lemmas")

(defun riemann-rcfn-refinement-is-riemann-rcfn-induction (p1 p2)
  ;; Similar to scheme from refinement-p, but keeping cars in sync.
  (if (consp p2)
      (if (consp (cdr p2))
          (riemann-rcfn-refinement-is-riemann-rcfn-induction
           (member (cadr p2) p1)
           (cdr p2))
        p1)
    t))

;;; We leave this here rather than moving it to riemann-lemmas.lisp
;;; because of the free variable.
(defthm partitionp-forward-to-realp-member
  (implies (and (partitionp p)
                (member a p))
           (realp (car (member a p))))
  :rule-classes :forward-chaining)

;;; We leave this here rather than moving it to riemann-lemmas.lisp
;;; because of the free variable.
(defthm refinement-p-implies-realp-car-member
  (implies (and (partitionp p1)
                (partitionp p2)
                (refinement-p p1 p2))
           (realp (car (member (car p2) p1))))
  :rule-classes :forward-chaining)

(defthm car-last-member
  (implies (member a x)
           (equal (car (last (member a x)))
                  (car (last x)))))

(defthm refinement-p-implies-realp-cadr-member
  (implies (and (partitionp p1)
                (cdr (member a p1)))
           (realp (cadr (member a p1))))
  :rule-classes :forward-chaining)

;;; This seems to expensive to move to riemann-lemmas.lisp.
(defthm car-member
  (implies (member a x)
           (equal (car (member a x))
                  a)))

(defthm partitionp-member
  (implies (and (partitionp p)
                (member a p))
           (partitionp (member a p)))
  :rule-classes :forward-chaining)

(defthm member-car-last
  (implies (partitionp p)
           (equal (member (car (last p)) p)
                  (last p))))

(defthm cdr-last
  (implies (true-listp p)
           (equal (cdr (last p))
                  nil)))

(defthm partitionp-implies-less-than-cadr
  (implies (and (partitionp p)
                (cdr (member a p)))
           (< a (cadr (member a p)))))

(defthm strong-refinement-p-preserved
  (implies (and (consp p2)
                (consp (cdr p2))
                (strong-refinement-p p1 p2))
           (strong-refinement-p (member (cadr p2) p1)
                                (cdr p2)))
  :hints (("Goal" :expand (refinement-p p1 p2))))

(encapsulate
 ()
 (local (include-book "equal-riemann-rcfn-refinement-reduction"))
 (defthm equal-riemann-rcfn-refinement-reduction
   (implies (and (partitionp p1)
                 (partitionp p2)
                 (consp (cdr p2))
                 (equal (riemann-rcfn-refinement (member (cadr p2) p1)
                                                 (cdr p2))
                        (riemann-rcfn (cdr p2)))
                 (strong-refinement-p p1 p2))
            (equal (riemann-rcfn-refinement p1 p2)
                   (riemann-rcfn p2)))))

(defthm strong-refinement-p-forward
  (implies (strong-refinement-p p1 p2)
           (and (partitionp p1)
                (partitionp p2)
                (equal (car p1) (car p2))
                (equal (car (last p1))
                       (car (last p2)))
                (refinement-p p1 p2)))
  :rule-classes :forward-chaining)

(defthm riemann-rcfn-refinement-is-riemann-rcfn-base-2
  (implies (and (strong-refinement-p p1 p2)
                (not (consp (cdr p2))))
           (equal (riemann-rcfn-refinement p1 p2)
                  (riemann-rcfn p2))))

(defthm riemann-rcfn-refinement-is-riemann-rcfn
  (implies (strong-refinement-p p1 p2)
           (equal (riemann-rcfn-refinement p1 p2)
                  (riemann-rcfn p2)))
  :hints (("Goal"
           :in-theory (disable strong-refinement-p
                               riemann-rcfn-refinement
                               riemann-rcfn)
           :induct
           (riemann-rcfn-refinement-is-riemann-rcfn-induction p1 p2))))
