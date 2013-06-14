(in-package "ACL2")

;;; Define basic notions.
(include-book "riemann-defuns")

(include-book "riemann-lemmas")

(defun co-member (a x)
  ;; returns all members of x up to and including a
  (if (consp x)
      (if (equal a (car x))
          (list a)
        (cons (car x) (co-member a (cdr x))))
    nil))

(defun my-make-list (n elt)
  (if (zp n)
      nil
    (cons elt (my-make-list (1- n) elt))))

(defthm my-make-list-1
  (equal (my-make-list 1 x)
         (list x))
  :hints (("Goal" :expand (my-make-list 1 x))))

(defthm next-gte-expand
  (implies (equal (car p2) a)
           (equal (next-gte a p2)
                  a)))

(defthm next-gte-for-last
  (implies (and (partitionp p)
                (equal (car (last p)) a))
           (equal (next-gte a p)
                  a)))

(defthm map-rcfn-refinement-for-constant
  (implies
   (and (partitionp p3)
        (partitionp p2)
        (consp (cdr p2))
        (< (car p2) (car p3))
        (equal (cadr p2) (car (last p3))))
   (equal
    (map-rcfn-refinement p3 p2)
    (my-make-list (len p3)
                  (rcfn (cadr p2))))))

(defthm partitionp-cdr-co-member
  (implies (partitionp p)
           (equal (partitionp (cdr (co-member a p)))
                  (and (consp (cdr p))
                       (not (equal a (car p)))))))

(defthm map-rcfn-refinement-cdr-co-member-subgoal-hack-1
  (implies (and (partitionp p1)
                (consp p2)
                (< (car p1) (cadr p2))
                (partitionp (cdr p2))
                (consp (cdr p2))
                (equal (car p1) (car p2))
                (equal (car (last p1))
                       (car (last (cdr p2))))
                (refinement-p p1 p2))
           (< (car p1)
              (cadr (co-member (cadr p2) p1)))))

(defthm car-last-cdr-co-member
  (implies (and (partitionp p1)
                (not (equal (car p1) a))
                (member a p1))
           (equal (car (last (cdr (co-member a p1))))
                  a)))

(defthm map-rcfn-refinement-cdr-co-member-subgoal-hack-2
  (implies (and (partitionp p1)
                (consp p2)
                (< (car p1) (cadr p2))
                (partitionp (cdr p2))
                (consp (cdr p2))
                (equal (car p1) (car p2))
                (equal (car (last p1))
                       (car (last (cdr p2))))
                (refinement-p p1 p2))
           (equal (car (last (cdr (co-member (cadr p2) p1))))
                  (cadr p2))))

(defthm partitionp-cdr-co-member-forced
  (implies (and (partitionp p)
                (not (equal a (car p)))
                (force (consp (cdr p))))
           (equal (partitionp (cdr (co-member a p)))
                  t)))

(defthm map-rcfn-refinement-cdr-co-member
  (implies
   (and (partitionp p1)
        (partitionp p2)
        (consp (cdr p2))
        (strong-refinement-p p1 p2))
   (equal
    (map-rcfn-refinement (cdr (co-member (cadr p2) p1))
                         p2)
    (my-make-list (len (cdr (co-member (cadr p2) p1)))
                  (rcfn (cadr p2))))))
