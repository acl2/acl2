(in-package "ACL2")

;;; This book re-does some of Ruben's continuity.lisp (as extended by
;;; email he sent me) in the context of partitions.

(include-book "riemann-defuns")
(include-book "riemann-lemmas")
(include-book "make-partition")
;;; !! The following should probably be in make-partition.lisp:
(in-theory (disable make-partition))
(include-book "nsa-lemmas")
(include-book "between-limited-implies-limited")
(include-book "integral-rcfn-lemmas")

(defun max-x-rec (p)
  (if (consp p)
      (if (consp (cdr p))
          (let ((a (max-x-rec (cdr p))))
            (if (> (rcfn (car p)) (rcfn a))
                (car p)
              a))
        (car p))
    ;; Should never reach the following case.
    0))

(defthm max-x-rec-between-first-last
  (implies (partitionp p)
           (and (<= (car p) (max-x-rec p))
                (<= (max-x-rec p) (car (last p)))))
  :rule-classes :forward-chaining)

(defthm max-x-rec-between
  (implies (partitionp p)
           (between (max-x-rec p) (car p) (car (last p))))
  :rule-classes :forward-chaining)

(defthm realp-max-x-rec
  (implies (partitionp p)
           (realp (max-x-rec p)))
  :rule-classes :type-prescription)

(defthm i-limited-max-x-rec
  (implies (and (partitionp p)
                (i-limited (car p))
                (i-limited (car (last p))))
           (i-limited (max-x-rec p))))

(defun-std max-x (a b)
  (if (and (realp a)
           (realp b)
           (< a b))
      (standard-part (max-x-rec (make-partition a b
                                                (i-large-integer))))
    0))

(defthm max-x-rec-is-maximum
  (implies (and (partitionp p)
                (member x p))
	   (>= (rcfn (max-x-rec p)) (rcfn x))))

;;; It should be routine to derive a fact analogous to the one just
;;; above, but for max-x.  However, that may require some tedium, so
;;; we postpone it.

(defun min-x-rec (p)
  (if (consp p)
      (if (consp (cdr p))
          (let ((a (min-x-rec (cdr p))))
            (if (< (rcfn (car p)) (rcfn a))
                (car p)
              a))
        (car p))
    ;; Should never reach the following case.
    0))

(defthm min-x-rec-between-first-last
  (implies (partitionp p)
           (and (<= (car p) (min-x-rec p))
                (<= (min-x-rec p) (car (last p)))))
  :rule-classes :forward-chaining)

(defthm min-x-rec-between
  (implies (partitionp p)
           (between (min-x-rec p) (car p) (car (last p))))
  :rule-classes :forward-chaining)

(defthm realp-min-x-rec
  (implies (partitionp p)
           (realp (min-x-rec p)))
  :rule-classes :type-prescription)

(defthm i-limited-min-x-rec
  (implies (and (partitionp p)
                (i-limited (car p))
                (i-limited (car (last p))))
           (i-limited (min-x-rec p))))

(defun-std min-x (a b)
  (if (and (realp a)
           (realp b)
           (< a b))
      (standard-part (min-x-rec (make-partition a b
                                                (i-large-integer))))
    0))

(defthm min-x-rec-is-minimum
  (implies (and (partitionp p)
                (member x p))
	   (<= (rcfn (min-x-rec p)) (rcfn x))))

;;; It should be routine to derive a fact analogous to the one just
;;; above, but for min-x.  However, that may require some tedium, so
;;; we postpone it.

