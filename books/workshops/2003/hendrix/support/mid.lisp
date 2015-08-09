;;;;; Identity matrix
;;;;; TODO: Tie this into mentry operations.
(in-package "ACL2")

(include-book "mdefthms")

(defmacro mid-guard (n)
  `(and (integerp ,n)
        (<= 0 ,n)))

(defun mid (n)
  (declare (xargs :guard (mid-guard n)
                  :verify-guards nil))
  (cond ((zp n) nil)
        ((zp (1- n)) '((1)))
        (t (let ((zero-row (vzero (1- n))))
             (row-cons (cons 1 zero-row)
                       (col-cons zero-row
                                 (mid (1- n))))))))

(local
 (defthm id-bootstrap
   (and (matrixp (mid n))
        (equal (row-count (mid n))
               (nfix n))
        (equal (col-count (mid n))
               (nfix n)))))

(defthm matrix-id
  (matrixp (mid n)))

(defthm m-empty-id
  (equal (m-emptyp (mid n))
         (zp n)))

(defthm row-count-id
  (equal (row-count (mid n))
         (nfix n)))

(defthm col-count-id
  (equal (col-count (mid n))
         (nfix n)))

(verify-guards mid)

(defthm id-by-col-def
  (equal (mid n)
         (cond ((zp n) nil)
               ((zp (1- n)) (col-cons '(1) nil))
               (t (col-cons (cons 1 (vzero (1- n)))
                            (row-cons (vzero (1- n))
                                      (mid (1- n)))))))
  :rule-classes :definition)
