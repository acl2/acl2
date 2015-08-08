(in-package "ACL2")

(include-book "min-length")
(include-book "../code/gen-trees/top")

(defun get-ordering-from-tree (tree)
  (declare (xargs :guard t))
  (let ((tips (mytips tree)))
    (app tips (list (car tips)))))

(defun get-pairings-from-ordering (ordering numberfied-seqs acc)
  (declare (xargs :guard (alistp-gen numberfied-seqs)))
  (if (consp ordering)
      (if (consp (cdr ordering))
          (get-pairings-from-ordering
           (cdr ordering)
           numberfied-seqs
           (cons (cons (cdr (assoc-hqual (car ordering) numberfied-seqs))
                       (cdr (assoc-hqual (cadr ordering) numberfied-seqs)))
                 acc))
        acc)
    acc))

(defun get-circle-pairings-from-align (tree numberfied-seqs)
  (declare (xargs :guard (alistp-gen numberfied-seqs)))
  (let ((ordering (get-ordering-from-tree tree)))
    (get-pairings-from-ordering ordering numberfied-seqs nil)))


(defun circle-score-numberfied-seqs
  (tree numberfied-seqs gap-char gap-cost gap-extend-cost transition-matrix)
  (declare (xargs :guard (and (alistp-gen numberfied-seqs)
                              (rationalp gap-cost)
                              (rationalp gap-extend-cost)
                              (small-integer-transition-matrixp
                               transition-matrix))))
  (let ((pairings (get-circle-pairings-from-align tree numberfied-seqs)))
    (score-pairings 'affine pairings
                    (list gap-char gap-cost gap-extend-cost
                          (numberfy transition-matrix 0)) 0)))

(defun numberfy-seq (seq mapping)
  (declare (xargs :guard (alistp-gen mapping)))
  (if (consp seq)
      (let ((mapped (assoc-hqual (car seq) mapping)))
        (if (consp mapped)
            (cons (cdr mapped) (numberfy-seq (cdr seq) mapping))
          (prog2$ (cw "Error: ambiguous character in seq??~%")
                  "Error: ambiguous character in seq?")))
    nil))

(defun make-numberfied-seqs (sequences mapping ans)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (alistp-gen mapping))))
  (if (consp sequences)
      (make-numberfied-seqs (cdr sequences) mapping
                            (cons (cons (caar sequences)
                                        (numberfy-seq (cdar sequences)
                                                      mapping))
                                  ans))
    ans))

(defun mapping-from-matrix (mat n)
  (declare (xargs :guard (and (alistp-gen mat)
                              (rationalp n))))
  (if (consp mat)
      (cons (cons (caar mat) n)
            (mapping-from-matrix (cdr mat) (1+ n)))
    nil))

(defthm small-integer-transition-matrixp-gives-alistp-gen
  (implies (small-integer-transition-matrixp x)
           (alistp-gen x)))

(defthm alistp-gen-mapping-from-matrix
  (implies (alistp-gen x)
           (alistp-gen (mapping-from-matrix x n))))

(defthm alistp-gen-make-numberfied-seqs
  (implies (and (alistp-gen seqs)
                (alistp-gen acc))
           (alistp-gen (make-numberfied-seqs seqs mapping acc))))

(defun circle-score-seqs (tree sequences gap-char gap-cost
                               gap-extend-cost transition-matrix)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (rationalp gap-cost)
                              (rationalp gap-extend-cost)
                              (small-integer-transition-matrixp
                               transition-matrix))))
  (circle-score-numberfied-seqs tree
                           (make-numberfied-seqs sequences
                                                 (mapping-from-matrix
                                                  transition-matrix 0) nil)
                           gap-char gap-cost gap-extend-cost
                           transition-matrix))

