(in-package "ACL2")

(include-book "../code/sequences/align")
(include-book "../code/gen-helper/extra")

(defun make-raw-sequence-pairings-each (child parent-seq
                                          seqs-with-tree-keys acc)
  (declare (xargs :guard t))
  (if (consp child)
      (let ((childSeq (cdr (assoc-hqual (car child)
                                         seqs-with-tree-keys))))
        (make-raw-sequence-pairings-each
         (car child) childSeq seqs-with-tree-keys
         (make-raw-sequence-pairings-each
          (cdr child)
          parent-seq seqs-with-tree-keys
          (cons
           (cons
            parent-seq childSeq)
           acc))))
    acc))


(defun make-raw-sequence-pairings (tree seqs-with-tree-keys)
  (declare (xargs :guard (alistp-gen seqs-with-tree-keys)))
  (let ((parent-seq (cdr (assoc-hqual tree seqs-with-tree-keys))))
    (make-raw-sequence-pairings-each tree
                                 parent-seq
                                 seqs-with-tree-keys
                                 nil)))

(defun get-opt-score-from-raw-pairings (pairings cost-stuff)
  (if (consp pairings)
      (+ (get-score-from-matrix (build-align-matrix (caar pairings)
                                                    (cdar pairings)
                                                    cost-stuff))
         (get-opt-score-from-raw-pairings (cdr pairings)
                                          cost-stuff))
    0))

(defun update-raw-sequence-keys (sequences anc-tree-mapping)
  (declare (xargs :guard (and (alistp-gen anc-tree-mapping)
                              (alistp-gen sequences))))
  (if (consp anc-tree-mapping)
      (update-raw-sequence-keys
       (hut (cdar anc-tree-mapping)
            (cdr (het (caar anc-tree-mapping)
                      sequences))
            sequences)
       (cdr anc-tree-mapping))
    sequences))

(defun get-opt-score-from-fully-loaded-tree
  (tree anc-mappings sequences cost-stuff)
  (let* ((new-seqs (update-raw-sequence-keys sequences anc-mappings))
         (pairings (make-raw-sequence-pairings tree new-seqs)))
    (get-opt-score-from-raw-pairings pairings cost-stuff)))

