(in-package "ACL2")

(defun create-new-tree-db-from-list (analysis-id rooted? brlens? list curTreeNum)
  (declare (xargs :guard (natp curTreeNum)))
  (if (consp list)
      (cons (cons curTreeNum (acons 'analysis-id analysis-id
                                    (acons 'rooted? rooted?
                                           (acons 'brlens? brlens?
                                                  (acons 'tree (car list) nil)))))
            (create-new-tree-db-from-list analysis-id
                                          rooted?
                                          brlens?
                                          (cdr list)
                                          (1+ curTreeNum)))
    nil))

(defun add-trees-to-tree-db-from-list
  (analysis-id rooted? brlens? list curTreeNum db)
  (declare (xargs :guard (and (natp curTreeNum)
                              (alistp db))))
  (if (consp list)
      (add-trees-to-tree-db-from-list
       analysis-id rooted? brlens? (cdr list)
       (1+ curTreeNum)
       (acons curTreeNum
             (acons 'analysis-id analysis-id
                    (acons 'rooted? rooted?
                           (acons 'brlens? brlens?
                                  (acons 'tree (car list) nil))))
             db))
    db))

