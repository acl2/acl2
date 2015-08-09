(in-package "ACL2")

(include-book "../gen-helper/extra")

;; For reference
(defun valid-match-matrix-entry (x)
  (and (consp x)
       (equal (len x) 4)
       (let ((score (car x))
             (left (cadr x))
             (diag (caddr x))
             (top (cadddr x)))
         (and (rationalp score)
              ;; to keep track of where we could have come from
              (or left ;;
                  diag ;; t for direction
                  top)))))

(defun valid-i/d-matrix-entry (x)
  (and (consp x)
       (equal (len x) 4)
       (let ((score (car x))
             (diag (cadr x))
             (other (caddr x)))
         (and (rationalp score)
              ;; to keep track of where we could have come from
              (or diag
                  other))))) ;; left or top

(defun valid-matrix-entry (x)
  (and (consp x)
       (equal (len x) 3)
       (let ((match (car x))
             (insert (cadr x))
             (delete (caddr x)))
         (and (valid-match-matrix-entry match)
              (valid-i/d-matrix-entry insert)
              (valid-i/d-matrix-entry delete)))))

(defmacro match-score (x)
  `(car (car ,x)))

(defmacro insert-score (x)
  `(car (cadr ,x)))

(defmacro delete-score (x)
  `(car (caddr ,x)))

;; First row in matrix
(defun build-affine-first-row-help (raw2 gap-open gap-extend len)
  (if (consp raw2)
      (cons
       (list (list -1 -1 nil) ;match junk
             (list -1 -1 nil) ;insert junk
             (list (+ gap-open (* gap-extend len)) nil len));delete
       (build-affine-first-row-help (cdr raw2) gap-open gap-extend
                                  (1+ len)))
    nil))

(defun build-affine-first-row-top (raw2 gap-open gap-extend)
  ;; At very beginning
  (cons (list (list 0 nil nil nil) ;match
              (list gap-open -1 nil) ;insert
              (list gap-open -1 nil)) ;delete
        (build-affine-first-row-help raw2 gap-open gap-extend 1)))

;; All other rows

(defun get-cost (char1 char2 transMat)
  (cdr (assoc-equal char2 (cdr (assoc-equal char1 transmat)))))

(defmacro i-max ()
  (expt 2 (1- 28)))

(defmacro plus-neg1-inf (x y)
  `(the (signed-byte 28)
        (let ((x ,x)
              (y ,y))
          (declare (type (signed-byte 28) x y))
          (cond ((or (< x 0)
                     (< y 0))
                 -1)
                (t (let ((result
                          (the (signed-byte 29) (+ x y))))
                     (declare (type (signed-byte 29) result))
                     (cond ((>= result (i-max)) -1)
                           (t (the (signed-byte 28) result)))))))))

(defmacro <-neg1-inf (x y)
  `(let ((x ,x)
         (y ,y))
     (declare (type (signed-byte 28) x y))
     (cond ((< x 0) nil)
           ((< y 0) t)
           (t
            (< x y)))))

(defun build-affine-align-matrix-row-help
  (char raw2 transMat gap-open gap-extend prev-row diag-entry left-entry)
  (if (consp raw2)
      (let ((top-entry (car prev-row)))
        ;; Compute possible scores
        (let* ((insert-from-insert (plus-neg1-inf (insert-score top-entry)
                                    gap-extend))
               (insert-from-match (plus-neg1-inf (match-score top-entry)
                                    (+ gap-extend gap-open)))
               (delete-from-delete (plus-neg1-inf (delete-score left-entry)
                                               gap-extend))
               (delete-from-match (plus-neg1-inf (match-score left-entry)
                                    (plus-neg1-inf gap-open gap-extend)))
               (match-from-match
                (plus-neg1-inf (match-score diag-entry)
                   (get-cost char (car raw2) transMat)))
               (match-from-insert
                (plus-neg1-inf (insert-score diag-entry)
                   (get-cost char (car raw2) transMat)))
               (match-from-delete
                (plus-neg1-inf (delete-score diag-entry)
                   (get-cost char (car raw2) transMat)))
               (insert (if (<-neg1-inf insert-from-insert insert-from-match)
                           (list insert-from-insert nil t)
                         (list insert-from-match t nil)))
               (delete (if (<-neg1-inf delete-from-delete delete-from-match)
                           (list delete-from-delete nil t)
                         (list delete-from-match t nil)))
               (match (if (<-neg1-inf match-from-match
                             match-from-delete)
                          (if (<-neg1-inf match-from-match
                                 match-from-insert)
                              (list match-from-match
                                    nil t nil)
                            (list match-from-insert
                                  t nil nil))
                        (if (<-neg1-inf match-from-delete match-from-insert)
                            (list match-from-delete nil nil t)
                          (list match-from-insert t nil nil))))
               (new-entry (list match insert delete)))
          (cons new-entry
                (build-affine-align-matrix-row-help
                 char (cdr raw2) transMat gap-open gap-extend
                 (cdr prev-row) top-entry new-entry))))
    nil))


(defun build-affine-align-matrix-row-top (char raw2 transMat gap-open
                                           gap-extend prev-row)
  (if (consp prev-row)
      (let* ((first-above-entry (car prev-row))
             (first-insert-score (insert-score first-above-entry))
             (new-score (plus-neg1-inf first-insert-score gap-extend))
             (new-entry (list (list -1 t t t) ;; not useful
                              (list new-score nil t)  ;; matters
                              (list -1 t nil) ;; random noise
                              )))
        (cons new-entry
              (build-affine-align-matrix-row-help
               char raw2 transMat gap-open gap-extend (cdr prev-row)
               first-above-entry new-entry)))
    "Error: Prev-row has to have something in it"))


(defun build-affine-align-matrix-rows (raw1 raw2 transMat gap-open
                                            gap-extend prev-row acc)
  (if (consp raw1)
      (let ((new-row (build-affine-align-matrix-row-top
                      (car raw1)
                      raw2 transMat gap-open gap-extend prev-row)))
        (build-affine-align-matrix-rows (cdr raw1) raw2 transMat gap-open
                                        gap-extend new-row
                                        (cons new-row acc)))
    acc))

(defun build-affine-align-matrix (raw1 raw2 transMat gap-open
                                       gap-extend)
  ;; Build-first row aligning to gaps
  (let ((first-row (build-affine-first-row-top
                    raw2 gap-open gap-extend)))
    (build-affine-align-matrix-rows raw1 raw2 transMat gap-open
                                    gap-extend first-row first-row)))


;;unpacks cost-stuff to call appropriate filling functions
(defun build-align-matrix (raw1 raw2 cost-stuff)
  (if (consp cost-stuff)
      (if (equal (car cost-stuff) 'affine)
          (let ((transMat (cadr cost-stuff))
                (gap-open (caddr cost-stuff))
                (gap-extend (cadddr cost-stuff)))
            (build-affine-align-matrix raw1 raw2 transMat gap-open
                                       gap-extend))
        ;; So far this is the only one we're implementing
        "Error: Unknown gap penalty type")
    "Error: Need good cost-stuff in build-align-matrix-helper"))

;; Assumes matrix is row reversed (i.e. first row is actually
;; bottom row of matrix).
(defun get-score-from-matrix (align-mat)
  (if (consp align-mat)
      (if (consp (car align-mat))
          (let* ((score-entry (car (last (car align-mat))))
                 (match (match-score score-entry))
                 (insert (insert-score score-entry))
                 (delete (delete-score score-entry)))
            (if (<-neg1-inf match insert)
                (if (<-neg1-inf match delete)
                    match
                  delete)
              (if (<-neg1-inf insert delete)
                  insert
                delete)))
        "Error: Need a good alignment matrix in get-score-from-matrix")
    "Error: Need a valid alignment matrix in get-score-from-matrix"))

(defun get-pairwise-score (seq1 seq2 cost-stuff)
  (get-score-from-matrix
   (build-align-matrix seq1 seq2
                       cost-stuff)))

(defun get-distances (seq sequences cost-stuff)
  (if (consp sequences)
      (cons (get-pairwise-score seq (cdar sequences) cost-stuff)
            (get-distances seq (cdr sequences) cost-stuff))
    nil))

;; returns upper triangular portion of distance matrix
(defun distance-matrix (sequences cost-stuff)
  (if (consp sequences)
      (cons (cons (caar sequences)
                  (get-distances (cdar sequences)
                                 sequences ;;including self
                                 cost-stuff))
            (distance-matrix (cdr sequences) cost-stuff))
    nil))

#||
(include-book
 "tree-score/min-length")
(get-score-from-matrix
 (build-align-matrix '(a a t) '(a c a c t)
                     (list 'affine *dna-trans-matrix* 3 1))
 )

(get-score-from-matrix
 (build-align-matrix '(a a g) '(a g t a c)
                     (list 'affine *dna-trans-matrix* 4 1))
 )
||#