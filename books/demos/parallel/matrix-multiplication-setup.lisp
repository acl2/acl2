(in-package "ACL2")

; This book is shared between our serial and parallel versions of matrix
; multiplication.

(set-compile-fns t)

(defun transpose-fast-aux (matrix)
  (if (endp matrix)
      (mv nil nil)

    (let ((element-to-append (caar matrix))
          (new-row (cdar matrix)))

      (mv-let (acc new-row-list)
              (transpose-fast-aux (cdr matrix))
              (mv (cons element-to-append acc)
                  (cons new-row new-row-list))))))

(defun transpose-fast (matrix)
  (if (endp (car matrix))
      nil
    (mv-let (new-row remaining-matrix)
            (transpose-fast-aux matrix)
            (cons new-row
                  (transpose-fast remaining-matrix)))))

(defun dot-product (rowA colB acc)
  (if (endp rowA)
      acc
    (dot-product (cdr rowA)
                 (cdr colB)
                 (+ (* (car rowA) (car colB))
                    acc))))

(defun multiply-matrices-row (rowA B-left)
  (if (endp B-left)
      nil
    (cons (dot-product rowA (car B-left) 0)
          (multiply-matrices-row rowA (cdr B-left)))))

;;;;;; Matrix creation functions ;;;;;;;;;

(defun make-matrix-aux (rows cols curr-row curr-col row-acc big-acc 64bit-flag)
  (declare (xargs :mode :program))
  (cond ((equal curr-row rows)
         big-acc)
        ((equal curr-col cols)
         (make-matrix-aux rows cols (1+ curr-row) 0 nil
                          (cons row-acc big-acc)
                          64bit-flag))
        (t
         (make-matrix-aux rows cols curr-row (1+ curr-col)
                          (cons (mod (+ (* curr-row curr-col)
                                        (* 23 curr-row curr-row)
                                        (* 3 curr-col curr-col))
                                     (if 64bit-flag 3000 300))
                                row-acc)
                          big-acc 64bit-flag))))

(defun make-matrix (rows cols 64bit-flag)
  (declare (xargs :mode :program))
  (make-matrix-aux rows cols 0 0 nil nil 64bit-flag))

(defun identity-matrix-aux (i zerow a)
  (cond ((zp i) a)
        (t (identity-matrix-aux (- i 1)
                             zerow
                             (cons (update-nth (- i 1) 1 zerow) a)))))

(defun identity-matrix (n)
  (identity-matrix-aux n
                       (make-list n :initial-element 0)
                       nil))

; For testing:

(defmacro assert-when-parallel (form)
  `(assert! (if (and (f-boundp-global 'parallel-evaluation-enabled state)
                     (f-get-global 'parallel-evaluation-enabled state))
                ,form
              t)))

(defconst *a-rows* 1024)
(defconst *a-cols* 1024)
(defconst *b-rows* 1024)
(defconst *b-cols* 1024)
