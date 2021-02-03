(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "make-event/embeddable-event-forms" :dir :system)
(include-book "matrix-multiplication-setup")

; NOTE: See the comment at this same point in
; matrix-multiplication-parallel.lisp about apparently 64-bit GCL issues.

(set-compile-fns t)

(defun multiply-matrices-aux (A B)
  (declare (xargs :mode :program))
  (if (endp A)
      nil
    (cons (multiply-matrices-row (car A) B)
          (multiply-matrices-aux (cdr A) B))))

(defun multiply-matrices (A B)
  (declare (xargs :mode :program))
  (multiply-matrices-aux A B))


(observe$ "Running simple matrix multiplcation test.")
(assert! (let ((mini-matrix '((1 2 3) (4 5 6) (7 8 9))))
           (equal (multiply-matrices mini-matrix mini-matrix)
                  '((14 32 50)
                    (32 77 122)
                    (50 122 194)))))

(observe$ "Generating 32 bit source matrices A and B (serial case).")

(assign$ a (make-matrix *a-rows* *a-cols* nil))
(assign$ b (make-matrix *b-rows* *b-cols* nil))

(observe$ "Testing the time it takes to transpose B.")

(assign$ b-transposed (time$ (transpose-fast (@ b))))

(observe$ "Testing the time it takes to generate the results (serial case).  ~
           It takes approximately 22.6 seconds on our machine.")

(assert-when-parallel
  (time$ (multiply-matrices (@ a) (@ b-transposed))))

(observe$ "Done testing matrix multiplication (serial case).")
