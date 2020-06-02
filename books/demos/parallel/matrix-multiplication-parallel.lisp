(in-package "ACL2")

; Here we fool the dependency tracker (thus removing a dependency from
; Makefile).
#||
(include-book "matrix-multiplication-serial")
||#

(include-book "std/testing/assert-bang" :dir :system)
(include-book "make-event/embeddable-event-forms" :dir :system)
(include-book "matrix-multiplication-setup")

; We have seen errors such as the following due to compilation (see
; set-compile-fns call below).  But we have only seen problems on 64-bit Linux
; running GCL 2.6.7, so we suspect a Lisp problem.  (By the way, this was not a
; disk space or protection issue; there was plenty of disk space, and
; subsequent certification attempts succeeded [ruling out a protection issue].)

; (1)
; Compiling gazonk2.lsp.
; End of Pass 1.
; End of Pass 2.
; gcc: gazonk2.c: No such file or directory
; gcc: no input files

; (2)
; Compiling gazonk2.lsp.
; End of Pass 1.
; End of Pass 2.
; Your C compiler failed to compile the intermediate file.
;
; Error: Cannot open the file gazonk2.o.

; (3)
; Error: Cannot open the file gazonk3.data.

(set-compile-fns t)

(defun get-midpoints (left right)
  (declare (xargs :guard (and (integerp left)
                              (integerp right))
                  :mode :program))

; Returns a cons pair of two values.  The first value is the rhs boundary of
; the left portion.  The second value is the rhs boundary of the right portion.
; Note that the second value is always 1+ the first value.

; Note that when the difference is even, that the left portion will be one
; larger than the right portion.

    (let* ((difference (- right left))
           (difference-div-2 (/ difference 2))
           (first-val (floor (+ left difference-div-2) 1))
           (second-val (1+ first-val)))

      (cons first-val second-val)))

(assert! (equal (get-midpoints 4 6)
                (cons 5 6)))

(assert! (equal (get-midpoints 4 7)
                (cons 5 6)))

(defun pmultiply-matrices-aux (a b n c-lhs-row c-rhs-row c-lhs-col c-rhs-col)
  (declare (xargs :measure (* (- c-rhs-row c-lhs-row)
                              (- c-rhs-col c-lhs-col))
                  :guard (and (integerp c-lhs-row)
                              (integerp c-rhs-row)
                              (integerp c-lhs-col)
                              (integerp c-rhs-col)
                              (integerp n))
                  :mode :program)
           (type signed-byte n c-lhs-row c-rhs-row c-lhs-col c-rhs-col))


; Returns a list of updates to C

  (if (equal c-lhs-row c-rhs-row)
      (list (multiply-matrices-row (nth c-lhs-row A) B))



; Code for the case that we have multi-row by multi-col cell

    (let* ((row-midpoints (get-midpoints c-lhs-row c-rhs-row))
           (row-left-midpoint (the-fixnum (car row-midpoints)))
           (row-right-midpoint (the-fixnum (cdr row-midpoints))))


      (plet (declare (granularity (> (* (- c-rhs-row c-lhs-row)
                                        (- c-rhs-col c-lhs-col))
                                     16000)))
            ((top-updates-list
              (pmultiply-matrices-aux a b n
                                      c-lhs-row row-left-midpoint
                                      c-lhs-col c-rhs-col))
             (bottom-updates-list
              (pmultiply-matrices-aux a b n
                                      row-right-midpoint c-rhs-row
                                      c-lhs-col c-rhs-col)))
            (append top-updates-list bottom-updates-list)))))

(defun pmultiply-matrices (a b a-rows a-cols b-rows b-cols)

; returns a new matrix, c, that stores the result of multiplying matrix a and
; matrix b.

; this function introduces the potential for four way parallelism, splitting
; the work into four quarters and then unifying the updates

  (declare (xargs :guard (and (integerp a-rows)
                              (integerp a-cols)
                              (integerp b-rows)
                              (integerp b-cols)
                              (equal a-cols b-rows))
                  :mode :program)
           (ignore b-rows))
  (let* ((n a-cols) ; c dimenision
         (updates (pmultiply-matrices-aux
                   a b (1- n) 0 (1- a-rows) 0 (1- b-cols))))
    updates))

(observe$ "Running simple matrix multiplcation test.")
(assert! (let ((mini-matrix '((1 2 3) (4 5 6) (7 8 9))))
           (equal (pmultiply-matrices mini-matrix mini-matrix 3 3 3 3)
                  '((14 32 50)
                    (32 77 122)
                    (50 122 194)))))

(observe$ "Generating 32 bit source matrices A and B (parallel case).")

(assign$ a (make-matrix *a-rows* *a-cols* nil))
(assign$ b (make-matrix *b-rows* *b-cols* nil))

(observe$ "Testing the time it takes to transpose B.")

(assign$ b-transposed (time$ (transpose-fast (@ b))))

; David claims more speedup if the constants at the end of
; matrix-multiplication-setup.lisp (*a-rows* etc.) are increased.
(observe$ "Testing the time it takes to generate the results (parallel case).  ~
           It has taken approximately 10.0 seconds on an 8-core machine.")

(assert-when-parallel
 (time$ (pmultiply-matrices (@ a) (@ b-transposed)
                            *a-rows* *a-cols* *b-rows* *b-cols*)))

(observe$ "Done testing matrix multiplication (parallel case).")
