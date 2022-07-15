;; This version of COMPOSE can only handle functions which take one
;; value and return one value. There are other ways of writing
;; COMPOSE, but this is the most commonly used.

(in-package :cl-utilities)

;; This is really slow and conses a lot. Fortunately we can speed it
;; up immensely with a compiler macro.
(defun compose (&rest functions)
  "Compose FUNCTIONS right-associatively, returning a function"
  #'(lambda (x)
      (reduce #'funcall functions
	      :initial-value x
	      :from-end t)))

;; Here's some benchmarking code that compares various methods of
;; doing the same thing. If the first method, using COMPOSE, is
;; notably slower than the rest, the compiler macro probably isn't
;; being run.
#+nil
(labels ((2* (x) (* 2 x)))
  (macrolet ((repeat ((x) &body body)
	       (with-unique-names (counter)
		 `(dotimes (,counter ,x)
		   (declare (type (integer 0 ,x) ,counter)
		            (ignorable ,counter))
		   ,@body))))
    ;; Make sure the compiler macro gets run
    (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
    (time (repeat (30000000) (funcall (compose #'1+ #'2* #'1+) 6)))
    (time (repeat (30000000) (funcall (lambda (x) (1+ (2* (1+ x)))) 6)))
    (time (repeat (30000000)
		  (funcall (lambda (x)
			     (funcall #'1+ (funcall #'2* (funcall #'1+ x))))
			   6)))))

;; Converts calls to COMPOSE to lambda forms with everything written
;; out and some things written as direct function calls.
;; Example: (compose #'1+ #'2* #'1+) => (LAMBDA (X) (1+ (2* (1+ X))))
(define-compiler-macro compose (&rest functions)
  (labels ((sharp-quoted-p (x)
	     (and (listp x)
		  (eql (first x) 'function)
		  (symbolp (second x)))))
    `(lambda (x) ,(reduce #'(lambda (fun arg)
			      (if (sharp-quoted-p fun)
				  (list (second fun) arg)
				  (list 'funcall fun arg)))
			  functions
			  :initial-value 'x
			  :from-end t))))