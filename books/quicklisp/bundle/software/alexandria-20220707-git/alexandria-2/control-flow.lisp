(in-package :alexandria-2)

(defun line-up-iter (thread-first-p acc forms)
  "Iterative implementation for `thread-iter'.

The THREAD-FIRST-P decides where to thread the FORMS, accumulating in ACC."
  (if forms
      (line-up-iter thread-first-p
                   (let ((form (car forms)))
                     (if (listp form)
                         (if thread-first-p
                             (apply #'list (car form) acc (cdr form))
                             (append form (cons acc nil)))
                         (list form acc)))
                   (cdr forms))
      acc))

(defmacro line-up-first (&rest forms)
  "Lines up FORMS elements as the first argument of their successor.
Example:

 (line-up-first
   5
   (+ 20)
   /
   (+ 40))

is equivalent to:

 (+ (/ (+ 5 20)) 40)

Note how the single '/ got converted into a list before
threading."
  (line-up-iter t (car forms) (cdr forms)))

(defmacro line-up-last (&rest forms)
  "Lines up FORMS elements as the last argument of their successor.
Example:

 (line-up-last
   5
   (+ 20)
   /
   (+ 40))

is equivalent to:

    (+ 40 (/ (+ 20 5)))

Note how the single '/ got converted into a list before
threading."
  (line-up-iter nil (car forms) (cdr forms)))
