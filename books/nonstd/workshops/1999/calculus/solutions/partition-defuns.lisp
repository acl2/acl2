(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Exercise 6.1.
Define a function (partitionp p) in ACL2, which is true exactly when p
is a non-empty, strictly increasing sequence of rational numbers.
Test your function.
|#

(defun partitionp (p)
  (and (consp p)
       (rationalp (car p))
       (or (null (cdr p))
           (and (rationalp (cadr p)) ; could perhaps omit but may be useful
                (< (car p) (cadr p))
                (partitionp (cdr p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Exercise 6.2.
Define a function (make-partition a b n) which, for rational numbers a
and b and positive integer n, splits the interval from a to b into n
equal-sized subintervals by returning an appropriate sequence of
numbers from a to b, for example as follows.

ACL2 !>(make-partition 3 7 8)
(3 7/2 4 9/2 5 11/2 6 13/2 7)

Test your function, for example as shown just above.
|#

; Our approach is to define make-partition by calling a
; recursively-defined function make-partition-rec a delta n), where a
; is the left endpoint, deltad} is the length of each subinterval, and
; n is the number of subintervals.

(defun make-partition-rec (a delta n)
  (if (zp n)
      (list a)
    (cons a
          (make-partition-rec (+ a delta) delta (1- n)))))

(defun make-partition (a b n)
  (make-partition-rec a (/ (- b a) n) n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Exercise 6.3.
Define the function \ptt{(deltas p)}\funi{deltas}, which returns the ordered
list of successive intervals represented by \ptt{p} as in the following
example.
{\small
\begin{verbatim}
ACL2 !>(deltas '(12 13 15 24))
(1 2 9)
|#

(defun deltas (p)
  (if (and (consp p) (consp (cdr p)))
      (cons (- (cadr p) (car p))
            (deltas (cdr p)))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Exercise 6.4.
Define the function (mesh p), the mesh of partition p as introduced informally
in the section entitled "Brief informal review of The Fundamental Theorem of
Calculus."
|#

; Our approach is to apply to (deltas p) a function (maxlist x) that returns
; the maximum of a non-empty list x.

(defun maxlist (x)
  ;; the maximum of non-empty list x of non-negative numbers
  (if (consp x)
      (max (car x) (maxlist (cdr x)))
    0))

(defun mesh (p)
  (maxlist (deltas p)))
