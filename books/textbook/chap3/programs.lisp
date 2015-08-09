(in-package "ACL2")

; ============================================================

; Exercise 3.10

; Define the Fibonacci function, (fib n), so that on successive integer values
; of n starting at 0, the function returns 1, 1, 2, 3, 5, 8, 13, ....

(defun fib (n)
  (if (or (zp n) (int= n 1))
      1
    (+ (fib (1- n)) (fib (- n 2)))))

; ============================================================

; Exercise 3.11

; Define (pascal i j) to be the binomial coefficient so that it returns the jth
; entry in the ith row of ``Pascal's triangle,''

;
;                      1
;                   1     1
;                1     2     1
;             1     3     3     1
;          1     4     6     4     1
;       1     5    10    10     5     1
;    1     6    15    20    15     6     1
; ...                 ...                 ...

; For example, (pascal 6 2) is 15.

(defun pascal (i j)
  (if (or (zp i) (zp j) (equal i j))
      1
    (+ (pascal (1- i) (1- j))
       (pascal (1- i) j))))

;============================================================

; Exercise 3.12

; Define (subset x y) to return t if every element of x is an element of y, and
; nil, otherwise.

; Here is the function mem defined earlier in the text:

(defun mem (e x)
  (if (endp x)
      nil
    (if (equal e (car x))
        t
      (mem e (cdr x)))))

(defun subset (x y)
  (if (endp x)
      t
    (and (mem (car x) y)
         (subset (cdr x) y))))

; ============================================================

; Exercise 3.13

; Define (un x y) to return a list with the property that e is an element of
; the list iff either e is an element of x or e is an element of y, and
; moreover, if neither x nor y has duplicate elements then (un x y) has no
; duplicate elements.

(defun un (x y)
  (cond ((endp x)
         y)
        ((mem (car x) y)
         (un (cdr x) y))
        (t
         (cons (car x) (un (cdr x) y)))))

; ============================================================

; Exercise 3.14

; Define (int x y) to return a list with the property that e is an element of
; the list iff e is an element of x and e is an element of y.

(defun int (x y)
  (cond ((endp x)
         nil)
        ((mem (car x) y)
         (cons (car x)
               (int (cdr x) y)))
        (t
         (int (cdr x) y))))

; ============================================================

; Exercise 3.15

; Define (diff x y) to return a list with the property that e is an element of
; the list iff e is an element of x and e is not an element of y.

(defun diff (x y)
  (cond ((endp x)
         nil)
        ((mem (car x) y)
         (diff (cdr x) y))
        (t
         (cons (car x) (diff (cdr x) y)))))

; ============================================================

; Exercise 3.16

; Define (rev x) to return the list containing the elements of x in the reverse
; order.  For example, (rev '(a b a c d)) should return (d c a b a).

(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

; ============================================================

; Exercise 3.17

; Define (isort x) to return a list containing the elements of x in ascending
; order.  You may assume x is a list of numbers.  For example, (isort '(4 1 0 9
; 7 4)) should return (0 1 4 4 7 9).

; Here is the function insert as defined in the book.
(defun insert (n x)
  (cond ((endp x) (list n))
        ((< n (car x)) (cons n x))
        (t (cons (car x) (insert n (cdr x))))))

(defun isort (x)
  (if (endp x)
      nil
    (insert (car x) (isort (cdr x)))))

; ============================================================

; Exercise 3.18

; Define (flatten x) to return the list of tips of the binary tree x, in the
; order in which they are encountered in a left-to-right sweep.  For example,
; (flatten '((a . b) . c)) should return (a b c).

(defun flatten (x)
  (if (atom x)
      (list x)
    (append (flatten (car x)) (flatten (cdr x)))))

; ============================================================

; Exercise 3.19

; Define (swap-tree x) to return the mirror image of the binary tree x.  The
; mirror image of ((a . b) . c) is (c . (b . a)).

(defun swap-tree (x)
  (if (atom x)
      x
    (cons (swap-tree (cdr x)) (swap-tree (car x)))))

; ============================================================

; Exercise 3.20

; Define (depth x) so that it returns the length of the longest branch in the
; binary tree x.

(defun depth (x)
  (if (atom x)
      0
    (let ((dcar (depth (car x)))
          (dcdr (depth (cdr x))))
      (1+ (if (< dcar dcdr) dcdr dcar)))))

; ============================================================

; Exercise 3.21

; Consider the notion of a ``path'' down a binary tree to a given subtree.  Let
; a path be given by a list of A's and D's indicating which way you should go
; at each cons.  The length of the path indicates how many steps to take to
; reach the subtree in question.  For example, the path to the second 2 in ((1
; . (2 . 2)) . 3) is (A D D).  Define the function (subtree p x) to return the
; subtree at the end of path p in tree x.

(defun subtree (p x)
  (cond
   ((endp p)
    x)
   ((eq (car p) 'a)
    (subtree (cdr p) (car x)))
   (t ; (eq (car p) 'd)
    (subtree (cdr p) (cdr x)))))

; ============================================================

; Exercise 3.22

; Define the function (replace-subtree p new x) to replace the subtree at the
; end of path p with the subtree new in tree x.  See the preceding exercise.

(defun replace-subtree (p new x)
  (cond
   ((endp p)
    new)
   ((eq (car p) 'a)
    (cons (replace-subtree (cdr p) new (car x))
          (cdr x)))
   (t ; (eq (car p) 'd)
    (cons (car x)
          (replace-subtree (cdr p) new (cdr x))))))

; ============================================================

; Exercise 3.23

; Define (deep-tip x) so that it returns a tip (leaf) of the binary tree x with
; the property that the tip occurs maximally deep in the tree.  Thus, (deep-tip
; '((a . b) . c)) might return a or might return b (both occur at depth 2), but
; it would not return c, which occurs at depth 1.

; Here is a solution that does not use multiple values.  Notice that
; the depth of a subtree may be calculated multiple times.

(defun deep-tip-1 (x)
  (cond ((atom x) x)
	((< (depth (car x))
	    (depth (cdr x)))
	 (deep-tip-1 (cdr x)))
	(t (deep-tip-1 (car x)))))

; Here is an alternate solution, using multiple values, that avoids
; the above problem.

(defun deep-tip-aux (x)
  (if (atom x)
      (mv x 0)
    (mv-let
     (a1 n1)
     (deep-tip-aux (car x))
     (mv-let
      (a2 n2)
      (deep-tip-aux (cdr x))
      (if (< n1 n2)
          (mv a2 (1+ n2))
        (mv a1 (1+ n1)))))))

(defun deep-tip (x)
  (mv-let (a1 n1)
          (deep-tip-aux x)
          (declare (ignore n1))
          a1))

; ============================================================
