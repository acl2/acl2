(in-package "ACL2")

; Courtesy of Bob Boyer and Warren Hunt:

(include-book "qi")

(defun fib (x)
  (declare (xargs :guard (and (integerp x)
                              (<= 0 x))))
  (mbe
   :logic
   (cond ((zp x) 0)
         ((= x 1) 1)
         (t (+ (fib (- x 1)) (fib (- x 2)))))
   :exec
   (if (< x 2)
       x
     (+ (fib (- x 1)) (fib (- x 2))))))

#+hons
(memoize 'fib)

#+hons
(defthm fib-test0

; SBCL 1.03 has given the following error for fib-test, below, when not
; including fib-test0 first:

; Error:  Control stack exhausted (no more space for function call frames).

; Since fib is not tail-recursive, the problem presumably is that even with
; memoization, we need a control stack of size about 10000 for fib-test.  By
; putting fib-test0 first, we presumably stay within SBCL's stack size limit.

  (equal (integer-length (fib 5000)) 3471))

#+hons
(defthm fib-test
  (equal (integer-length (fib 10000)) 6942))

(defn tree-depth (x)

  ; This is the same as max-depth, but we want to
  ; hack with it so we give it another name.

  (if (atom x)
      0
    (1+ (max (tree-depth (car x))
             (tree-depth (cdr x))))))

(defun build-tree (n)
  (declare (xargs :guard t))
  (if (posp n)
      (hons (build-tree (1- n)) (build-tree (1- n)))
    nil))

#+hons
(memoize 'build-tree)

#+hons
(memoize 'tree-depth)

#+hons
(defthm build-tree-test
  (let ((n 1000))
    (equal (tree-depth (build-tree n)) n)))

(defn make-list-of-numbers (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (list n)
    (hons n (make-list-of-numbers (1- n)))))

(comp 'make-list-of-numbers)

(defun lots (n)
  (declare (xargs :guard (posp n)))
  (let* ((lots-of-numbers (make-list-of-numbers n)))
    (equal (+ (len (hons-intersection lots-of-numbers
                                      lots-of-numbers))
              (len (hons-union        lots-of-numbers
                                      lots-of-numbers))
              (len (hons-set-diff     lots-of-numbers
                                      lots-of-numbers)))
           (+ 2 (* 2 n)))))

(defthm lots-thm (lots 6000))

#+hons
(memoize 'q-ite :condition '(and (consp x) (or (consp y) (consp z))))
#+hons
(memoize 'qnorm1)
#+hons
(memoize 'qvar-n)

(defn lfoo (x) (if (atom x) 0 (+ 1 (lfoo (cdr x)))))

#+hons
(memoize 'lfoo :trace 'notinline)

(defthm l-thm (equal (lfoo (hons-copy '(a b c))) 3))

(defthm l-thm2 (equal (lfoo (hons-copy '(a b c))) 3))

(defthm quick-sanity-check (check-q))
