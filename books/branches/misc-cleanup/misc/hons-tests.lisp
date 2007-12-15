(in-package "ACL2")

; Courtesy of Bob Boyer and Warren Hunt:

(include-book "qi")

(value-triple (clear-memoize-tables))

(value-triple (clear-hash-tables))

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
(defthm fib-test
  (equal (integer-length (fib 10000)) 6942))

(defn tree-depth (x)
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

(defthm quick-sanity-check (check-q))
