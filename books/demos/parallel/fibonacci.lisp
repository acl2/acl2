(in-package "ACL2")

; Here we fool the dependency tracker (thus removing a dependency from
; Makefile).
#||
(include-book "matrix-multiplication-parallel")
||#

(include-book "std/testing/assert-bang" :dir :system)

(set-compile-fns t)

; Serial version of Fibonacci
(defun fib (x)
  (declare (xargs :guard (natp x)))
  (cond ((mbe :logic (or (zp x) (<= x 0))
              :exec (<= x 0))
         0)
        ((= x 1) 1)
        (t (let ((a (fib (- x 1)))
                 (b (fib (- x 2))))
             (+ a b)))))

; Parallelized version of Fibonacci, using plet
(defun pfib (x)
  (declare (xargs :guard (natp x)))
  (cond ((mbe :logic (or (zp x) (<= x 0))
              :exec (<= x 0))
         0)
        ((= x 1) 1)
        (t (plet (declare (granularity (> x 30)))
                 ((a (pfib (- x 1)))
                  (b (pfib (- x 2))))
                 (+ a b)))))

(assert! (equal (fib 32) (pfib 32)))

; Parallel version of Fibonacci, using pargs
(defun pfib-with-pargs (x)
  (declare (xargs :guard (natp x)))
  (cond ((mbe :logic (or (zp x) (<= x 0))
              :exec (<= x 0))
         0)
        ((= x 1) 1)
        (t (pargs (declare (granularity (> x 30)))
                  (binary-+ (pfib-with-pargs (- x 1))
                            (pfib-with-pargs (- x 2)))))))

(assert! (equal (fib 32) (pfib-with-pargs 32)))

(defmacro assert-when-parallel (form)
  `(assert! (if (and (f-boundp-global 'parallel-evaluation-enabled state)
                     (f-get-global 'parallel-evaluation-enabled state))
                ,form
              t)))

; About 2.3 seconds on an 8-core Linux machine running
; OpenMCL Version 1.1-r7635:
(assert-when-parallel (equal (time$ (fib 39)) 63245986))

; About 0.7 seconds on an 8-core Linux machine running
; OpenMCL Version 1.1-r7635:
(assert-when-parallel (equal (time$ (pfib 39)) 63245986))

; About 0.8 seconds on an 8-core Linux machine running
; OpenMCL Version 1.1-r7635:
(assert-when-parallel (equal (time$ (pfib-with-pargs 39)) 63245986))
