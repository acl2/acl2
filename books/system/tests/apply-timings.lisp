; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

(defun posps (n acc) ; acc is nil at the top level
  (declare (xargs :guard (natp n)))
  (if (zp n)
      acc
    (posps (1- n)
           (cons n acc))))

(comp t)

(defconst *100k* (posps 100000 nil))
(defconst *million* (posps 1000000 nil))
(defconst *10M* (posps 10000000 nil))

(defun cw-apply-test-args (n args)
  (declare (xargs :guard (and (natp n)
                              (true-listp args))
                  :mode :program))
  (cond ((zp n) args)
        (t (cw-apply-test-args (1- n)
                               (cons (packn (list '*GOOD-LAMBDA n '*))
                                     args)))))

(defmacro cw-apply-test (list-to-test n)
  `(make-event
    (let ((list-to-test ,list-to-test)
          (n ,n))
      (progn$ (cw "~%Testing ~n0 lambda~#1~[~/s~] ~n2 times.~|"
                  n
                  (if (= n 1) 0 1)
                  (length list-to-test))
              (time$ (,(packn (list 'ap n))
                      list-to-test
                      ,@(cw-apply-test-args n nil)
                      0))
              (value '(value-triple :invisible))))))

(defconst *good-lambda1*
  '(lambda (x)
     (binary-+ '2 (binary-* '3 (fix x)))))

(defconst *good-lambda2*
  '(lambda (x)
     (binary-+ '4 (binary-* '5 (fix x)))))

(defconst *good-lambda3*
  '(lambda (x)
     (binary-+ '6 (binary-* '7 (fix x)))))

(defconst *good-lambda4*
  '(lambda (x)
     (binary-+ '8 (binary-* '9 (fix x)))))

(defun ap1-guard-rec (fn lst)
  (declare (xargs :guard t))
  (cond ((atom lst) t)
        (t (and (apply$-guard fn (list (car lst)))
                (ap1-guard-rec fn (cdr lst))))))

(defun ap1-guard (fn lst)
  (declare (xargs :guard t))
  (or (atom fn)
      (ap1-guard-rec fn lst)))


(defun$ ap1 (lst fn1 acc)
  (declare (xargs :guard (and (acl2-numberp acc)
                              (ap1-guard fn1 lst))))
  (cond ((atom lst) acc)
        (t (ap1 (cdr lst)
                fn1
                (+ (fix (apply$ fn1 (list (car lst))))
                   acc)))))

(defun$ ap2 (lst fn1 fn2 acc)
  (declare (xargs :guard (and (acl2-numberp acc)
                              (ap1-guard fn1 lst)
                              (ap1-guard fn2 lst))))
  (cond ((atom lst) acc)
        (t (ap2 (cdr lst)
                fn1 fn2
                (+ (fix (apply$ fn1 (list (car lst))))
                   (fix (apply$ fn2 (list (car lst))))
                   acc)))))

(defun$ ap3 (lst fn1 fn2 fn3 acc)
  (declare (xargs :guard (and (acl2-numberp acc)
                              (ap1-guard fn1 lst)
                              (ap1-guard fn2 lst)
                              (ap1-guard fn3 lst))))
  (cond ((atom lst) acc)
        (t (ap3 (cdr lst)
                fn1 fn2 fn3
                (+ (fix (apply$ fn1 (list (car lst))))
                   (fix (apply$ fn2 (list (car lst))))
                   (fix (apply$ fn3 (list (car lst))))
                   acc)))))

(defun$ ap4 (lst fn1 fn2 fn3 fn4 acc)
  (declare (xargs :guard (and (acl2-numberp acc)
                              (ap1-guard fn1 lst)
                              (ap1-guard fn2 lst)
                              (ap1-guard fn3 lst)
                              (ap1-guard fn4 lst))))
  (cond ((atom lst) acc)
        (t (ap4 (cdr lst)
                fn1 fn2 fn3 fn4
                (+ (fix (apply$ fn1 (list (car lst))))
                   (fix (apply$ fn2 (list (car lst))))
                   (fix (apply$ fn3 (list (car lst))))
                   (fix (apply$ fn4 (list (car lst))))
                   acc)))))

(comp t)

; Note: Each of the tests below shows approximately 16 bytes per iteration.
; That is good: it shows that there is essentially no consing by the cl-cache
; (compiled lambda cache), since each invocation of (list (car lst)) is create
; 16 bytes:

;   ? (time$ (loop for x in *million* always (list x)))
;   ; (LOOP FOR ...) took 
;   ; 0.01 seconds realtime, 0.01 seconds runtime
;   ; (16,000,000 bytes allocated).
;   T
;   ? 

; The "4" tests below run very slowly when only three cache lines are
; available.

(cw-apply-test *100k* 1)
(cw-apply-test *100k* 2)
(cw-apply-test *100k* 3)
(cw-apply-test *100k* 4)

(cw-apply-test *million* 1)
(cw-apply-test *million* 2)
(cw-apply-test *million* 3)
(cw-apply-test *million* 4)

(cw-apply-test *10M* 1)
(cw-apply-test *10M* 2)
(cw-apply-test *10M* 3)
(cw-apply-test *10M* 4)
