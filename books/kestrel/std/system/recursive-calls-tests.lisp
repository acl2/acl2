; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "recursive-calls")

(include-book "pseudo-tests-and-call-listp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (let ((rc (recursive-calls 'len (w state))))
           (and (pseudo-tests-and-call-listp rc)
                (= (len rc) 1)
                (let ((rc1 (first rc)))
                  (and  (equal (access tests-and-call rc1 :tests)
                               '((consp x)))
                        (equal (access tests-and-call rc1 :call)
                               '(len (cdr x))))))))

(must-succeed*
 (defun fib (n)
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((rc (recursive-calls 'fib (w state))))
            (and (pseudo-tests-and-call-listp rc)
                 (= (len rc) 2)
                 (let ((rc1 (first rc)))
                   (and (equal (access tests-and-call rc1 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc1 :call)
                               '(fib (binary-+ '-1 n)))))
                 (let ((rc2 (second rc)))
                   (and (equal (access tests-and-call rc2 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc2 :call)
                               '(fib (binary-+ '-2 n)))))))))

(must-succeed*
 (defun fib (n)
   (declare (xargs :mode :program))
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((rc (recursive-calls 'fib (w state))))
            (and (pseudo-tests-and-call-listp rc)
                 (= (len rc) 2)
                 (let ((rc1 (first rc)))
                   (and (equal (access tests-and-call rc1 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc1 :call)
                               '(fib (binary-+ '-1 n)))))
                 (let ((rc2 (second rc)))
                   (and (equal (access tests-and-call rc2 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc2 :call)
                               '(fib (binary-+ '-2 n)))))))))

(must-succeed*
 (defun nonrec (x) (cons x x))
 (assert-equal (recursive-calls 'nonrec (w state)) nil))

(must-succeed*
 (defun nonrec (x) (declare (xargs :mode :program)) (cons x x))
 (assert-equal (recursive-calls 'nonrec (w state)) nil))
