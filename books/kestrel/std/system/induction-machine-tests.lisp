; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "induction-machine")

(include-book "system/pseudo-tests-and-calls-listp" :dir :system)

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (let ((im (induction-machine 'len (w state))))
           (and (pseudo-tests-and-calls-listp im)
                (= (len im) 2)
                (let ((im1 (first im)))
                  (and (equal (access tests-and-calls im1 :tests)
                              '((consp x)))
                       (equal (access tests-and-calls im1 :calls)
                              '((len (cdr x))))))
                (let ((im2 (second im)))
                  (and (equal (access tests-and-calls im2 :tests)
                              '((not (consp x))))
                       (equal (access tests-and-calls im2 :calls)
                              nil))))))

(must-succeed*
 (defun fib (n)
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((im (induction-machine 'fib (w state))))
            (and (pseudo-tests-and-calls-listp im)
                 (= (len im) 3)
                 (let ((im1 (first im)))
                   (and (equal (access tests-and-calls im1 :tests)
                               '((zp n)))
                        (equal (access tests-and-calls im1 :calls)
                               nil)))
                 (let ((im2 (second im)))
                   (and (equal (access tests-and-calls im2 :tests)
                               '((not (zp n))
                                 (= n '1)))
                        (equal (access tests-and-calls im2 :calls)
                               nil)))
                 (let ((im3 (third im)))
                   (and (equal (access tests-and-calls im3 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-calls im3 :calls)
                               '((fib (binary-+ '-1 n))
                                 (fib (binary-+ '-2 n))))))))))
