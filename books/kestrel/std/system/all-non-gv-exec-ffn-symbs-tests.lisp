; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-non-gv-exec-ffn-symbs")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro same-member-equal (x y)
  `(let ((x ,x) (y ,y))
     (and (subsetp-equal x y)
          (subsetp-equal y x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-non-gv-exec-ffn-symbs 'x (w state)) nil)

(assert-equal (all-non-gv-exec-ffn-symbs '(quote 4) (w state)) nil)

(assert-equal (all-non-gv-exec-ffn-symbs '(cons x y) (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert!
  (same-member-equal (all-non-gv-exec-ffn-symbs '(cons (f x) (g (f y)))
                                                (w state))
             '(f))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert!
  (same-member-equal (all-non-gv-exec-ffn-symbs '(cons (mycar z) (len y))
                                                (w state))
                     '(mycar)))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert-equal (all-non-gv-exec-ffn-symbs (body 'f nil (w state))
                                          (w state))
               nil))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) (cons (ec-call (f x)) (len x)))
 (assert-equal (all-non-gv-exec-ffn-symbs (body 'g nil (w state))
                                          (w state))
               nil))
