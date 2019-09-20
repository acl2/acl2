; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-mbe")

(include-book "misc/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-mbe-logic-from-term 'x) 'x)

(assert-equal (remove-mbe-logic-from-term '(quote 0)) '(quote 0))

(assert-equal (remove-mbe-logic-from-term '(f x y z)) '(f x y z))

(assert-equal (remove-mbe-logic-from-term '((lambda (a b) (cons a b))
                                            x '(1 2 3)))
              '((lambda (a b) (cons a b))
                x '(1 2 3)))

(assert-equal (remove-mbe-logic-from-term '(return-last 'mbe1-raw (f x) (g y)))
              '(f x))

(assert-equal (remove-mbe-logic-from-term '(g x (return-last 'mbe1-raw a b)))
              '(g x a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-mbe-exec-from-term 'x) 'x)

(assert-equal (remove-mbe-exec-from-term '(quote 0)) '(quote 0))

(assert-equal (remove-mbe-exec-from-term '(f x y z)) '(f x y z))

(assert-equal (remove-mbe-exec-from-term '((lambda (a b) (cons a b))
                                           x '(1 2 3)))
              '((lambda (a b) (cons a b))
                x '(1 2 3)))

(assert-equal (remove-mbe-exec-from-term '(return-last 'mbe1-raw (f x) (g y)))
              '(g y))

(assert-equal (remove-mbe-exec-from-term '(g x (return-last 'mbe1-raw a b)))
              '(g x b))
