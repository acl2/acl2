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

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-mbe-logic 'x) 'x)

(assert-equal (remove-mbe-logic '(quote 0)) '(quote 0))

(assert-equal (remove-mbe-logic '(f x y z)) '(f x y z))

(assert-equal (remove-mbe-logic '((lambda (a b) (cons a b))
                                  x '(1 2 3)))
              '((lambda (a b) (cons a b))
                x '(1 2 3)))

(assert-equal (remove-mbe-logic '(return-last 'mbe1-raw (f x) (g y)))
              '(f x))

(assert-equal (remove-mbe-logic '(g x (return-last 'mbe1-raw a b)))
              '(g x a))

(assert-equal (remove-mbe-logic
               '(return-last 'mbe1-raw
                             (return-last 'mbe1-raw a b)
                             (return-last 'mbe1-raw c d)))
              'a)

(assert-equal (remove-mbe-logic '(f (return-last 'progn a b)))
              '(f (return-last 'progn a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-mbe-exec 'x) 'x)

(assert-equal (remove-mbe-exec '(quote 0)) '(quote 0))

(assert-equal (remove-mbe-exec '(f x y z)) '(f x y z))

(assert-equal (remove-mbe-exec '((lambda (a b) (cons a b))
                                 x '(1 2 3)))
              '((lambda (a b) (cons a b))
                x '(1 2 3)))

(assert-equal (remove-mbe-exec '(return-last 'mbe1-raw (f x) (g y)))
              '(g y))

(assert-equal (remove-mbe-exec '(g x (return-last 'mbe1-raw a b)))
              '(g x b))

(assert-equal (remove-mbe-exec
               '(return-last 'mbe1-raw
                             (return-last 'mbe1-raw a b)
                             (return-last 'mbe1-raw c d)))
              'd)

(assert-equal (remove-mbe-exec '(f (return-last 'progn a b)))
              '(f (return-last 'progn a b)))
