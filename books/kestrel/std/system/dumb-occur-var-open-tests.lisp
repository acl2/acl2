; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dumb-occur-var-open")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (dumb-occur-var-open 'x 'x))

(assert! (not (dumb-occur-var-open 'x 'y)))

(assert! (not (dumb-occur-var-open 'x '(quote 0))))

(assert! (dumb-occur-var-open 'y '(f x (g y) z)))

(assert! (dumb-occur-var-open 'x '((lambda (z) (cons z z)) (f x))))

(assert! (not (dumb-occur-var-open 'x '((lambda (z) (cons z z)) (f y)))))

(assert! (not (dumb-occur-var-open 'z '((lambda (z) (cons z z)) (f y)))))

(assert! (dumb-occur-var-open 'w '((lambda (z) (cons w z)) (f y))))

(assert! (not (dumb-occur-var-open 'z '((lambda (z) (cons w z)) (f y)))))
