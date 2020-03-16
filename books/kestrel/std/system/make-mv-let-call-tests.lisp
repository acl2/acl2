; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-mv-let-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (make-mv-let-call 'mv nil :all 'mv-term 'body-term)
              '((lambda (mv) ((lambda () body-term))) mv-term))

(assert-equal (make-mv-let-call 'mv '(a) :all 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a) body-term)
                              (mv-nth '0 mv)))
                mv-term))

(assert-equal (make-mv-let-call 'mv '(a b) :all 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a b) body-term)
                              (mv-nth '0 mv)
                              (mv-nth '1 mv)))
                mv-term))

(assert-equal (make-mv-let-call 'mv '(a b c) :all 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a b c) body-term)
                              (mv-nth '0 mv)
                              (mv-nth '1 mv)
                              (mv-nth '2 mv)))
                mv-term))

(assert-equal (make-mv-let-call 'mvvv '(a b c) :all 'mv-term 'body-term)
              '((lambda (mvvv) ((lambda (a b c) body-term)
                              (mv-nth '0 mvvv)
                              (mv-nth '1 mvvv)
                              (mv-nth '2 mvvv)))
                mv-term))

(assert-equal (make-mv-let-call 'mv '(a b c) '(3 5 8) 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a b c) body-term)
                              (mv-nth '3 mv)
                              (mv-nth '5 mv)
                              (mv-nth '8 mv)))
                mv-term))

(assert-equal (make-mv-let-call 'x '(a b c) '(3 5 8) 'mv-term 'body-term)
              '((lambda (x) ((lambda (a b c) body-term)
                             (mv-nth '3 x)
                             (mv-nth '5 x)
                             (mv-nth '8 x)))
                mv-term))
