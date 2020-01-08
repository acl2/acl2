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

(include-book "misc/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (make-mv-let-call nil 'mv-term 'body-term)
              '((lambda (mv) ((lambda () body-term))) mv-term))

(assert-equal (make-mv-let-call '(a) 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a) body-term)
                              (mv-nth '0 mv)))
                mv-term))

(assert-equal (make-mv-let-call '(a b) 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a b) body-term)
                              (mv-nth '0 mv)
                              (mv-nth '1 mv)))
                mv-term))

(assert-equal (make-mv-let-call '(a b c) 'mv-term 'body-term)
              '((lambda (mv) ((lambda (a b c) body-term)
                              (mv-nth '0 mv)
                              (mv-nth '1 mv)
                              (mv-nth '2 mv)))
                mv-term))
