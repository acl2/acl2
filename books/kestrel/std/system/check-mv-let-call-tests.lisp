; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-mv-let-call")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro check-mv-let-call-untrans (x)
  `(b* (((mv & term &)
         (translate1-cmp ',x :stobjs-out '((:stobjs-out . :stobjs-out))
                         t 'top (w state) (default-state-vars nil))))
     (mv-list 6 (check-mv-let-call term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 6 (check-mv-let-call 'var))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '(quote "const")))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '(f a b c)))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (x) (cons x x)) y)))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda () (body))))
                                              mv-val)))
              '(t mv nil nil mv-val (body)))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda (a) (body a))
                                                 (mv-nth '0 mv)))
                                              mv-val)))
              '(t mv (a) (0) mv-val (body a)))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda (a b) (body a b))
                                                 (mv-nth '0 mv)
                                                 (mv-nth '1 mv)))
                                              mv-val)))
              '(t mv (a b) (0 1) mv-val (body a b)))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda (a b c) (body a b c))
                                                 (mv-nth '0 mv)
                                                 (mv-nth '1 mv)
                                                 (mv-nth '2 mv)))
                                              mv-val)))
              '(t mv (a b c) (0 1 2) mv-val (body a b c)))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mvvv)
                                                ((lambda (a b) (body a b))
                                                 (mv-nth '0 mv)
                                                 (mv-nth '1 mv)))
                                              mv-val)))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda (a b) (body a b))
                                                 (mv-nth '1 mv)
                                                 (mv-nth '0 mv)))
                                              mv-val)))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda (a b) (body a b))
                                                 (f mv)
                                                 (g mv)))
                                              mv-val)))
              '(nil nil nil nil nil nil))

(assert-equal (mv-list 6 (check-mv-let-call '((lambda (mv)
                                                ((lambda (x z) (cons x z))
                                                 (mv-nth '0 mv)
                                                 (mv-nth '2 mv)))
                                              mv-val)))
              '(t mv (x z) (0 2) mv-val (cons x z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f (x) (mv x x))

(assert-equal (check-mv-let-call-untrans (mv-let (x y) (f u) (cons x y)))
              '(t mv (x y) (0 1) (f u) (cons x y)))

(assert-equal (check-mv-let-call-untrans (mv-let (x y) (f mv) (list x y mv)))
              '(t mv0 (x y) (0 1) (f mv) (cons x (cons y (cons mv 'nil)))))
