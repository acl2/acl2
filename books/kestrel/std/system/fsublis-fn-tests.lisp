; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fsublis-fn")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(quote #\c)
                          nil
                          t))
              '(nil (quote #\c)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(quote #\c)
                          nil
                          nil))
              '(nil (quote #\c)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          'y
                          nil
                          t))
              '(nil y))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          'y
                          nil
                          nil))
              '(nil y))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(f (r x) y)
                          nil
                          t))
              '(nil (g (r x) y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(f (r x) y)
                          nil
                          nil))
              '(nil (g (r x) y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(h a)
                          nil
                          t))
              '(nil (cons a y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(h a)
                          nil
                          nil))
              '((y) (h a)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '((lambda (z w) (h (cons z w))) (f a) (j c))
                          nil
                          t))
              '(nil ((lambda (z w y) (cons (cons z w) y)) (g a) (j c) y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '((lambda (z w) (h (cons z w))) (f a) (j c))
                          nil
                          nil))
              '((y) (h (cons z w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(quote #\c)
                          nil))
              '(nil (quote #\c)))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          'y
                          nil))
              '(nil y))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(f (r x) y)
                          nil))
              '(nil (g (r x) y)))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(h a)
                          nil))
              '(nil (cons a y)))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '((lambda (z w) (h (cons z w))) (f a) (j c))
                          nil))
              '(nil ((lambda (z w y) (cons (cons z w) y)) (g a) (j c) y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fsublis-fn-simple '((f . g) (h . i)) '(quote '(1 2 3)))
              '(quote '(1 2 3)))

(assert-equal (fsublis-fn-simple '((f . g) (h . i)) 'xyz)
              'xyz)

(assert-equal (fsublis-fn-simple '((f . g) (h . i))
                                 '(f (cons (g (h a) b) c) d))
              '(g (cons (g (i a) b) c) d))

(assert-equal (fsublis-fn-simple '((f . g) (h . i))
                                 '(f ((lambda (x) (cons x (h 'a))) (g b))))
              '(g ((lambda (x) (cons x (i 'a))) (g b))))
