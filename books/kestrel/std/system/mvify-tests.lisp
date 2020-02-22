; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "mvify")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mvify '(cons x (cons y 'nil)))
              '(mv x y))

(assert-equal (mvify '(cons x (cons y (cons z (cons w 'nil)))))
              '(mv x y z w))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mvify '(f a b))
              '(f a b))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mvify '(if a (f u) (g v)))
              '(if a (f u) (g v)))

(assert-equal (mvify '(if (cons x (cons y 'nil)) (f u) (g v)))
              '(if (cons x (cons y 'nil)) (f u) (g v)))

(assert-equal (mvify '(if a (cons x (cons y 'nil)) (g v)))
              '(if a (mv x y) (g v)))

(assert-equal (mvify '(if a (f u) (cons x (cons y 'nil))))
              '(if a (f u) (mv x y)))

(assert-equal (mvify '(if a (cons x (cons y 'nil)) (cons z (cons w 'nil))))
              '(if a (mv x y) (mv z w)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mvify '(return-last a (f u) (g v)))
              '(return-last a (f u) (g v)))

(assert-equal (mvify '(return-last (cons x (cons y 'nil)) (f u) (g v)))
              '(return-last (cons x (cons y 'nil)) (f u) (g v)))

(assert-equal (mvify '(return-last a (cons x (cons y 'nil)) (g v)))
              '(return-last a (mv x y) (g v)))

(assert-equal (mvify '(return-last a (f u) (cons x (cons y 'nil))))
              '(return-last a (f u) (mv x y)))

(assert-equal (mvify
               '(return-last a (cons x (cons y 'nil)) (cons z (cons w 'nil))))
              '(return-last a (mv x y) (mv z w)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mvify '((lambda (a b) (f a b)) 'anything :anything))
              '((lambda (a b) (f a b)) 'anything :anything))

(assert-equal (mvify '((lambda (u) (cons x (cons y 'nil))) anything))
              '((lambda (u) (mv x y)) anything))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mvify
               '((lambda (u) (if a
                                 (cons x (cons y (cons z 'nil)))
                               (return-last a (h a) (cons u (cons v 'nil)))))
                 '3/4))
              '((lambda (u) (if a
                                (mv x y z)
                              (return-last a (h a) (mv u v))))
                '3/4))
