; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "flatten-conjuncts")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro check-flatten-conjuncts-untrans (x)
  `(b* (((mv & term &)
         (translate1-cmp ',x :stobjs-out '((:stobjs-out . :stobjs-out))
                         t 'top (w state) (default-state-vars nil))))
     (flatten-conjuncts term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (flatten-conjuncts 'var)
              (list 'var))

(assert-equal (flatten-conjuncts ''18)
              (list ''18))

(assert-equal (flatten-conjuncts '(f x y))
              (list '(f x y)))

(assert-equal (flatten-conjuncts '((lambda (x) x) y))
              (list '((lambda (x) x) y)))

(assert-equal (flatten-conjuncts '(if a b 'nil))
              (list 'a 'b))

(assert-equal (flatten-conjuncts '(if a (if b c 'nil) 'nil))
              (list 'a 'b 'c))

(assert-equal (flatten-conjuncts '(if (if a b 'nil) (if c d 'nil) 'nil))
              (list 'a 'b 'c 'd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (check-flatten-conjuncts-untrans (and a b))
              (list 'a 'b))

(assert-equal (check-flatten-conjuncts-untrans (and a b c d e))
              (list 'a 'b 'c 'd 'e))

(assert-equal (check-flatten-conjuncts-untrans
               (and a (and b1 b2) c d (and e1 e2 e3)))
              (list 'a 'b1 'b2 'c 'd 'e1 'e2 'e3))
