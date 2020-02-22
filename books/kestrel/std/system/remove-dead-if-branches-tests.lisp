; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "remove-dead-if-branches")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (remove-dead-if-branches 'x) 'x)

(assert-equal (remove-dead-if-branches '(quote 3)) '(quote 3))

(assert-equal (remove-dead-if-branches '(f a b)) '(f a b))

(assert-equal (remove-dead-if-branches '(if a b c)) '(if a b c))

(assert-equal (remove-dead-if-branches '(if 't a b)) 'a)

(assert-equal (remove-dead-if-branches '(if 'nil a b)) 'b)

(assert-equal (remove-dead-if-branches '(if (if 't a b) x y)) '(if a x y))

(assert-equal (remove-dead-if-branches '(if (if 'nil a b) x y)) '(if b x y))

(assert-equal (remove-dead-if-branches '(if x (if 't a b) y)) '(if x a y))

(assert-equal (remove-dead-if-branches '(if x (if 'nil a b) y)) '(if x b y))

(assert-equal (remove-dead-if-branches '(if x y (if 't a b))) '(if x y a))

(assert-equal (remove-dead-if-branches '(if x y (if 'nil a b))) '(if x y b))

(assert-equal (remove-dead-if-branches '(g (if a b c) y)) '(g (if a b c) y))

(assert-equal (remove-dead-if-branches '(g (if 't b c) y)) '(g b y))

(assert-equal (remove-dead-if-branches '(if (not 'nil) a b)) 'a)

(assert-equal (remove-dead-if-branches '(if (not 't) a b)) 'b)
