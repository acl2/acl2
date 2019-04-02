; Integer Arithmetic -- Rules
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "operations")

(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Each of these rules are integer counterparts of
; either built-in axioms or rules in [books]/arithmetic/top,
; whose names are indicated next to each rule.
; The rules asserting that i+, i*, and i- return integers
; correspond to "implicit" type prescription rules in ACL2,
; which knows that +, *, and - return acl2-numberp
; without explicit type prescription rules in the world.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable i* i+ i-)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-i* ; implicit type prescription rule for *
  (integerp (i* x y))
  :rule-classes :type-prescription)

(defthm integerp-of-i- ; implicit type prescription rule for -
  (integerp (i- x))
  :rule-classes :type-prescription)

(defthm integerp-of-i+ ; implicit type prescription rule for +
  (integerp (i+ x y))
  :rule-classes :type-prescription)

(defthm associativity-of-i* ; associativity-of-*
  (equal (i* (i* x y) z)
         (i* x (i* y z))))

(defthm associativity-of-i+ ; associativity-of-+
  (equal (i+ (i+ x y) z)
         (i+ x (i+ y z))))

(defthm commutativity-of-i* ; commutativity-of-*
  (equal (i* x y)
         (i* y x)))

(defthm commutativity-of-i+ ; commutativity-of-+
  (equal (i+ x y)
         (i+ y x)))

(defthm commutativity-2-of-i* ; commutativity-2-of-*
  (equal (i* x (i* y z))
         (i* y (i* x z))))

(defthm commutativity-2-of-i+ ; commutativity-2-of-+
  (equal (i+ x (i+ y z))
         (i+ y (i+ x z))))

(defthm integer-distributivity ; distributivity
  (equal (i* x (i+ y z))
         (i+ (i* x y) (i* x z))))

(defthm distributivity-of-iminus-over-i+ ; distributivity-of-minus-over-+
  (equal (i- (i+ x y))
         (i+ (i- x) (i- y))))

(defthm functional-commutativity-of-iminus-i*-left ; functional-commutativity-of-minus-*-left
  (equal (i* (i- x) y)
         (i- (i* x y))))

(defthm functional-commutativity-of-iminus-i*-right ; functional-commutativity-of-minus-*-right
  (equal (i* x (i- y))
         (i- (i* x y))))

(defthm functional-self-inversion-of-iminus ; functional-self-inversion-of-minus
  (equal (i- (i- x))
         (ifix x)))

(defthm inverse-of-i+ ; inverse of i+
  (equal (i+ x (i- x))
         0))

(defthm iminus-cancellation-on-left ; minus-cancellation-on-left
  (equal (i+ x (i- x) y)
         (ifix y)))

(defthm iminus-cancellation-on-right ; minus-cancellation-on-right
  (equal (i+ x y (i- x))
         (ifix y)))

(defthm i*-zero ; times-zero
  (equal (i* 0 x)
         0))

(defthm integer-unicity-of-0 ; unicity-of-0
  (equal (i+ 0 x)
         (ifix x)))

(defthm integer-unicity-of-1 ; unicity-of-1
  (equal (i* 1 x)
         (ifix x)))

(defthm nonnegative-iproduct ; nonnegative-product
  (implies (integerp x)
           (and (integerp (i* x x))
                (<= 0 (i* x x))))
  :rule-classes ((:type-prescription :typed-term (i* x x))))
