; A lightweight book about the built-in function unary--.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm integerp-of--
  (equal (integerp (- x))
         (integerp (fix x)))
  :hints (("Goal" :cases ((integerp x)))))

(in-theory (disable rationalp-unary--)) ;rationalp-of-- is stronger

(defthm rationalp-of--
  (equal (rationalp (- x))
         (rationalp (fix x)))
  :hints (("Goal" :cases ((rationalp x)))))

(defthm --of--
  (equal (- (- x))
         (fix x)))

;; The (- k) in the conclusion gets computed.
(defthm equal-of---and-constant
  (implies (syntaxp (quotep k))
           (equal (equal k (- x))
                  (and (acl2-numberp k)
                       (equal (fix x) (- k))))))

;; The (- k) in the conclusion gets computed.
(defthm <-of-minus-and-constant
  (implies (syntaxp (quotep k))
           (equal (< (- x) k)
                  (< (- k) x)))
  :hints (("Goal" :cases ((< (- x) k)))))

(defthm equal-of-minus-self
  (equal (equal x (- x))
         (equal x 0)))

(defthm equal-of---and--
  (equal (equal (- x) (- y))
         (equal (fix x) (fix y))))

(defthm <-of---and--
  (equal (< (- x) (- y))
         (< (fix y) (fix x)))
  :hints (("Goal" :cases ((< (- x) (- y))))))
