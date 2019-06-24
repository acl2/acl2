; A lightweight book about the built-in operation +.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that the rule commutativity-2-of-+ is built in to ACL2.

(defthm integerp-of-+-when-integerp-1
  (implies (integerp x)
           (equal (integerp (+ x y))
                  (integerp (fix y))))
  :hints (("Goal" :cases ((integerp y)))))

(defthm integerp-of-+-when-integerp-2
  (implies (integerp y)
           (equal (integerp (+ x y))
                  (integerp (fix x))))
  :hints (("Goal" :use (:instance integerp-of-+-when-integerp-1 (x y) (y x)))))

;; Disabled since the rules above are better
(defthmd integerp-of-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (+ x y))))

;; Should be cheap and useful when integerp-of-+-when-integerp-1 is disabled.
(defthm integerp-of-+-when-integerp-1-cheap
  (implies (integerp x)
           (equal (integerp (+ x y))
                  (integerp (fix y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm +-combine-constants
  (implies (syntaxp (and (quotep k2) ;tested first to fail fast
                         (quotep k1)))
           (equal (+ k1 k2 i)
                  (+ (+ k1 k2) i))))

(defthm equal-of-+-and-+-cancel-1
  (equal (equal (+ x y1) (+ x y2))
         (equal (fix y1) (fix y2))))

;rename
(defthm equal-of-+-and-+-cancel-hack
  (equal (equal (+ x y z) y)
         (and (equal (+ x z) 0)
              (acl2-numberp y)))
  :hints (("Goal" :cases ((equal (+ x z) 0)))))

;rename
(defthm <-+-cancel-1
  (equal (< (+ x y) x)
         (< y 0))
  :hints (("Goal" :cases ((< y 0)))))

;rename
(defthm <-+-cancel-2
  (equal (< x (+ x y))
         (< 0 y))
  :hints (("Goal" :cases ((< 0 y)))))

;rename
(defthm <-of-+-and-+-cancel-1
  (equal (< (+ x y) (+ x z))
         (< y z))
  :hints (("Goal" :cases ((< y z)))))

(defthm <-of-+-combine-constants-1
  (implies (syntaxp (and (quotep k2)
                         (quotep k1)))
           (equal (< k1 (+ k2 x))
                  (< (- k1 k2) x)))
  :hints (("Goal" :cases ((< k1 (+ k2 x))))))

(defthm <-of-+-combine-constants-2
  (implies (syntaxp (and (quotep k2)
                         (quotep k1)))
           (equal (< (+ k1 x) k2)
                  (< x (- k2 k1))))
  :hints (("Goal" :cases ((< (+ k1 x) k2)))))
