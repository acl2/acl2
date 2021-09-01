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

(defthm equal-of-+-cancel-same
  (equal (equal (+ x y) x)
         (and (equal 0 (fix y))
              (acl2-numberp x))))

(defthm equal-of-+-cancel-same-alt
  (equal (equal x (+ x y))
         (and (equal 0 (fix y))
              (acl2-numberp x))))

(defthm equal-of-+-cancel-same-alt-2
  (equal (equal x (+ y x))
         (and (equal 0 (fix y))
              (acl2-numberp x))))

(defthm equal-of-+-cancel-same-3
  (equal (equal (+ y x) x)
         (and (equal 0 (fix y))
              (acl2-numberp x))))

(defthm equal-of-+-and-+-cancel-1
  (equal (equal (+ x y1) (+ x y2))
         (equal (fix y1) (fix y2))))

;rename
(defthm equal-of-+-and-+-cancel-hack
  (equal (equal (+ x y z) y)
         (and (equal (+ x z) 0)
              (acl2-numberp y)))
  :hints (("Goal" :cases ((equal (+ x z) 0)))))

;;;
;;; cancellation rules for < (TODO: Make this more systematic)
;;;

(defthm <-of-+-cancel-1+-1
  (equal (< (+ x y) x)
         (< y 0))
  :hints (("Goal" :cases ((< y 0)))))

(defthm <-of-+-cancel-1-1+
  (equal (< x (+ x y))
         (< 0 y))
  :hints (("Goal" :cases ((< 0 y)))))

(defthm <-of-+-cancel-1+-1+
  (equal (< (+ x y) (+ x z))
         (< y z))
  :hints (("Goal" :cases ((< y z)))))

(defthm <-of-+-cancel-1-2
  (equal (< x (+ y x))
         (< 0 y))
  :hints (("Goal" :cases ((< 0 y)))))

(defthm <-of-+-cancel-1+-2
  (equal (< (+ x y) (+ z x))
         (< y z)))

(defthm <-of-+-cancel-2-1
  (equal (< (+ y x) x)
         (< y 0))
  :hints (("Goal" :cases ((< y 0)))))

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

(defthm equal-of-+-combine-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (equal k1 (+ k2 x))
                  (and (acl2-numberp k1)
                       (equal (- k1 k2) (fix x)))))
  :hints (("Goal" :cases ((equal k1 (+ k2 x))))))

(defthm rationalp-of-+-when-rationalp-arg1
  (implies (rationalp x)
           (equal (rationalp (+ x y))
                  (rationalp (fix y))))
  :hints (("Goal" :cases ((rationalp (fix y))))))

(defthm rationalp-of-+-when-rationalp-arg2
  (implies (rationalp y)
           (equal (rationalp (+ x y))
                  (rationalp (fix x))))
  :hints (("Goal" :cases ((rationalp (fix x))))))

(in-theory (disable rationalp-+)) ;the rules above are better

(defthm <-of-+-arg1-when-negative-constant
  (implies (and (syntaxp (quotep k))
                (< k 0))
           (equal (< (+ k x) y)
                  (< x (+ (- k) y))))
  :hints (("Goal" :cases ((< (+ k x) y)))))

(defthm <-of-+-arg2-when-negative-constant
  (implies (and (syntaxp (quotep k))
                (< k 0))
           (equal (< y (+ k x))
                  (< (+ (- k) y) x)))
  :hints (("Goal" :cases ((< y (+ k x))))))

;; One rule may suffice here since equal can match either way.  In rare cases,
;; this can cause problems, e.g., when we have a rule for (equal x ...), or
;; want to substitute for x, since in the RHS, x is not equated to anything.
(defthm equal-of-+-when-negative-constant
  (implies (and (syntaxp (quotep k))
                (< k 0) ;; not logically necessary
                )
           (equal (equal x (+ k y))
                  (and (equal (+ (- k) x) (fix y))
                       (acl2-numberp x)))))

;; Consider enabling
(defthmd <-of-+-of-1-when-integers
  (implies (and (syntaxp (not (quotep y)))
                (integerp x)
                (integerp y))
           (equal (< x (+ 1 y))
                  (<= x y))))

;; Needed?
(defthmd binary-+-bring-constant-forward
  (implies (syntaxp (quotep x))
           (equal (+ y x)
                  (+ x y))))
