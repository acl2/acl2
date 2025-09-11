; A lightweight book about the built-in operation +.
;
; Copyright (C) 2019-2025 Kestrel Institute
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

;; TODO: Drop (see fold-consts-in-+)
(defthm +-combine-constants
  (implies (syntaxp (and (quotep k2) ;tested first to fail fast
                         (quotep k1)))
           (equal (+ k1 k2 i)
                  (+ (+ k1 k2) i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; NOTE ON NAMES: In these names, "n+" (for any positive integer n) means x is
;; the nth addend (1-based) and there are more addends, whereas "n" means x is
;; the nth addend and there are no more.

;; In this series, there is a + on one side of the equality and a variable on the
;; other (but see the series just below).

(defthm equal-of-+-cancel-1+
  (equal (equal (+ x y) x)
         (and (equal 0 (fix y))
              (acl2-numberp x))))

;; Only needed for Axe, as ACL2 can match equalities either way?
(defthmd equal-of-+-cancel-1+-alt
  (equal (equal x (+ x y))
         (and (equal 0 (fix y))
              (acl2-numberp x))))

(defthm equal-of-+-cancel-2
  (equal (equal (+ y x) x)
         (and (equal 0 (fix y))
              (acl2-numberp x))))

;; Only needed for Axe, as ACL2 can match equalities either way?
(defthmd equal-of-+-cancel-2-alt
  (equal (equal x (+ y x))
         (and (equal 0 (fix y))
              (acl2-numberp x))))

(defthm equal-of-+-cancel-2+
  (equal (equal (+ y1 x y2) x)
         (and (equal (+ y1 y2) 0)
              (acl2-numberp x))))

;; Only needed for Axe, as ACL2 can match equalities either way?
(defthmd equal-of-+-cancel-2+-alt
  (equal (equal x (+ y1 x y2))
         (and (equal (+ y1 y2) 0)
              (acl2-numberp x))))

(defthm equal-of-+-cancel-3
  (equal (equal (+ y1 y2 x) x)
         (and (equal (+ y1 y2) 0)
              (acl2-numberp x))))

;; Only needed for Axe, as ACL2 can match equalities either way?
(defthmd equal-of-+-cancel-3-alt
  (equal (equal x (+ y1 y2 x))
         (and (equal (+ y1 y2) 0)
              (acl2-numberp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm equal-of-+-and-+-cancel-1+-1+
  (equal (equal (+ x y1) (+ x y2))
         (equal (fix y1) (fix y2))))

(defthm equal-of-+-and-+-cancel-1+-2
  (equal (equal (+ x y1) (+ y2 x))
         (equal (fix y1) (fix y2))))

;; Only needed for Axe, since ACL2 can match equalities either way?
(defthmd equal-of-+-and-+-cancel-2-1+
  (equal (equal (+ y1 x) (+ x y2))
         (equal (fix y1) (fix y2))))

(defthm equal-of-+-and-+-cancel-2-2
  (equal (equal (+ y1 x) (+ y2 x))
         (equal (fix y1) (fix y2))))

(defthm equal-of-+-and-+-cancel-1+-2+
  (equal (equal (+ x y1) (+ y2 x y3))
         (equal (fix y1) (+ y2 y3))))

(defthm equal-of-+-and-+-cancel-2+-2+
  (equal (equal (+ y1 x y2) (+ y3 x y4))
         (equal (+ y1 y2) (+ y3 y4))))

(defthm equal-of-+-and-+-cancel-3-3
  (equal (equal (+ y1 y2 x) (+ y3 y4 x))
         (equal (+ y1 y2) (+ y3 y4))))

(defthm equal-of-+-and-+-cancel-3-1+
  (equal (equal (+ y1 y2 x) (+ x y3))
         (equal (+ y1 y2) (fix y3))))

(defthm equal-of-+-and-+-cancel-2-3
  (equal (equal (+ y1 x) (+ y2 y3 x))
         (equal (fix y1) (+ y2 y3))))

(defthm equal-of-+-and-+-cancel-2-4
  (equal (equal (+ y1 x) (+ y2 y3 y4 x))
         (equal (fix y1) (+ y2 y3 y4))))

;; TODO: Consider adding more like this, but we need a meta rule to handle all
;; the cases.

;;;
;;; cancellation rules for < (TODO: Make this more systematic)
;;;

;; See the NOTE ON NAMES above.

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
         (< 0 y)))

(defthm <-of-+-cancel-1-2+
  (equal (< x (+ y x z))
         (< 0 (+ y z))))

(defthm <-of-+-cancel-1+-2+
  (equal (< (+ x w) (+ y x z))
         (< w (+ y z)))
  :hints (("Goal" :cases ((< w (+ y z))))))

(defthm <-of-+-cancel-1+-2
  (equal (< (+ x y) (+ z x))
         (< y z)))

(defthm <-of-+-cancel-2-2
  (equal (< (+ y x) (+ z x))
         (< y z)))

(defthm <-of-+-cancel-2-1+
  (equal (< (+ y x) (+ x z))
         (< y z)))

(defthm <-of-+-cancel-1-3
  (equal (< x (+ y (+ z x)))
         (< 0 (+ y z))))

(defthm <-of-+-cancel-3-1
  (equal (< (+ y (+ z x)) x)
         (< (+ y z) 0)))

(defthm <-of-+-cancel-3-1+
  (equal (< (+ y y2 x) (+ x z))
         (< (+ y y2) z)))

(defthm <-of-+-cancel-2-1
  (equal (< (+ y x) x)
         (< y 0)))

(defthm <-of-+-cancel-2+-1
  (equal (< (+ y x z) x)
         (< (+ y z) 0)))

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

(defthm <-of-+-and-+-combine-constants
  (implies (syntaxp (and (quotep k2)
                         (quotep k1)))
           (equal (< (+ k1 x) (+ k2 y))
                  (if (< k1 k2) ; ensure the new constant is non-negative
                      (< x (+ (- k2 k1) y))
                    (< (+ (- k1 k2) x) y))))
  :hints (("Goal" :cases ((< (+ k1 x) (+ k2 y))))))

(defthm equal-of-+-combine-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (equal k1 (+ k2 x))
                  (and (acl2-numberp k1)
                       (equal (- k1 k2) (fix x))))))

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
;; Without the (not (symbolp x)) below, we observed the following loop with EQUAL-OF---WHEN-VARIABLE:
;; (equal (+ 1 x) (- y)) -> (equal (+ -1 (- x)) y) -> (equal (- x) (+ 1 y)) -> (equal x (+ -1 (- y))) -> (equal (+ 1 x) (- y))
(defthm equal-of-+-when-negative-constant
  (implies (syntaxp (and (quotep k)
                         (< (unquote k) 0)
                         (if (symbolp x)
                             ;; if x is a var, don't apply unless y is also a var
                             (symbolp y)
                           t)))
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

;; Could this be too expensive?
;; Disabled since it can get rid of NATP even though that may be our normal form.
(defthmd natp-of-+-when-integerp-and-integerp
  (implies (and (integerp x)
                (integerp y))
           (equal (natp (+ x y))
                  (<= 0 (+ x y)))))

;; Could this be too expensive?
(defthm natp-of-+-when-natp-and-natp
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

(defthm equal-of-+-and-+-cancel-constants
  (implies (syntaxp (and (quotep k1)
                         (quotep k2)))
           (equal (equal (+ k1 x) (+ k2 y))
                  ;; computations with k1 and k2 here get computed:
                  (if (< k1 k2)
                      (equal (fix x) (+ (- k2 k1) y))
                    (equal (+ (- k1 k2) x) (fix y))))))

(defthmd natp-of-+-of-constant
  (implies (and (syntaxp (quotep x))
                (natp x) ; gets evaluated
                (<= (- x) y)
                (integerp y))
           (natp (+ x y)))
  :hints (("Goal" :in-theory (enable natp))))

(defthmd natp-of-+-of-constant-strong
  (implies (and (syntaxp (quotep x))
                (natp x) ; gets evaluated
                (integerp y)
                )
           (equal (natp (+ x y))
                  ;; the (- x) should get evaluated:
                  (<= (- x) y)))
  :hints (("Goal" :in-theory (enable natp))))
