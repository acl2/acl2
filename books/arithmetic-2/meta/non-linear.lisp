; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; non-linear.lisp
;;
;;
;; This book contains some non-linear :linear rules about
;; multiplication and exponentiation.
;; See the end of this file for the theory ratio-theory-of-1
;; which is exported disabled, but is sometimes useful.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "../pass1/top"))

(local
 (include-book "cancel-terms-helper"))

(local
 (in-theory (enable prefer-*-to-/)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We do not export these lemmas.

(local
 (defthm *-preserves-<=-1
     (implies (and (<= x1 x2)
                   (<= 0 x1)
                   (<= 0 y1)
                   (real/rationalp x1)
                   (real/rationalp x2)
                   (real/rationalp y1))
              (<= (* x1 y1) (* x2 y1)))
   :rule-classes :linear))

(local
 (defthm *-preserves-<=-2
     (implies (and (<= y1 y2)
                   (<= 0 x2)
                   (<= 0 y1)
                   (real/rationalp x2)
                   (real/rationalp y1)
                   (real/rationalp y2))
              (<= (* x2 y1) (* x2 y2)))
   :rule-classes :linear))

(local
 (defthm *-preserves-<-1
     (implies (and (< x1 x2)
                   (<= 0 x1)
                   (< 0 y1)
                   (real/rationalp x1)
                   (real/rationalp x2)
                   (real/rationalp y1))
              (< (* x1 y1) (* x2 y1)))
   :rule-classes :linear))

(local
 (defthm *-preserves-<-2
     (implies (and (< y1 y2)
                   (< 0 x2)
                   (<= 0 y1)
                   (real/rationalp x2)
                   (real/rationalp y1)
                   (real/rationalp y2))
              (< (* x2 y1) (* x2 y2)))
   :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm *-preserves-<=-for-nonnegatives
    (implies (and (<= x1 x2)
                  (<= y1 y2)
                  (<= 0 x1)
                  (<= 0 y1)
                  (real/rationalp x1)
                  (real/rationalp x2)
                  (real/rationalp y1)
                  (real/rationalp y2))
             (<= (* x1 y1) (* x2 y2)))
  :rule-classes :linear)

(defthm *-preserves-<-for-nonnegatives
    (implies (and (< x1 x2)
                  (< y1 y2)
                  (<= 0 x1)
                  (<= 0 y1)
                  (real/rationalp x1)
                  (real/rationalp x2)
                  (real/rationalp y1)
                  (real/rationalp y2))
             (< (* x1 y1) (* x2 y2)))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal x1 0) (equal y1 0)))))

(defthm *-preserves-<-for-nonnegatives-stronger-1
    (implies (and (<= x1 x2)
                  (< y1 y2)
                  (< 0 x1)
                  (<= 0 y1)
                  (real/rationalp x1)
                  (real/rationalp x2)
                  (real/rationalp y1)
                  (real/rationalp y2))
             (< (* x1 y1) (* x2 y2)))
  :rule-classes :linear)

(defthm *-preserves-<-for-nonnegatives-stronger-2
    (implies (and (< x1 x2)
                  (<= y1 y2)
                  (<= 0 x1)
                  (< 0 y1)
                  (real/rationalp x1)
                  (real/rationalp x2)
                  (real/rationalp y1)
                  (real/rationalp y2))
             (< (* x1 y1) (* x2 y2)))
  :rule-classes :linear)

(local
 (in-theory (disable *-preserves-<=-1 *-preserves-<=-2
                     *-preserves-<-1 *-preserves-<-2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm *-weakly-monotonic
  (implies (and (<= y y+)
               (real/rationalp x)   ; This does not hold if x, y, and z are complex!
               (<= 0 x))
           (<= (* x y) (* x y+)))
  :hints (("Goal" :cases ((equal x 0))))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (<= y y+)
                  (real/rationalp x)
                  (<= 0 x))
             (<= (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and (<= y y+)
                  (real/rationalp x)
                  (<= 0 x))
             (<= (* y x) (* y+ x))))))

#| Here is the complex counterexample to which we alluded above.

(let ((y  #c(1 -1))
      (y+ #c(1 1))
      (x  #c(1 1)))
    (implies (and (<= y y+)
                  (<= 0 x))
             (<= (* x y) (* x y+))))
|#

(defthm *-strongly-monotonic
  (implies (and (< y y+)
                (real/rationalp x)
                (< 0 x))
           (< (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (< y y+)
                  (real/rationalp x)
                  (< 0 x))
             (< (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and (< y y+)
                  (real/rationalp x)
                  (< 0 x))
             (< (* y x) (* y+ x))))))

(defthm *-weakly-monotonic-negative-multiplier
  (implies (and (<= y y+)
               (real/rationalp x)
               (< x 0))
           (<= (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (<= y y+)
                  (real/rationalp x)
                  (< x 0))
             (<= (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and (<= y y+)
                  (real/rationalp x)
                  (< x 0))
             (<= (* y+ x) (* y x))))))

(defthm *-strongly-monotonic-negative-multiplier
  (implies (and (< y y+)
                (real/rationalp x)
                (< x 0))
           (< (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (< y y+)
                  (real/rationalp x)
                  (< x 0))
             (< (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and (< y y+)
                  (real/rationalp x)
                  (< x 0))
             (< (* y+ x) (* y x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm /-weakly-monotonic
  (implies (and (<= y y+)
                (real/rationalp y)
                (real/rationalp y+)
                (< 0 y))
           (<= (/ y+) (/ y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

(defthm /-strongly-monotonic
  (implies (and (< y y+)
                (real/rationalp y)
                (real/rationalp y+)
                (< 0 y))
           (< (/ y+) (/ y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm x*y>1-positive
   (implies (and (< 1 x)
                 (< 1 y)
                 (real/rationalp x)
                 (real/rationalp y))
    (< 1 (* x y)))
   :rule-classes (:linear :rewrite))

(defthm x*y>1-positive-stronger
   (implies (and (or (and (< 1 x)
                          (<= 1 y))
                     (and (<= 1 x)
                          (< 1 y)))
                 (real/rationalp x)
                 (real/rationalp y))
    (< 1 (* x y)))
   :rule-classes (:linear :rewrite))

(defthm x*y>=1-positive
   (implies (and (<= 1 x)
                 (<= 1 y)
                 (real/rationalp x)
                 (real/rationalp y))
    (<= 1 (* x y)))
   :rule-classes (:linear :rewrite))

(defthm x*y>1-negative
   (implies (and (< x -1)
                 (< y -1)
                 (real/rationalp x)
                 (real/rationalp y))
    (< 1 (* x y)))
  :hints (("Goal" :use ((:instance x*y>1-positive
                                   (x (- x))
                                   (y (- y))))))
   :rule-classes (:linear :rewrite))

(defthm x*y>=1-negative
   (implies (and (<= x -1)
                 (<= y -1)
                 (real/rationalp x)
                 (real/rationalp y))
    (<= 1 (* x y)))
  :hints (("Goal" :use ((:instance x*y>=1-positive
                                   (x (- x))
                                   (y (- y))))))
  :rule-classes (:linear :rewrite))

(in-theory (disable x*y>1-positive-stronger
                    x*y>1-negative x*y>=1-negative))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;  This theory is useful for proving certain types of bounds
;  properties, but will cause thrashing in linear arithmetic unless
;  the hypotheses e.g.  x <= y can be relieved.

(defthm ratio-theory-of-1-a
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= 0 x)
                (< 0 y)
                (<= x y))
           (and (<= 0 (/ x y))
                (<= (/ x y) 1)))
   :rule-classes :linear)

(defthm ratio-theory-of-1-b
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= 0 x)
                ;;(< 0 y)
                (< x y))
           (and (<= 0 (/ x y))
                (< (/ x y) 1)))
   :rule-classes :linear)

(defthm ratio-theory-of-1-c
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (< 0 x)
                (< 0 y)
                (<= y x))
           (and (< 0 (/ x y))
                (<= 1 (/ x y))))
   :rule-classes :linear)

(defthm ratio-theory-of-1-d
  (implies (and (real/rationalp x)
                (real/rationalp y)
                ;;(< 0 x)
                (< 0 y)
                (< y x))
           (and (< 0 (/ x y))
                (< 1 (/ x y))))
   :rule-classes :linear)

(defthm ratio-theory-of-1-e
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= 0 x)
                (< y 0)
                (<= x (- y)))
           (and (<= (/ x y) 0)
                (<= -1 (/ x y))))
   :rule-classes :linear)

(defthm ratio-theory-of-1-f
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= 0 x)
                ;;(< y 0)
                (< x (- y)))
           (and (<= (/ x y) 0)
                (< -1 (/ x y))))
   :rule-classes :linear)

(defthm ratio-theory-of-1-g
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (< 0 x)
                (< y 0)
                (<= (- y) x))
           (<= (/ x y) -1))
   :rule-classes :linear)

(defthm ratio-theory-of-1-h
  (implies (and (real/rationalp x)
                (real/rationalp y)
                ;;(< 0 x)
                (< y 0)
                (< (- y) x))
           (< (/ x y) -1))
   :rule-classes :linear)

(defthm ratio-theory-of-1-i
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= x 0)
                (< 0 y)
                (<= (- x) y))
           (and (<= (/ x y) 0)
                (<= -1 (/ x y))))
   :rule-classes :linear)

(defthm ratio-theory-of-1-j
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= x 0)
                ;;(< 0 y)
                (< (- x) y))
           (and (<= (/ x y) 0)
                (< -1 (/ x y))))
   :rule-classes :linear)

(defthm ratio-theory-of-1-k
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (< x 0)
                (< 0 y)
                (<= y (- x)))
           (<= (/ x y) -1))
   :rule-classes :linear)

(defthm ratio-theory-of-1-l
  (implies (and (real/rationalp x)
                (real/rationalp y)
                ;;(< x 0)
                (< 0 y)
                (< y (- x)))
           (< (/ x y) -1))
   :rule-classes :linear)

(defthm ratio-theory-of-1-m
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (< x 0)
                (< y 0)
                (<= x y))
           (<= 1 (/ x y)))
   :rule-classes :linear)

(defthm ratio-theory-of-1-n
  (implies (and (real/rationalp x)
                (real/rationalp y)
                ;;(< x 0)
                (< y 0)
                (< x y))
           (< 1 (/ x y)))
   :rule-classes :linear)

(defthm ratio-theory-of-1-o
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= x 0)
                (< y 0)
                (<= y x))
           (and (<= 0 (/ x y))
                (<= (/ x y) 1)))
   :rule-classes :linear)

(defthm ratio-theory-of-1-p
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= x 0)
                ;;(< y 0)
                (< y x))
           (and (<= 0 (/ x y))
                (< (/ x y) 1)))
  :rule-classes :linear)

(deftheory ratio-theory-of-1
  '(ratio-theory-of-1-a ratio-theory-of-1-b
    ratio-theory-of-1-c ratio-theory-of-1-d
    ratio-theory-of-1-e ratio-theory-of-1-f
    ratio-theory-of-1-g ratio-theory-of-1-h
    ratio-theory-of-1-i ratio-theory-of-1-j
    ratio-theory-of-1-k ratio-theory-of-1-l
    ratio-theory-of-1-m ratio-theory-of-1-n
    ratio-theory-of-1-o ratio-theory-of-1-p))

(in-theory (disable ratio-theory-of-1))



