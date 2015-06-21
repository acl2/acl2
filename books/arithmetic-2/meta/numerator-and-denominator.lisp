; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; numerator-and-denominator.lisp
;;
;;
;; Some simple facts about numerator and denominator.
;;
;; This book needs to be expanded some day.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type-set already knows that (numerator x) and (denominator x)
;; are integers, and that 0 < (denominator x).

(defthm |(* (/ (denominator x)) (numerator x))|
  (implies (rationalp x)
           (equal (* (/ (denominator x)) (numerator x))
                  x)))

(local (in-theory (enable rewrite-linear-equalities-to-iff)))

(defthm |(< 0 (numerator x))|
  (implies (rationalp x)
	   (equal (< 0 (numerator x))
		  (< 0 x))))

(defthm numerator-type-prescription-positive
  (implies (and (rationalp x)
                (< 0 x))
           (< 0 (numerator x)))
  :rule-classes :type-prescription)

(defthm numerator-type-prescription-non-negative
  (implies (and (rationalp x)
                (<= 0 x))
           (<= 0 (numerator x)))
  :rule-classes :type-prescription)

(defthm |(< (numerator x) 0)|
  (implies (rationalp x)
	   (equal (< (numerator x) 0)
		  (< x 0))))

(defthm numerator-type-prescription-negative
  (implies (and (rationalp x)
                (< x 0))
           (< (numerator x) 0))
  :rule-classes :type-prescription)

(defthm numerator-type-prescription-non-positive
  (implies (and (rationalp x)
                (<= x 0))
           (<= (numerator x) 0))
  :rule-classes :type-prescription)

(defthm |(numerator (- i))|
   (equal (numerator (- i))
          (- (numerator i))))

(defthm |(denominator (- x))|
  (implies (rationalp x)
           (equal (denominator (- x))
                  (denominator x))))

(defthm |integerp x in (numerator x)|
  (implies (integerp x)
	   (equal (numerator x)
		  x)))

(defthm |integerp x in (denominator x)|
  (implies (integerp x)
           (equal (denominator x)
		  1)))

(defthm |(equal (denominator x) 1)|
  (equal (equal (denominator x) 1)
         (or (integerp x)
             (not (rationalp x)))))

(defthm |(* r (denominator r))|
  (equal (* r (denominator r))
         (if (rationalp r)
             (numerator r)
           (fix r))))
