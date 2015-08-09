; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; pre.lisp
;;;
;;;
;;; This is the first book to be loaded.  The capitalized rules
;;; are either copied form axioms.lisp, or are renamed versions
;;; of rules in axioms.lisp.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm |Non-numeric x in (+ x y)|
  (implies (not (acl2-numberp x))
           (equal (+ x y)
                  (fix y))))

(defthm |Non-numeric y in (+ x y)|
  (implies (not (acl2-numberp y))
           (equal (+ x y)
                  (fix x))))

(defthm |Non-numeric x in (- x)|
  (implies (not (acl2-numberp x))
           (equal (- x)
                  0)))

(defthm |Non-Numeric x in (* x y)|
  (implies (not (acl2-numberp x))
           (equal (* x y)
                  0)))

(defthm |Non-Numeric y in (* x y)|
  (implies (not (acl2-numberp y))
           (equal (* x y)
                  0)))

(defthm |Non-Numeric x in (/ x)|
  (implies (or (not (acl2-numberp x))
               (equal x 0))
           (equal (/ x)
                  0)))

(defthm |Non-Numeric x in (< x y)|
  (implies (not (acl2-numberp x))
           (equal (< x y)
                  (< 0 y))))

(defthm |Non-Numeric y in (< x y)|
  (implies (not (acl2-numberp y))
           (equal (< x y)
                  (< x 0))))

(defthm |Non-Numeric x in (denominator x)|
  (implies (not (rationalp x))
           (equal (denominator x)
                  1)))

(defthm |Non-Numeric x in (numerator x)|
  (implies (not (rationalp x))
           (equal (numerator x)
                  0)))

(defthm |(+ y x)|   ; Commutativity-of-plus
  (equal (+ y x)
         (+ x y)))

(defthm |(+ y (+ x z))|
  (equal (+ y (+ x z))
         (+ x (+ y z))))

(defthm |(* y x)|   ; Commutativity-of-times
  (equal (* y x)
         (* x y)))

(defthm |(* y (* x z))|
   (equal (* y (* x z))
          (* x (* y z))))

