(in-package "RTL")

(include-book "support/coprime")

(set-enforce-redundancy t)
(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; This book contains definition of coprime integers
;; and theorems about them.

(defnd coprime (x y)
  (and (integerp x)
       (integerp y)
       (equal (g-c-d x y) 1)))

(defrule coprime-forward
  (implies (coprime x y)
           (and (integerp x)
                (integerp y)))
  :rule-classes :forward-chaining)

(defruled coprime-commutative
  (equal (coprime x y)
         (coprime y x)))

(defruled coprime-minus-1
  (equal (coprime (- x) y)
         (coprime (fix x) y)))

(defruled coprime-minus-2
  (equal (coprime x (- y))
         (coprime x (fix y))))

(defrule coprime-self
  (equal (coprime x x)
         (or (equal x 1) (equal x -1))))

(defruled coprime-0
  (and (equal (coprime 0 y)
              (or (equal y 1) (equal y -1)))
       (equal (coprime x 0)
              (or (equal x 1) (equal x -1)))))

(defruled coprime-1
  (and (equal (coprime 1 y)
              (integerp y))
       (equal (coprime x 1)
              (integerp x))
       (equal (coprime -1 y)
              (integerp y))
       (equal (coprime x -1)
              (integerp x))))

(defrule coprime-when-extended-euclid
  (implies (and (equal (+ (* r x) (* s y)) 1)
                (integerp x)
                (integerp y)
                (integerp r)
                (integerp s))
           (coprime x y))
  :rule-classes ())

(defrule coprime-when-inverse
  (implies (and (equal (mod (* x x^-1) n)
                       (mod 1 n))
                (integerp n)
                (integerp x)
                (integerp x^-1))
           (coprime x n))
  :rule-classes ())

(defruled coprime-product
  (implies (and (coprime x1 y)
                (coprime x2 y))
           (coprime (* x1 x2) y)))

(defruled coprime-expt
  (implies (and (coprime x y)
                (natp n))
           (coprime (expt x n) y)))

;----------------

(defrule cancelation-when-coprime
  (implies (and (coprime x n)
                (integerp z)
                (divides n (* x z)))
           (divides n z))
  :rule-classes ())

(defruled divides-by-product-of-coprimes
  (implies (and (coprime x y)
                (acl2-numberp z)
                (divides x z)
                (divides y z))
           (divides (* x y) z)))

(defruled extended-euclid-mod
  (implies (and (integerp x)
                (integerp y))
           (and (equal (mod (* x (r x y)) y)
                       (mod (g-c-d x y) y))
                (equal (mod (* y (s x y)) x)
                       (mod (g-c-d x y) x)))))

(defruled extended-euclid-coprime-mod
  (implies (coprime x y)
           (and (equal (mod (* x (r x y)) y)
                       (mod 1 y))
                (equal (mod (* y (s x y)) x)
                       (mod 1 x)))))

; mod-inverse

(defnd mod-inverse (x n)
  (and (coprime x n)
       (mbe :logic (mod (r x n) n)
            :exec (if (= n 0) x (mod (r x n) n)))))

(defrule mod-inverse-forward
  (implies (mod-inverse x n)
           (and (integerp x)
                (integerp n)))
  :rule-classes :forward-chaining)

(defrule mod-inverse-type-when-coprime
  (implies (coprime x y)
           (integerp (mod-inverse x y)))
  :rule-classes :type-prescription)

(defruled mod-inverse-n=0
  (equal (mod-inverse x 0)
         (case x
           (1 1)
           (-1 -1))))

(defruled mod-inverse-abs-n=1
  (and (equal (mod-inverse x 1)
              (and (integerp x) 0))
       (equal (mod-inverse x -1)
              (and (integerp x) 0))))

(defrule mod-inverse-bound-n>0
  (implies (and (mod-inverse x n)
                (> n 0))
           (and (<= 0 (mod-inverse x n))
                (< (mod-inverse x n) n)))
  :rule-classes :linear)

(defrule mod-inverse-when-coprime
  (implies (coprime x n)
           (equal (mod (* x (mod-inverse x n)) n)
                  (mod 1 n))))

(defrule mod-inverse-unique
  (implies (and (coprime x n)
                (equal (mod (* x x^-1) n)
                       (mod 1 n))
                (integerp x^-1))
           (equal (mod x^-1 n) (mod-inverse x n)))
  :rule-classes ())

(defruled mod-inverse-product
  (implies (and (coprime x y1)
                (coprime x y2))
           (and (equal (mod (mod-inverse x (* y1 y2)) y1)
                       (mod-inverse x y1))
                (equal (mod (mod-inverse x (* y1 y2)) y2)
                       (mod-inverse x y2)))))

; binary chinese remainder theorem

(defnd binary-chinese-remainder-witness (a1 n1 a2 n2)
  (declare (xargs :guard (and (coprime n1 n2)
                              (integerp a1)
                              (integerp a2))))
  (+ (* a1 n2 (mod-inverse n2 n1))
     (* a2 n1 (mod-inverse n1 n2))))

(defrule binary-chinese-remainder-witness-type
  (implies (and (coprime n1 n2)
                (integerp a1)
                (integerp a2))
           (integerp (binary-chinese-remainder-witness a1 n1 a2 n2))))

(defrule binary-chinese-remainder-existence
  (implies (and (coprime n1 n2)
                (integerp a1)
                (integerp a2))
           (and (equal (mod (binary-chinese-remainder-witness a1 n1 a2 n2) n1)
                       (mod a1 n1))
                (equal (mod (binary-chinese-remainder-witness a1 n1 a2 n2) n2)
                       (mod a2 n2)))))

(defrule binary-chinese-remainder-uniqueness
  (implies (and (coprime n1 n2)
                (equal (mod x n1) (mod y n1))
                (equal (mod x n2) (mod y n2))
                (integerp x)
                (integerp y))
           (or (= x y) (divides (* n1 n2) (- x y))))
  :rule-classes ())
