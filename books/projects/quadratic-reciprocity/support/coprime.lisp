(in-package "RTL")

;; This book contains definition of coprime integers
;; and theorems about them.

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (acl2::set-minimal-arithmetic-5-theory))

(include-book "std/util/defrule" :dir :system)
(include-book "euclid")
(local (include-book "rtl/rel11/support/basic" :dir :system))

;-------------------

(local
 (defrule mod-1-n>1
   (implies (and (integerp n)
                 (> n 1))
            (equal (mod 1 n) 1))))

(defnd coprime (x y)
  (and (integerp x)
       (integerp y)
       (equal (g-c-d x y) 1)))

(defrule coprime-forward
  (implies (coprime x y)
           (and (integerp x)
                (integerp y)))
  :enable coprime
  :rule-classes :forward-chaining)

(local
 (defruled g-c-d-nat-commutative
   (implies (and (natp x)
                 (natp y))
            (equal (g-c-d-nat x y)
                   (g-c-d-nat y x)))))

(defruled coprime-commutative
  (equal (coprime x y)
         (coprime y x))
  :enable (coprime g-c-d g-c-d-nat-commutative))

(defruled coprime-minus-1
  (equal (coprime (- x) y)
         (coprime (fix x) y))
  :enable (coprime g-c-d))

(defruled coprime-minus-2
  (equal (coprime x (- y))
         (coprime x (fix y)))
  :enable (coprime g-c-d))

(acl2::with-arith5-help
 (defrule coprime-self
   (equal (coprime x x)
          (or (equal x 1) (equal x -1)))
   :enable (coprime g-c-d)))

(defruled coprime-0
  (and (equal (coprime 0 y)
              (or (equal y 1) (equal y -1)))
       (equal (coprime x 0)
              (or (equal x 1) (equal x -1))))
  :enable (coprime g-c-d))

(defruled coprime-1
  (and (equal (coprime 1 y)
              (integerp y))
       (equal (coprime x 1)
              (integerp x))
       (equal (coprime -1 y)
              (integerp y))
       (equal (coprime x -1)
              (integerp x)))
  :prep-lemmas (
    (defrule lemma1
      (implies (natp y)
               (equal (g-c-d-nat 1 y) 1))
      :induct (sub1-induction y))
    (defrule lemma2
      (implies (natp x)
               (equal (g-c-d-nat x 1) 1))
      :enable g-c-d-nat-commutative))
  :enable (coprime g-c-d))

(defrule coprime-when-extended-euclid
  (implies (and (equal (+ (* r x) (* s y)) 1)
                (integerp x)
                (integerp y)
                (integerp r)
                (integerp s))
           (coprime x y))
  :prep-lemmas (
    (defrule lemma
      (implies (and (posp n)
                    (integerp (/ n)))
               (equal n 1))
      :rule-classes ()))
  :enable coprime
  :cases ((divides (g-c-d x y) (+ (* r x) (* s y))))
  :hints (
    ("subgoal 2" :use (
      (:instance divides-sum
        (x (g-c-d x y))
        (y (* r x))
        (z (* s y)))
      (:instance divides-product
        (x (g-c-d x y))
        (y x)
        (z r))
      (:instance divides-product
        (x (g-c-d x y))
        (y y)
        (z s))
      g-c-d-divides))
    ("subgoal 1" :in-theory (enable divides)
                 :use (g-c-d-pos
                       (:instance lemma
                         (n (g-c-d x y))))))
  :rule-classes ())

(defrule coprime-when-inverse
  (implies (and (equal (mod (* x x^-1) n)
                       (mod 1 n))
                (integerp n)
                (integerp x)
                (integerp x^-1))
           (coprime x n))
  :enable divides
  :use (
   (:instance coprime-when-extended-euclid
     (r x^-1)
     (y n)
     (s (/ (- 1 (* x x^-1)) n)))
   (:instance mod-equal-int
              (a 1)
              (b (* x x^-1))))
  :rule-classes ())

(acl2::with-arith5-help
 (defruled coprime-product
   (implies (and (coprime x1 y)
                 (coprime x2 y))
            (coprime (* x1 x2) y))
   :prep-lemmas (
     (defrule lemma1
       (implies (and (coprime x1 y)
                     (integerp x2))
                (equal (* x1 x2 (r x1 y) (r x2 y))
                       (- (* x2 (r x2 y))
                          (* x2 y (r x2 y) (s x1 y)))))
       :enable coprime
       :use (:instance g-c-d-linear-combination (x x1)))
     (defrule lemma2
       (implies (coprime x2 y)
                (equal (+ (* x2 (r x2 y)) (* y (s x2 y))) 1))
       :enable coprime
       :use (:instance g-c-d-linear-combination (x x2))))
   :use ((:instance coprime-when-extended-euclid
           (x (* x1 x2))
           (y y)
           (r (* (r x1 y) (r x2 y)))
           (s (+ (* x2 (r x2 y) (s x1 y)) (s x2 y)))))))

(defruled coprime-expt
  (implies (and (coprime x y)
                (natp n))
           (coprime (expt x n) y))
  :enable coprime-1
  :induct (sub1-induction n)
  :hints (("subgoal *1/2" :expand (expt x n)
           :use (:instance coprime-product
                           (x1 (expt x (1- n)))
                           (x2 x)))))

;----------------

(defrule cancelation-when-coprime
  (implies (and (coprime x n)
                (integerp z)
                (divides n (* x z)))
           (divides n z))
  :prep-lemmas (
    (acl2::with-arith5-help
     (defrule lemma1
       (implies (and (divides n (* x z))
                     (integerp x)
                     (integerp n)
                     (integerp z))
                (divides n (+ (* x z (r x n))
                              (* n z (s x n)))))
       :enable divides
       :rule-classes ()))
    (acl2::with-arith5-help
     (defrule lemma2
       (implies (and (coprime x y)
                     (integerp z))
                (equal (+ (* y z (s x y)) (* x z (r x y)))
                       z))
       :enable coprime
       :use g-c-d-linear-combination)))
  :use lemma1
  :rule-classes ())

(defruled divides-by-product-of-coprimes
  (implies (and (coprime x y)
                (acl2-numberp z)
                (divides x z)
                (divides y z))
           (divides (* x y) z))
  :prep-lemmas (
    (defruled lemma1
      (implies (and (integerp (* x z))
                    (integerp r))
               (integerp (* x z r))))
    (acl2::with-arith5-help
     (defrule lemma2
       (implies (and (divides x z)
                     (divides y z)
                     (integerp x)
                     (integerp y))
                (divides (* x y) (+ (* x z (r x y))
                                    (* y z (s x y)))))
       :enable (divides lemma1)
       :rule-classes ()))
    (acl2::with-arith5-help
     (defrule lemma3
       (implies (and (coprime x y)
                     (acl2-numberp z))
                (equal (+ (* x z (r x y)) (* y z (s x y)))
                       z))
       :enable coprime
       :use g-c-d-linear-combination)))
  :use lemma2)

(defruled extended-euclid-mod
  (implies (and (integerp x)
                (integerp y))
           (and (equal (mod (* x (r x y)) y)
                       (mod (g-c-d x y) y))
                (equal (mod (* y (s x y)) x)
                       (mod (g-c-d x y) x))))
  :prep-lemmas (
    (defrule lemma1
      (implies (and (integerp x)
                    (integerp y))
               (equal (g-c-d x y)
                      (+ (* x (r x y)) (* y (s x y)))))
      :use g-c-d-linear-combination)
    (defrule lemma2
      (implies (and (acl2-numberp x)
                    (not (= x 0))
                    (integerp y))
               (divides x (* x y)))
      :enable divides)
    (acl2::with-arith5-help
     (defrule lemma3
       (implies (and (integerp x)
                     (integerp y)
                     (not (= y 0)))
                (equal (mod (* x (r x y)) y)
                       (mod (g-c-d x y) y)))
       :use (:instance divides-mod-equal
              (a (g-c-d x y))
              (b (* x (r x y)))
              (n y))))
    (acl2::with-arith5-help
     (defrule lemma4
       (implies (and (integerp x)
                     (integerp y)
                     (not (= x 0)))
                (equal (mod (* y (s x y)) x)
                       (mod (g-c-d x y) x)))
       :use (:instance divides-mod-equal
              (a (g-c-d x y))
              (b (* y (s x y)))
              (n x)))))
  :cases ((= x 0) (= y 0)))

(defruled extended-euclid-coprime-mod
  (implies (coprime x y)
           (and (equal (mod (* x (r x y)) y)
                       (mod 1 y))
                (equal (mod (* y (s x y)) x)
                       (mod 1 x))))
  :enable (coprime extended-euclid-mod))

(defnd mod-inverse (x n)
  (declare (xargs :guard-hints (("goal" :in-theory (enable coprime-0)))))
  (and (coprime x n)
       (mbe :logic (mod (r x n) n)
            :exec (if (= n 0) x (mod (r x n) n)))))

(defrule mod-inverse-forward
  (implies (mod-inverse x n)
           (and (integerp x)
                (integerp n)))
  :enable mod-inverse
  :rule-classes :forward-chaining)

(defrule mod-inverse-type-when-coprime
  (implies (coprime x y)
           (integerp (mod-inverse x y)))
  :enable mod-inverse
  :rule-classes :type-prescription)

(defruled mod-inverse-n=0
  (equal (mod-inverse x 0)
         (case x
           (1 1)
           (-1 -1)))
  :enable mod-inverse
  :use (:instance coprime-0 (y x)))

(defruled mod-inverse-abs-n=1
  (and (equal (mod-inverse x 1)
              (and (integerp x) 0))
       (equal (mod-inverse x -1)
              (and (integerp x) 0)))
  :enable (mod-inverse coprime-1))

(defrule mod-inverse-bound-n>0
  (implies (and (mod-inverse x n)
                (> n 0))
           (and (<= 0 (mod-inverse x n))
                (< (mod-inverse x n) n)))
  :enable mod-inverse
  :rule-classes :linear)

(defrule mod-inverse-when-coprime
  (implies (coprime x n)
           (equal (mod (* x (mod-inverse x n)) n)
                  (mod 1 n)))
  :prep-lemmas (
    (defrule lemma
      (implies (and (coprime x n))
               (equal (mod-inverse x n)
                      (- (r x n)
                         (* n (fl (/ (r x n) n))))))
      :enable mod-inverse
      :use  (:instance mod-def
                       (x (r x n))
                       (y n)))
    (defrule lemma2
      (implies (and (acl2-numberp x)
                    (not (= x 0))
                    (integerp y))
               (divides x (* x y)))
      :enable divides)
    (acl2::with-arith5-help
     (defrule lemma3
       (equal (- (* x r) (* x (- r z))) (* x z)))))
  :enable (coprime-0 extended-euclid-coprime-mod)
  :cases ((= x 0) (= n 0))
  :use ((:instance divides-mod-equal
                  (a (* x (r x n)))
                  (b (* x (mod-inverse x n))))))

(acl2::with-arith5-help
 (defrule mod-inverse-unique
   (implies (and (coprime x n)
                 (equal (mod (* x x^-1) n)
                        (mod 1 n))
                 (integerp x^-1))
            (equal (mod x^-1 n) (mod-inverse x n)))
   :enable (coprime-0 mod-inverse extended-euclid-coprime-mod)
   :use (
     (:instance divides-mod-equal
       (a x^-1)
       (b (r x n)))
     (:instance cancelation-when-coprime
       (z (- x^-1 (r x n))))
     (:instance divides-mod-equal
       (a (* x x^-1))
       (b (* x (r x n)))))
   :rule-classes ()))

(defruled mod-inverse-product
  (implies (and (coprime x y1)
                (coprime x y2))
           (and (equal (mod (mod-inverse x (* y1 y2)) y1)
                       (mod-inverse x y1))
                (equal (mod (mod-inverse x (* y1 y2)) y2)
                       (mod-inverse x y2))))
  :prep-lemmas (
    (defrule lemma1
      (implies (and (integerp x)
                    (integerp y))
               (integerp (* x y)))
      :rule-classes ())
    (defrule lemma2
      (implies (and (integerp (* (/ y1) (/ y2) x))
                    (acl2-numberp x)
                    (acl2-numberp y1)
                    (not (= y1 0))
                    (integerp y2)
                    (not (= y2 0)))
               (divides y1 x))
      :enable divides
      :use (:instance lemma1
             (x (* (/ y1) (/ y2) x))
             (y y2))
      :rule-classes ())
    (defrule lemma3
      (implies (and (coprime x (* y1 y2))
                    (integerp y1)
                    (integerp y2))
               (equal (mod (* x (mod-inverse x (* y1 y2))) y1)
                      (mod 1 y1)))
      :enable coprime-0
      :cases ((= y1 0) (= y2 0))
      :hints (("subgoal 3"
      :use ((:instance lemma2
              (x (+ -1 (* x (mod-inverse x (* y1 y2))))))
            (:instance divides-mod-equal
              (a (* x (mod-inverse x (* y1 y2))))
              (b 1)
              (n y1))
            (:instance mod-equal-int
              (a (* x (mod-inverse x (* y1 y2))))
              (b 1)
              (n (* y1 y2)))
            (:instance mod-inverse-when-coprime
              (n (* y1 y2))))))))
  :cases ((coprime x (* y1 y2)))
  :hints (
    ("subgoal 2" :cases ((coprime (* y1 y2) x)))
    ("subgoal 2.2" :in-theory (enable coprime-product coprime-commutative))
    ("subgoal 2.1" :in-theory (enable coprime-commutative))
    ("subgoal 1" :use ((:instance mod-inverse-unique
                        (x^-1 (mod-inverse x (* y1 y2)))
                        (n y1))
                       (:instance mod-inverse-unique
                        (x^-1 (mod-inverse x (* y1 y2)))
                        (n y2))
                       (:instance lemma3
                         (y1 y2)
                         (y2 y1))))))

; binary chinese remainder theorem

(defnd binary-chinese-remainder-witness (a1 n1 a2 n2)
  (declare (xargs :guard (and (coprime n1 n2)
                              (integerp a1)
                              (integerp a2))
                  :guard-hints (("goal" :cases ((coprime n2 n1))
                                        :in-theory (enable coprime-commutative)))))
  (+ (* a1 n2 (mod-inverse n2 n1))
     (* a2 n1 (mod-inverse n1 n2))))

(defrule binary-chinese-remainder-witness-type
  (implies (and (coprime n1 n2)
                (integerp a1)
                (integerp a2))
           (integerp (binary-chinese-remainder-witness a1 n1 a2 n2)))
  :enable (binary-chinese-remainder-witness)
  :cases ((coprime n2 n1))
  :hints (("subgoal 2" :in-theory (enable coprime-commutative))))

(acl2::with-arith5-help
 (defrule binary-chinese-remainder-existence
   (implies (and (coprime n1 n2)
                 (integerp a1)
                 (integerp a2))
            (and (equal (mod (binary-chinese-remainder-witness a1 n1 a2 n2) n1)
                        (mod a1 n1))
                 (equal (mod (binary-chinese-remainder-witness a1 n1 a2 n2) n2)
                        (mod a2 n2))))
   :prep-lemmas (
     (defrule lemma1
       (implies (and (coprime n2 n1)
                     (not (= n1 0))
                     (not (= n2 0))
                     (integerp a1))
                (equal (mod (* a1 n2 (mod-inverse n2 n1)) n1)
                       (mod a1 n1)))
       :use ((:instance divides-mod-equal
               (a (* a1 n2 (mod-inverse n2 n1)))
               (b a1)
               (n n1))
             (:instance divides-product
               (x n1)
               (y (1- (* n2 (mod-inverse n2 n1))))
               (z a1))
             (:instance divides-mod-equal
               (a (* n2 (mod-inverse n2 n1)))
               (b 1)
               (n n1)))))
   :enable (binary-chinese-remainder-witness coprime-0)
   :cases ((= n1 0) (= n2 0))
   :hints (
     ("subgoal 3" :cases ((coprime n2 n1)))
     ("subgoal 3.2" :in-theory (enable coprime-commutative)))))

(defrule binary-chinese-remainder-uniqueness
  (implies (and (coprime n1 n2)
                (equal (mod x n1) (mod y n1))
                (equal (mod x n2) (mod y n2))
                (integerp x)
                (integerp y))
           (or (= x y) (divides (* n1 n2) (- x y))))
  :enable divides-by-product-of-coprimes
  :use ((:instance divides-mod-equal
          (a x)
          (b y)
          (n n1))
        (:instance divides-mod-equal
          (a x)
          (b y)
          (n n2)))
  :rule-classes ())
