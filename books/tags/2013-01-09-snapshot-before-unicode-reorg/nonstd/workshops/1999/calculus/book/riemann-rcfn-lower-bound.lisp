(in-package "ACL2")

;;; See also comments on analogous proof in
;;; riemann-rcfn-lower-bound.lisp, which was done second (and hence
;;; may be a bit cleaner, though they follow each other closely).

(deflabel start-riemann-rcfn-lower-bound)

(local (include-book "top-with-meta"))

(deflabel start-riemann-rcfn-lower-bound-2)

;;; The main work is in proving the four arithmetic lemmas that we
;;; need:  arith-lemma-1, arith-lemma-2, arith-lemma-3, and
;;; arith-lemma-4.  A main tool is to use distributivity in reverse.
;;; The following eight lemmas might not all be necessary, but some
;;; are.

(local
(encapsulate
 ()

(defthm distributivity-in-reverse-1
  (equal (+ (- (* c a))
            (* d a))
         (* (+ (- c) d) a)))

(defthm distributivity-in-reverse-2
  (equal (+ (* c a)
            (* d a))
         (* (+ c d) a)))

(defthm distributivity-in-reverse-3
  (equal (+ (* c a)
            (- (* d a)))
         (* (+ c (- d)) a)))

(defthm distributivity-in-reverse-4
  (equal (+ (- (* c a))
            (- (* d a)))
         (* (+ (- c) (- d)) a)))

(defthm distributivity-in-reverse-5
  (equal (+ (- (* a c))
            (* a d))
         (* a (+ (- c) d))))

(defthm distributivity-in-reverse-6
  (equal (+ (* a c)
            (* a d))
         (* a (+ c d))))

(defthm distributivity-in-reverse-7
  (equal (+ (* a c)
            (- (* a d)))
         (* a (+ c (- d)))))

(defthm distributivity-in-reverse-8
  (equal (+ (- (* a c))
            (- (* a d)))
         (* a (+ (- c) (- d)))))

(in-theory (disable distributivity))

(defthm arith-lemma-1
  (implies (and (< a b)
                (< c d)
                (realp a)
                (realp b)
                (realp c)
                (realp d))
           (<= (+ (- (* c a))
                  (* d a))
               (+ (- (* c b))
                  (* d b)))))

(defthm arith-lemma-2-a
  (implies (and
            (< h g)
            (< g f)
            (< d c)
            (force (>= e f))
            (force (realp a))
            (force (realp b))
            (force (realp c))
            (force (realp d))
            (force (realp e))
            (force (realp f))
            (force (realp g))
            (force (realp h)))
           (<= (+ (- (* h d))
                  (* d e))
               (+ (- (* h c))
                  (* g c)
                  (- (* g c))
                  (* c e))))
  :rule-classes nil)

(defthm arith-lemma-2
  (implies (and
            (<= (+ (- (* g c))
                   (* c e))
                (+ (- (* g b))
                   (* f b)
                   a))
            (< h g)
            (< g f)
            (< d c)
            (force (>= e f))
            (force (realp a))
            (force (realp b))
            (force (realp c))
            (force (realp d))
            (force (realp e))
            (force (realp f))
            (force (realp g))
            (force (realp h)))
           (<= (+ (- (* h d))
                  (* d e))
               (+ (- (* h c))
                  (* g c)
                  (- (* g b))
                  (* f b)
                  a)))
  :hints (("Goal" :use arith-lemma-2-a
           :in-theory (current-theory 'start-riemann-rcfn-lower-bound))))

(defthm arith-lemma-3-a-a-a
  (implies (and (<= if 0)
                (<= ea 0)
                (>= hi 0)
                (>= da 0)
                (realp if)
                (realp ea)
                (realp hi)
                (realp da))
           (<= 0
               (+ (* if ea) (* hi da))))
  :rule-classes nil)

(defthm arith-lemma-3-a-a
  (implies (and (<= a d)
                (< i h)
                (< h g)
                (< e a)
                (<= g f)
                (realp a)
                (realp d)
                (realp e)
                (realp f)
                (realp g)
                (realp h)
                (realp i))
           (<= 0
               (+ (* (- i f) (- e a)) (* (- h i) (- d a)))))
  :rule-classes nil
  :hints (("Goal"
           :use
           ((:instance
             arith-lemma-3-a-a-a
             (if (- i f))
             (ea (- e a))
             (hi (- h i))
             (da (- d a)))))))

(defthm arith-lemma-3-a
  (implies (and (<= a d)
                (< i h)
                (< h g)
                (< e a)
                (<= g f)
                (realp a)
                (realp d)
                (realp e)
                (realp f)
                (realp g)
                (realp h)
                (realp i))
           (<= 0
               (+ (* i e)
                  (- (* e f))
                  (- (* i d))
                  (* h d)
                  (- (* h a))
                  (* f a))))
  :rule-classes nil
  :hints (("Goal" :use arith-lemma-3-a-a
           :in-theory (current-theory 'start-riemann-rcfn-lower-bound-2))))

#| Proof sketch for arith-lemma-3:

We have:
e <= a <= d
i <= h <= g <= f

Suffices to prove:

            (<= 0
                (+ (* i e)
                   (- (* e f))
                   (- (* i d))
                   (* h d)
                   (- (* h a))
                   (* f a)))
(* e (- i f))
(* d (- h i))
(* a (- f h)) = (* a (+ (- f i) (- i h)))
--> (+ (* (- i f) (- e a)) (* (- h i) (- d a)))

|#

(defthm arith-lemma-3
  (implies (and (<= a d)
                (<= (+ (- (* h a))
                       (* f a))
                    (+ (- (* h c))
                       (* g c)
                       b))
                (< i h)
                (< h g)
                (< e a)
                (force (<= g f))
                (force (realp a))
                (force (realp b))
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp g))
                (force (realp h))
                (force (realp i)))
           (<= (+ (- (* i e))
                  (* e f))
               (+ (- (* i d))
                  (* h d)
                  (- (* h c))
                  (* g c)
                  b)))
  :hints (("Goal" :use arith-lemma-3-a
           :in-theory (current-theory 'start-riemann-rcfn-lower-bound))))

(defthm arith-lemma-4-a-a
  (implies (and (<= a d)
                (< h g)
                (< g f)
                (<= f e)
                (realp a)
                (realp d)
                (realp e)
                (realp f)
                (realp g)
                (realp h))
           (<= (- (* a (+ e (- h)))
                  (* a (+ e (- g))))
               (+ (* d g)
                  (- (* d h)))))
  :rule-classes nil)

(defthm arith-lemma-4-a
  (implies (and (<= a d)
                (< h g)
                (< g f)
                (<= f e)
                (realp a)
                (realp d)
                (realp e)
                (realp f)
                (realp g)
                (realp h))
           (<= (+ (- (* h a))
                  (* e a))
               (+ (- (* h d))
                  (* g d)
                  (- (* g a))
                  (* e a))))
  :rule-classes nil
  :hints (("Goal" :use arith-lemma-4-a-a
           :in-theory (current-theory 'start-riemann-rcfn-lower-bound-2))))

(defthm arith-lemma-4
  (implies (and (<= a d)
                (<= (+ (- (* g a))
                       (* e a))
                    (+ (- (* g c))
                       (* f c)
                       b))
                (< h g)
                (< g f)
                (force (<= f e))
                (force (realp a))
                (force (realp b))
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp g))
                (force (realp h)))
           (<= (+ (- (* h a))
                  (* e a))
               (+ (- (* h d))
                  (* g d)
                  (- (* g c))
                  (* f c)
                  b)))
  :hints (("Goal" :use arith-lemma-4-a
           :in-theory (current-theory
                       'start-riemann-rcfn-lower-bound-2))))
))

;; Set up theory so that we can prove the results that follow without
;; concern for how we proved the arithmetic lemmas above.

(local
 (in-theory (union-theories
             '(arith-lemma-1 arith-lemma-2 arith-lemma-3 arith-lemma-4)
             (current-theory 'start-riemann-rcfn-lower-bound-2))))

(include-book "riemann-defuns")
(include-book "make-partition")
(local (include-book "riemann-lemmas"))
(local (include-book "nsa-lemmas"))

(defthm real-listp-cdr-map-rcfn
  (implies (partitionp p)
           (real-listp (cdr (map-rcfn p)))))

(defthm realp-car-map-rcfn
  (implies (partitionp p)
           (realp (car (map-rcfn p)))))

; For definition of max-x-rec, at the least:
(include-book "max-and-min-attained")

(defthm riemann-rcfn-lower-bound
  (implies (partitionp p)
           (let ((a (car p))
                 (b (car (last p))))
             (>= (riemann-rcfn p)
                 (* (rcfn (min-x-rec p))
                    (- b a)))))
  :rule-classes nil)
