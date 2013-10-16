(in-package "ACL2")

;;; See also comments on analogous proof in
;;; riemann-rcfn-lower-bound.lisp.

(deflabel start-riemann-rcfn-upper-bound)

(local (include-book "top-with-meta"))

(deflabel start-riemann-rcfn-upper-bound-2)

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

#|
 (:GENERALIZE ((SUMLIST (MAP-TIMES (DELTAS (CDDR P))
                                   (CDR (MAP-RCFN (CDDR P)))))
               A)
              ((CAR (MAP-RCFN (CDDR P))) B)
              ((RCFN (MAX-X-REC (CDDR P))) C)
              ((RCFN (CADR P)) D)
              ((RCFN (CAR P)) E))
 (:GENERALIZE ((CAR (LAST (CDDR P))) F)
              ((CADDR P) G)
              ((CADR P) H)
              ((CAR P) I))
|#

(defthm arith-lemma-2-a
  (implies (and (< c d)
                (< i h)
                (< h g)
                (< d e)
                (< i f)
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp g))
                (force (realp h))
                (force (realp i)))
           (<= (+ (- (* i d))
                  (* h d)
                  (- (* h d))
                  (* d f))
               (+ (- (* i e)) (* e f))))
  :rule-classes nil)

(defthm arith-lemma-2
  (implies (and (< c d)
                (<= (+ (- (* h b)) (* g b) a)
                    (+ (- (* h d)) (* d f)))
                (< i h)
                (< h g)
                (< d e)
                (< i f)
                (force (realp a))
                (force (realp b))
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp g))
                (force (realp h))
                (force (realp i)))
           (<= (+ (- (* i d))
                  (* h d)
                  (- (* h b))
                  (* g b)
                  a)
               (+ (- (* i e)) (* e f))))
  :hints (("Goal" :use arith-lemma-2-a
           :in-theory (current-theory 'start-riemann-rcfn-upper-bound))))

; Derivation of 3-a-a from 3-a:
#|
 (+ (* i d)
    (- (* h d))
    (* h c)
    (- (* f c))
    (- (* i e))
    (* e f))
=
 (+ (* (- i h) d)
    (* (- h f) c)
    (- (* (- i f) e)))
=
 (+ (* (- i h) d)
    (* (- h i) c)
    (* (- i f) c)
    (- (* (- i f) e)))
=
 (+ (* (- i h) (- d c))
    (* (- i f) (- c e)))
|#

(defthm arith-lemma-3-a-a-a
  (implies (and (<= dc 0)
                (<= ih 0)
                (<= if 0)
                (<= ce 0)
                (realp dc)
                (realp ih)
                (realp if)
                (realp ce))
           (<= 0
               (+ (* ih dc)
                  (* if ce))))
  :rule-classes nil)

(defthm arith-lemma-3-a-a
  (implies (and (<= d c)
                (< i h)
                (< c e)
                (< i f)
                (realp c)
                (realp d)
                (realp e)
                (realp f)
                (realp h)
                (realp i))
           (<= 0
               (+ (* (- i h) (- d c))
                  (* (- i f) (- c e)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (set-difference-theories
            (current-theory
             'start-riemann-rcfn-upper-bound)
            '(distributivity
              commutativity-of-*
              commutativity-of-+))
           :use
           ((:instance
             arith-lemma-3-a-a-a
             (ih (- i h))
             (dc (- d c))
             (if (- i f))
             (ce (- c e)))))))

(defthm arith-lemma-3-a
  (implies (and (<= d c)
                (< i h)
                (< c e)
                (< i f)
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp h))
                (force (realp i)))
           (<= 0
               (+ (* i d)
                  (- (* h d))
                  (* h c)
                  (- (* f c))
                  (- (* i e))
                  (* e f))))
  :hints (("Goal" :use arith-lemma-3-a-a
           :in-theory (current-theory
                       'start-riemann-rcfn-upper-bound-2)))
  :rule-classes nil)

(defthm arith-lemma-3
  (implies (and (<= d c)
                (<= (+ (- (* h b)) (* g b) a)
                    (+ (- (* h c)) (* f c)))
                (< i h)
                (< h g)
                (< c e)
                (< i f)
                (force (realp a))
                (force (realp b))
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp g))
                (force (realp h))
                (force (realp i)))
           (<= (+ (- (* i d))
                  (* h d)
                  (- (* h b))
                  (* g b)
                  a)
               (+ (- (* i e)) (* e f))))
  :hints (("Goal" :use arith-lemma-3-a
           :in-theory (current-theory 'start-riemann-rcfn-upper-bound))))

; Derivation of 4-a-a from 4-a:
#|
 (<= 0
     (+ (* i d)
        (- (* h d))
        (* h c)
        (- (* f c))
        (- (* i c))
        (* f c)))
=
 (+ (* (- i h) d)
    (* (- h f) c)
    (- (* (- i f) c)))
=
 (+ (* (- i h) d)
    (* (- h f) c)
    (* (- f i) c))
=
 (+ (* (- i h) d)
    (* (- h i) c)
=
 (* (- i h) (- d c))
|#

(defthm arith-lemma-4-a-a
  (implies (and (<= d c)
                (< i h)
                (< i f)
                (force (realp c))
                (force (realp d))
                (force (realp f))
                (force (realp h))
                (force (realp i)))
           (<= 0
               (* (- i h)
                  (- d c))))
  :rule-classes nil)

(defthm arith-lemma-4-a
  (implies (and (<= d c)
                (< i h)
                (< i f)
                (force (realp c))
                (force (realp d))
                (force (realp f))
                (force (realp h))
                (force (realp i)))
           (<= 0
               (+ (* i d)
                  (- (* h d))
                  (* h c)
                  (- (* f c))
                  (- (* i c))
                  (* f c))))
  :rule-classes nil
  :hints (("Goal" :use arith-lemma-4-a-a
           :in-theory (current-theory 'start-riemann-rcfn-upper-bound-2))))

(defthm arith-lemma-4
  (implies (and (<= d c)
                (<= (+ (- (* h b)) (* g b) a)
                    (+ (- (* h c)) (* f c)))
                (< i h)
                (< h g)
                (<= e c)
                (< i f)
                (force (realp a))
                (force (realp b))
                (force (realp c))
                (force (realp d))
                (force (realp e))
                (force (realp f))
                (force (realp g))
                (force (realp h))
                (force (realp i)))
           (<= (+ (- (* i d))
                  (* h d)
                  (- (* h b))
                  (* g b)
                  a)
               (+ (- (* i c)) (* f c))))
  :hints (("Goal" :use arith-lemma-4-a
           :in-theory (current-theory 'start-riemann-rcfn-upper-bound))))
))

;; Set up theory so that we can prove the results that follow without
;; concern for how we proved the arithmetic lemmas above.

(local
 (in-theory (union-theories
             '(arith-lemma-1 arith-lemma-2 arith-lemma-3 arith-lemma-4)
             (current-theory 'start-riemann-rcfn-upper-bound-2))))

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

(defthm riemann-rcfn-upper-bound
  (implies (partitionp p)
           (let ((a (car p))
                 (b (car (last p))))
             (<= (riemann-rcfn p)
                 (* (rcfn (max-x-rec p))
                    (- b a)))))
  :rule-classes nil)
