(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "make-partition")
(include-book "nsa-lemmas")
(include-book "max-and-min-attained")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(encapsulate
 ()
 (local (include-book "i-limited-rcfn"))

 (defthm i-limited-rcfn
   (implies (and (realp x)
                 (i-limited x))
            (i-limited (rcfn x)))))

(defthm riemann-rcfn-is-limited-lemma-1
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b)
                (< a b))
           (i-limited (* (rcfn (min-x-rec
                                (make-partition a b (i-large-integer))))
                         (- b a)))))

(defthm riemann-rcfn-is-limited-lemma-2
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b)
                (< a b))
           (i-limited (* (rcfn (max-x-rec
                                (make-partition a b (i-large-integer))))
                         (- b a)))))

(defthm riemann-rcfn-is-limited-lemma-3
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b)
                (< a b))
           (realp (* (rcfn (min-x-rec
                            (make-partition a b (i-large-integer))))
                     (- b a)))))

(defthm riemann-rcfn-is-limited-lemma-4
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b)
                (< a b))
           (realp (* (rcfn (max-x-rec
                            (make-partition a b (i-large-integer))))
                     (- b a)))))
