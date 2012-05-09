(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "make-partition")
(include-book "nsa-lemmas")
(include-book "max-and-min-attained")

(encapsulate
 ()
 (local (include-book "riemann-rcfn-between"))

 (defthm riemann-rcfn-between
  (implies (and (realp a)
                (realp b)
                (< a b))
           (let ((p (make-partition a b (i-large-integer))))
             (between (riemann-rcfn p)
                      (* (rcfn (min-x-rec p))
                         (- b a))
                      (* (rcfn (max-x-rec p))
                         (- b a)))))
   :rule-classes nil))

(in-theory (disable between))

(include-book "min-max-x-rec-lemmas")

(encapsulate
 ()
 (local (include-book "riemann-lemmas"))

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
 )

(defthm riemann-rcfn-is-limited
  (implies (and (standard-numberp a) (realp a)
                (standard-numberp b) (realp b)
                (< a b))
           (i-limited (riemann-rcfn
                       (make-partition a b (i-large-integer)))))
  :hints (("Goal"
           :in-theory
           (disable riemann-rcfn make-partition abs
                    between-limited-implies-limited
                    ;; The following lemmas show up during the proof
                    ;; attempt, but we don't want them interfering
                    ;; with the structure that we've set up.
                    distributivity
                    functional-commutativity-of-minus-*-right
                    commutativity-of-*
                    commutativity-of-+)
           :use
           (riemann-rcfn-between
            (:instance
             between-limited-implies-limited
             (z (riemann-rcfn
                 (make-partition a b (i-large-integer))))
             (x (* (rcfn (min-x-rec
                          (make-partition a b (i-large-integer))))
                   (- b a)))
             (y (* (rcfn (max-x-rec
                          (make-partition a b (i-large-integer))))
                   (- b a))))))))

(defthm standard-part-riemann-rcfn-is-standard
  (implies (and (standard-numberp a) (realp a)
                (standard-numberp b) (realp b)
                (< a b))
           (standard-numberp
            (standard-part (riemann-rcfn
                            (make-partition a b (i-large-integer))))))
  :hints (("Goal" :in-theory (disable riemann-rcfn make-partition))))
