(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "make-partition")
(include-book "riemann-lemmas")
(include-book "integral-rcfn-lemmas")
(include-book "nsa-lemmas")
(include-book "max-and-min-attained")
(include-book "riemann-rcfn-between")
(include-book "integral-rcfn")
(include-book "between-limited-implies-limited")
(include-book "defaxioms")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(encapsulate
 ()

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

(defthm riemann-rcfn-between-rewrite
   (implies (and (realp a)
                 (realp b)
                 (< a b))
            (let ((p (make-partition a b (i-large-integer))))
              (between (riemann-rcfn p)
                       (* (+ (- a) b)
                          (rcfn (min-x-rec p)))
                       (* (+ (- a) b)
                          (rcfn (max-x-rec p))))))
   :hints (("Goal" :use riemann-rcfn-between)))

(defthm between-quotient
  (implies (and (realp num)
                (realp den)
                (< 0 den)
                (realp x)
                (realp y))
           (equal (between (* (/ den) num) x y)
                  (between num (* x den) (* y den)))))

(in-theory (disable riemann-rcfn between))

(encapsulate
 ()
 (local (include-book "standard-part-preserves-between"))

 (defthm standard-part-preserves-between
   (implies (and (realp x)
                 (realp y)
                 (realp z)
                 (between z x y))
            (between (standard-part z)
                     (standard-part x)
                     (standard-part y)))
   :rule-classes nil
   :hints (("Goal"
            :cases
            ((<= (standard-part x)
                 (standard-part z)))))))

(defthm standard-part-preserves-between-rewrite
   (implies (and (realp x)
                 (realp y)
                 (realp z)
                 (between z x y))
            (between (standard-part z)
                     (standard-part x)
                     (standard-part y)))
   :hints (("Goal" :by standard-part-preserves-between)))

(encapsulate
 ()
 (local (include-book "rcfn-standard-part"))

 (defthm rcfn-standard-part
   (implies (and (i-limited x)
                 (realp x))
            (equal (rcfn (standard-part x))
                   (standard-part (rcfn x))))))

(local
 (defthm hack
   (implies (and (standard-numberp s)
                 (i-limited x))
            (equal (* s (standard-part x))
                   (standard-part (* s x))))))

(encapsulate
 ()
 (local (include-book "i-limited-rcfn"))

 (defthm i-limited-rcfn
   (implies (and (realp x)
                 (i-limited x))
            (i-limited (rcfn x)))))

(defthm realp-standard-part-rewrite
  (implies (realp x)
           (realp (standard-part x))))

(defthm integral-rcfn-quotient-between-non-classical
   (implies (and (standard-numberp a) (realp a)
                 (standard-numberp b) (realp b)
                 (< a b))
            (between
             (/ (integral-rcfn a b)
                (- b a))
             (rcfn (min-x a b))
             (rcfn (max-x a b))))
   :hints (("Goal"
            :in-theory
            (disable distributivity
                     distributivity-commuted
                     ;; The following must be disabled in order to
                     ;; avoid looping with hack above.  This problem
                     ;; was discovered by using :brr t and then (in
                     ;; raw Lisp) the form (cw-gstack *deep-gstack*
                     ;; state) after a stack overflow.
                     standard-part-of-times))))
