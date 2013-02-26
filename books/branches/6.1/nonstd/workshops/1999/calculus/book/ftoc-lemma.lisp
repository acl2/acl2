(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "make-partition")
(include-book "riemann-lemmas")
(include-book "integral-rcfn-lemmas")
(include-book "nsa-lemmas")
(include-book "max-and-min-attained")
(include-book "integral-rcfn")
(include-book "defaxioms")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(encapsulate
 ()
 (local (include-book "min-x-and-max-x-lemmas"))

 (defthm-std realp-min-x
   (implies (and (realp a)
                 (realp b))
            (realp (min-x a b)))
   :rule-classes (:type-prescription :rewrite))

 (defthm-std realp-max-x
   (implies (and (realp a)
                 (realp b))
            (realp (max-x a b)))
   :rule-classes (:type-prescription :rewrite))

 (defthm i-close-min-x
   (implies (and (realp x)
                 (realp y)
                 (< x y)
                 (i-close x y))
            (i-close (min-x x y) x)))

 (defthm i-close-max-x
   (implies (and (realp x)
                 (realp y)
                 (< x y)
                 (i-close x y))
            (i-close (max-x x y) x)))

 (defthm i-close-min-x-alt
   (implies (and (realp x)
                 (realp y)
                 (< x y)
                 (i-close x y))
            (i-close (min-x x y) y)))

 (defthm i-close-max-x-alt
   (implies (and (realp x)
                 (realp y)
                 (< x y)
                 (i-close x y))
            (i-close (max-x x y) y)))
 )

(encapsulate
 ()
 (local (include-book "integral-rcfn-quotient-between-non-classical"))

 (defthm integral-rcfn-quotient-between-non-classical
   (implies (and (standard-numberp a) (realp a)
                 (standard-numberp b) (realp b)
                 (< a b))
            (between
             (/ (integral-rcfn a b)
                (- b a))
             (rcfn (min-x a b))
             (rcfn (max-x a b))))))

(defthm-std integral-rcfn-quotient-between
  (implies (and (realp a)
                (realp b)
                (< a b))
           (between
            (/ (integral-rcfn a b)
               (- b a))
            (rcfn (min-x a b))
            (rcfn (max-x a b))))
  :hints (("Goal" :use integral-rcfn-quotient-between-non-classical)))

(encapsulate
 ()
 (local (include-book "between-i-close-implies-i-close"))

 (defthm between-i-close-implies-i-close
   (implies (and (realp z)
                 (realp x)
                 (realp y)
                 (realp r)
                 (between z x y)
                 (i-close x r)
                 (i-close y r))
            (i-close z r))
   :rule-classes nil))

(defthm realp-standard-part-rewrite
  (implies (realp x)
           (realp (standard-part x))))

(defthm-std realp-integral-rcfn
  (implies (and (realp a)
                (realp b))
           (realp (integral-rcfn a b)))
  :hints (("Goal" :in-theory (disable sumlist map-times deltas map-rcfn))))

(defthm rcfn-continuous-commuted
  (implies (and (standard-numberp y) ; as opposed to x
                (realp x)
                (i-close x y)
                (realp y))
           (i-close (rcfn x) (rcfn y)))
  :hints (("Goal" :use ((:instance rcfn-continuous (x y) (y x)))
           :in-theory (set-difference-theories
                       (enable i-close-symmetric)
                       '(rcfn-continuous)))))

(defthm i-close-+-2
  (implies (and (realp x)
                (realp eps)
                (i-small eps))
           (i-close x (+ eps x)))
  :hints (("Goal" :in-theory (enable i-small i-close))))

(defthm ftoc-lemma-as-i-close-case-1
  (implies (and (realp a)
                (realp b)
                (< 0 (- b a))
                (i-close a b)
                (standard-numberp a))
           (i-close (/ (integral-rcfn a b)
                       (- b a))
                    (rcfn a)))
  :hints (("Goal"
           :in-theory (disable distributivity
                               distributivity-commuted
                               commutativity-of-+)
           :use
           ((:instance
             between-i-close-implies-i-close
             (z (/ (integral-rcfn a b)
                   (- b a)))
             (x (rcfn (min-x a b)))
             (y (rcfn (max-x a b)))
             (r (rcfn a))))))
  :rule-classes nil)

;;;;;;; Start proof of ftoc-lemma-as-i-close-case-2.

(defthm ftoc-lemma-as-i-close-case-2-helper-1
  (equal (/ (+ a (- b)))
         (/ (- (+ (- a) b))))
  :rule-classes nil)

(defthm ftoc-lemma-as-i-close-case-2-helper-2
  (implies (and (realp a)
                (realp b)
                (realp x))
           (equal (* x (/ (+ a (- b))))
                  (- (* x (/ (+ (- a) b))))))
  :hints (("Goal" :use ftoc-lemma-as-i-close-case-2-helper-1
           :in-theory (disable distributivity-of-minus-over-+))))

(defthm ftoc-lemma-as-i-close-case-2-helper-3
  (implies (and (realp a)
                (realp b)
                (< b a)
                (i-close a b)
                (standard-numberp a))
           (equal (- (* (integral-rcfn b a) (/ (+ (- a) b))))
                  (* (integral-rcfn b a) (/ (+ a (- b)))))))

(defthm-std integral-rcfn-reverse
    (implies (and (realp a)
                  (realp b)
                  (< b a))
             (equal (integral-rcfn a b)
                    (- (integral-rcfn b a)))))

(in-theory (disable ftoc-lemma-as-i-close-case-2-helper-2))

(defthm ftoc-lemma-as-i-close-case-2
  (implies (and (realp a)
                (realp b)
                (< (- b a) 0)
                (i-close a b)
                (standard-numberp a))
           (i-close (/ (integral-rcfn a b) (- b a))
                    (rcfn a)))
  :hints (("Goal"
           :use
           ((:instance
             between-i-close-implies-i-close
             (z (/ (integral-rcfn b a) (+ a (- b))))
             (x (rcfn (min-x b a)))
             (y (rcfn (max-x b a)))
             (r (rcfn a))))
           :in-theory
           (union-theories '(i-close-symmetric)
                           (disable <-+-negative-0-2)))))

;;;;;;; End proof of ftoc-lemma-as-i-close-case-2.

(defthm ftoc-lemma-as-i-close
  (implies (and (realp eps)
                (not (equal eps 0))
                (i-small eps)
                (realp x) (standard-numberp x))
           (i-close (/ (integral-rcfn x (+ eps x))
                       eps)
                    (rcfn x)))
  :hints (("Goal"
           :use
           ((:instance ftoc-lemma-as-i-close-case-1
                       (a x)
                       (b (+ eps x)))
            (:instance ftoc-lemma-as-i-close-case-2
                       (a x)
                       (b (+ eps x))))))
  :rule-classes nil)

(defthm i-close-is-equal-standard-part-1
  (implies (and (realp a)
                (standard-numberp b)
                (realp b))
           (iff (i-close a b)
                (equal (standard-part a) b)))
  :hints (("Goal" :in-theory (enable i-close i-small))))

(defthm ftoc-lemma
  (implies (and (realp eps)
                (not (equal eps 0))
                (i-small eps)
                (realp x) (standard-numberp x))
           (equal (standard-part
                   (/ (integral-rcfn x (+ x eps))
                      eps))
                  (rcfn x)))
  :hints (("Goal" :use ftoc-lemma-as-i-close)))
