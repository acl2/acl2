(in-package "ACL2")

(deflabel ftoc-start)

(include-book "riemann-defuns")
(include-book "make-partition")
(local (include-book "riemann-lemmas"))
(local (include-book "integral-rcfn-lemmas"))
(local (include-book "nsa-lemmas"))
(include-book "integral-rcfn")

(encapsulate
 ()
 (local (include-book "split-integral-by-subintervals"))

 (defthm-std split-integral-by-subintervals
   (implies (and (realp a)
                 (realp b)
                 (realp c))
            (equal (integral-rcfn a c)
                   (+ (integral-rcfn a b)
                      (integral-rcfn b c)))))
 )

(local (in-theory (disable split-integral-by-subintervals)))

(defthm split-integral-by-subintervals-difference
  (implies (and (realp a)
                (realp b)
                (realp c))
           (equal (- (integral-rcfn a c)
                     (integral-rcfn a b))
                  (integral-rcfn b c)))
  :hints (("Goal"
           :in-theory
           (disable integral-rcfn)
           :use split-integral-by-subintervals)))

(encapsulate
 ()
 (local (include-book "ftoc-lemma"))

 (defthm ftoc-lemma
   (implies (and (realp eps)
                 (not (equal eps 0))
                 (i-small eps)
                 (realp x) (standard-numberp x))
            (equal (standard-part
                    (/ (integral-rcfn x (+ x eps))
                       eps))
                   (rcfn x)))))

(defthm fundamental-theorem-of-calculus-nonclassical
  (implies (and (realp eps)
                (not (equal eps 0))
                (i-small eps)
                (realp a) (standard-numberp a)
                (realp x) (standard-numberp x))
           (equal (standard-part
                   (/ (- (integral-rcfn a (+ x eps))
                         (integral-rcfn a x))
                      eps))
                  (rcfn x)))
  :hints (("Goal"
           :in-theory
           (set-difference-theories
            (union-theories
             '(split-integral-by-subintervals-difference
               ftoc-lemma)
             (current-theory 'ftoc-start))
            '(distributivity commutativity-of-+
                             commutativity-of-*))))
  :rule-classes nil)

(in-theory (disable integral-rcfn))

(encapsulate
 ()

 (local
  (defthm integral-rcfn-prime-hint
    (implies
     (and (standard-numberp a) (realp a)
          (standard-numberp x) (realp x))
     (let ((eps (/ (i-large-integer))))
       (standard-numberp
        (standard-part (* (+ (integral-rcfn a (+ x eps))
                             (- (integral-rcfn a x)))
                          (i-large-integer))))))
    :hints (("Goal"
             :use
             ((:instance
               fundamental-theorem-of-calculus-nonclassical
               (eps (/ (i-large-integer)))))))))

 (local (in-theory (disable
                    split-integral-by-subintervals-difference
                    distributivity-commuted
                    functional-commutativity-of-minus-*-left
                    commutativity-of-*
                    /r-when-abs-numerator=1
                    numerator-/x
                    commutativity-of-+)))

 (defun-std integral-rcfn-prime (a x)
   (if (and (realp a) (realp x))
       (let ((eps (/ (i-large-integer))))
         (standard-part
          (/ (- (integral-rcfn a (+ x eps))
                (integral-rcfn a x))
             eps)))
     0)))

;;; This sort of theorem is a proof obligation that we have whenever
;;; we introduce the derivative of a standard function.
(defthm integral-rcfn-prime-exists
  (implies (and (realp eps)
                (not (equal eps 0))
                (i-small eps)
                (realp a) (standard-numberp a)
                (realp x) (standard-numberp x))
           (equal (standard-part
                   (/ (- (integral-rcfn a (+ x eps))
                         (integral-rcfn a x))
                      eps))
                  (integral-rcfn-prime a x)))
  :hints (("Goal"
           :use
           (fundamental-theorem-of-calculus-nonclassical
            (:instance
             fundamental-theorem-of-calculus-nonclassical
             (eps (/ (i-large-integer)))))
           :in-theory
           (disable numerator-/x))))

(defthm-std fundamental-theorem-of-calculus
  (implies (and (realp a)
                (realp x))
           (equal (integral-rcfn-prime a x)
                  (rcfn x)))
  :hints (("Goal"
           :use ((:instance
                  fundamental-theorem-of-calculus-nonclassical
                  (eps (/ (i-large-integer)))))
           :in-theory
           (disable numerator-/x))))
