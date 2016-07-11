(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-lemmas")
(include-book "integral-rcfn")
(include-book "nsa-lemmas")

(encapsulate
 ()
 (local (include-book "riemann-sum-approximates-integral"))
 (defthm riemann-sum-approximates-integral
   (implies (and (partitionp p)
                 (equal a (car p))
                 (equal b (car (last p)))
                 (< a b)
                 (standard-numberp a)
                 (standard-numberp b)
                 (i-small (mesh p)))
            (i-close (riemann-rcfn p)
                     (integral-rcfn a b)))))

;;; Main idea of proof of split-integral-by-subintervals:
;;; each integral-rcfn term in the conclusion is i-close to a
;;; riemann-rcfn term involving an appropriate partition:
;;;
;;; p-ab for the uniform partition from a to b using (i-large-integer)
;;; p-bc for the uniform partition from b to c using (i-large-integer)
;;; p-ac for the result of combining those two partitions.
;;;
;;; So, we will eventually need the following lemma on combining
;;; partitions, which has been added to riemann-lemmas.lisp but is
;;; left here for documentation purposes.

(defthm partitionp-append
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car p2)))
           (partitionp (append p1 (cdr p2)))))

;;; Next, we prove a lemma that lets us reduce the desired result to a
;;; corresponding lemma about i-close.
(encapsulate
 ()
 (local (include-book "integral-rcfn-equal-if-i-close"))
 (defthm integral-rcfn-equal-if-i-close
   (implies (and (realp a) (standard-numberp a)
                 (realp b) (standard-numberp b)
                 (< a b) ; discovered missing during its proof
                 (realp y)
                 (realp z))
            (equal (equal (integral-rcfn a b)
                          (+ (standard-part y) (standard-part z)))
                   (i-close (integral-rcfn a b) (+ y z))))))

;;; Note:  We need realp-riemann-rcfn here in order to apply the
;;; preceding lemma, where y and z are the riemann-rcfns of partitions
;;; from a to b and from b to c.

;;; But we also now need to know that the aforementioned partitions
;;; from a to b and from b to c are indeed partitions, in order to
;;; relieve the hypothesis of the preceding lemma.  The last of htese
;;; is what we need first, but we need the second one later.  Rewrite
;;; rules car-make-partition and car-last-make-partition were
;;; originally proved here in an encapsulate as trivial consequences
;;; of locally-included book "riemann-sum-approximates-integral-1".
;;; They are now forward-chaining rules in integral-rcfn-lemmmas.lisp.

;;; Note that mesh-make-partition is among the lemmas needed to finish
;;; off the proof of split-integral-by-subintervals, discovered in the
;;; proof-builder. Although originally proved in
;;; riemann-sum-approximates-integral-1.lisp, it has been moved to
;;; integral-rcfn-lemmas.lisp

(include-book "integral-rcfn-lemmas")

;;; An attempt now to prove split-integral-by-subintervals results in
;;; having to combine the two riemann sums on the right-hand side.

(defthm split-riemann-rcfn-by-subintervals
  (implies
   (and (partitionp p1)
        (partitionp p2)
        (equal (car (last p1)) (car p2)))
   (equal (+ (riemann-rcfn p1)
             (riemann-rcfn p2))
          (riemann-rcfn (append p1 (cdr p2))))))

(defthm riemann-sum-approximates-integral-commuted
  (implies (and (partitionp p)
                (equal a (car p))
                (equal b (car (last p)))
                (< a b)
                (standard-numberp a)
                (standard-numberp b)
                (i-small (mesh p)))
           (i-close (integral-rcfn a b)
                    (riemann-rcfn p)))
  :hints (("Goal" :use riemann-sum-approximates-integral
           :in-theory
           (union-theories
            '(i-close-symmetric)
            (disable riemann-sum-approximates-integral
                     mesh integral-rcfn riemann-rcfn partitionp)))))

;;; Lemmas discovered attempting to prove
;;; split-integral-by-subintervals in the proof-builder by
;;; backchaining through rewrite rules:

(defthm car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))
(defthm consp-append
  (equal (consp (append x y))
         (or (consp x) (consp y))))
(defthm car-last-append
  (equal (car (last (append x y)))
         (if (consp y)
             (car (last y))
           (car (last x)))))
(defthm consp-cdr-make-partition-rec
  (implies (and (integerp n)
                (< 1 n))
           (consp (cdr (make-partition-rec a delta n))))
  :hints (("Goal" :expand (make-partition-rec a delta n))))
(defthm consp-cdr-make-partition
  (implies (and (integerp n)
                (< 1 n))
           (consp (cdr (make-partition a b n)))))
(defthm i-large-integer-is-greater-than-1
  (< 1 (i-large-integer))
  :hints (("Goal" :use
           (i-large-integer-is-large
            (:instance large-if->-large
                       (y 1)
                       (x (i-large-integer))))
           :in-theory
           (disable i-large-integer-is-large
                    large-if->-large))))

;;; Mesh-append has been moved from here to riemann-lemmas.lisp.

;;; CAREFUL!  The following could cause looping
(local
 (defthm car-last-cdr
   (implies (consp (cdr x))
            (equal (car (last (cdr x)))
                   (car (last x))))))
(in-theory (disable last))

;;; Gross!  Once I got the proof of split-integral-by-subintervals
;;; through the proof-builder, I could not replay it directly as the
;;; defthm shown below.  I found that there was a term (i-small (mesh
;;; ...)) that was apparently being rewritten to (i-small (max ...)),
;;; which reduced to (i-small (if ...)).  Hence, the following lemma:
(defthm i-small-if
  (equal (i-small (if x y z))
         (if x (i-small y) (i-small z))))

;;; End of lemmas discovered attempting to prove
;;; split-integral-by-subintervals.

;;; The following was necessary after the defun of integral-rcfn was
;;; replaced by a defun-std, because :expand no longer worked.
(defthm integral-rcfn-rewrite-hack
  (implies (and (standard-numberp a)
                (standard-numberp b)
                (syntaxp (or (and (equal a 'a)
                                  (equal b 'b))
                             (and (equal a 'b)
                                  (equal b 'c)))))
           (equal (integral-rcfn a b)
                  (cond
                   ((or (not (realp a)) (not (realp b))) 0)
                   ((< a b)
                    (standard-part
                     (riemann-rcfn (make-partition a b (i-large-integer)))))
                   ((< b a)
                    (-
                     (standard-part
                      (riemann-rcfn (make-partition b a (i-large-integer))))))
                   (t 0)))))

(defthm split-integral-by-subintervals-ordered
  (implies (and (realp a)
                (realp b)
                (realp c)
                (< a b)
                (< b c)
                (standard-numberp a)
                (standard-numberp b)
                (standard-numberp c))
           (equal (integral-rcfn a c)
                  (+ (integral-rcfn a b)
                     (integral-rcfn b c))))
  :hints (("Goal"
           :in-theory
           (disable riemann-rcfn make-partition integral-rcfn mesh
                    ;; We want to prove lemmas about i-close, rather
                    ;; than reducing it to equality of standard
                    ;; parts.
                    i-close)))
  :rule-classes nil)

(defthm integral-rcfn-reversed
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b))
           (equal (integral-rcfn a b)
                  (- (integral-rcfn b a))))
  :rule-classes nil)

(defthm integral-rcfn-reversed-rewrite
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b)
                (< b a))
           (equal (integral-rcfn a b)
                  (- (integral-rcfn b a)))))

(defthm integral-rcfn-a-a
  (implies (and (realp a) (standard-numberp a))
           (equal (integral-rcfn a a)
                  0))
  :hints (("Goal" :in-theory (disable integral-rcfn-reversed-rewrite))))

(defthm integral-rcfn-reversed-rewrite-2
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b))
           (equal (equal (integral-rcfn a b)
                         (- (integral-rcfn b a)))
                  t)))

(defthm integral-rcfn-reversed-rewrite-3
  (implies (and (realp a) (standard-numberp a)
                (realp b) (standard-numberp b))
           (equal (equal 0
                         (+ (integral-rcfn a b)
                            (integral-rcfn b a)))
                  t)))

(defthm-std split-integral-by-subintervals
  (implies (and (realp a)
                (realp b)
                (realp c))
           (equal (integral-rcfn a c)
                  (+ (integral-rcfn a b)
                     (integral-rcfn b c))))
  ;; slight change in hints for v2-6
  :hints (("Goal"
           :in-theory
           (disable integral-rcfn integral-rcfn-rewrite-hack)
           :use
           ((:instance
             split-integral-by-subintervals-ordered
             (a (if (< a b)
                    (if (< b c)
                        a ; a < b < c
                      (if (< a c) ; a < c <= b
                          a
                        c)) ; c <= a < b
                  (if (< a c)
                      b ; b <= a < c
                    (if (< b c) ; b < c <= a
                        b
                      c)))) ; c <= b <= a
             (b (if (< a b)
                    (if (< b c)
                        b ; a < b < c
                      (if (< a c) ; a < c <= b
                          c
                        a)) ; c <= a < b
                  (if (< a c)
                        a ; b <= a < c
                      (if (< b c) ; b < c <= a
                          c
                        b)))) ; c <= b <= a
             (c (if (< a b)
                    (if (< b c)
                        c ; a < b < c
                      (if (< a c) ; a < c <= b
                          b
                        b)) ; c <= a < b
                  (if (< a c)
                        c ; b <= a < c
                      (if (< b c) ; b < c <= a
                          a
                        a)))) ; c <= b <= a
             )))
          ("Goal'" :cases ((equal a b)))))
