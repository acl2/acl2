(in-package "ACL2")

(include-book "lop1") ;BOZO
(include-book "lior");BOZO
(local (include-book "lop2-proofs"))

(defthm lop-thm-1
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (= e (expo a))
                (< (expo b) e)
                (= lambda
                   (lior (* 2 (mod a (expt 2 e)))
                         (lnot (* 2 b) (1+ e))
                         (1+ e))))
           (or (= (expo (- a b)) (expo lambda))
               (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())