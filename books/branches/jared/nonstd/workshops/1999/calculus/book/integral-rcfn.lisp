(in-package "ACL2")

(include-book "make-partition")

(encapsulate
 ()
 (local (include-book "standard-part-riemann-rcfn-is-standard"))

 (defthm standard-part-riemann-rcfn-is-standard
   (implies (and (standard-numberp a) (realp a)
                 (standard-numberp b) (realp b)
                 (< a b))
            (standard-numberp
             (standard-part (riemann-rcfn
                             (make-partition a b (i-large-integer))))))))

(include-book "nsa-lemmas")

(encapsulate
 ()

 (local
  (in-theory (disable riemann-rcfn make-partition)))

 (defun-std integral-rcfn (a b)
   (cond
    ((or (not (realp a))
         (not (realp b)))
     0)
    ((< a b)
     (standard-part (riemann-rcfn
                     (make-partition a b (i-large-integer)))))
    ((< b a)
     (- (standard-part (riemann-rcfn
                        (make-partition b a (i-large-integer))))))
    (t 0)))

 )
