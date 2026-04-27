(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "ln")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(defun raise (a x)
  (if (= x 0)
      1
    (if (equal (fix a) 0)
        0
      (acl2-exp (* x (acl2-ln a))))))

(encapsulate
 ()

 (local
  (defthm raise-expt-for-non-negative-exponents
    (implies (and (integerp i)
                  (<= 0 i))
             (equal (raise a i)
                    (expt a i)))))

 (local
  (defthm raise-expt-for-negative-exponents
    (implies (and (integerp i)
                  (< i 0))
             (equal (raise a i)
                    (expt a i)))
    :hints (("Goal"
             :use ((:instance raise-expt-for-non-negative-exponents
                              (i (- i))))
             :in-theory (disable raise-expt-for-non-negative-exponents)))))

 (defthm raise-expt
   (implies (integerp i)
             (equal (raise a i)
                    (expt a i)))
    :hints (("Goal"
             :cases ((<= 0 i)))))

 )

(defthm raise-acl2-exp
  (implies (acl2-numberp x)
           (equal (raise (acl2-exp 1) x)
                  (acl2-exp x))))

(defthm power-of-sums
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (raise a (+ x y))
                  (if (equal (+ x y) 0)
                      1
                      (* (raise a x) (raise a y))))))

(defthmd power-of-powers
    (implies (and (<= 0 (imagpart (* x (acl2-ln a))))
                  (< (imagpart (* x (acl2-ln a))) (* 2 (acl2-pi)))
                  (acl2-numberp x)
                  (acl2-numberp y))
             (equal (raise (raise a x) y)
                    (raise a (* x y)))))

(defthmd power-of-powers-for-non-negative-real-base
    (implies (and (realp a)
                  (<= 0 a)
                  (realp x)
                  (acl2-numberp y))
             (equal (raise (raise a x) y)
                    (raise a (* x y))))
  :hints (("Goal"
           :use ((:instance power-of-powers)
                 (:instance realp-ln
                            (y a))
                 )
           :in-theory (disable realp-ln)))
  )

#|
(encapsulate
    () ;; start lemmas for power-of-powers-for-reals-3

    (local
     (defthmd lemma-1
         (implies (and (realp a)
                       (< a 0))
                  (equal (acl2-ln a)
                         (+ (acl2-ln (- a))
                            (* #c(0 1) (acl2-pi)))))
       :hints  (("Goal"
                 :in-theory (enable acl2-ln
                                    complex-definition)))
       ))

  (local
   (defthmd lemma-2
       (equal (acl2-ln -1) (* #c(0 1) (acl2-pi)))
     :hints (("Goal"
              :use ((:instance ln-1))
              :in-theory (e/d (acl2-ln
                               complex-definition)
                              (ln-1))))))

  (defthmd power-of-powers-for-reals-3
     (implies (and (realp a)
                   (< a 0)
                   (realp x)
                   (acl2-numberp y))
              (equal (raise (raise a x) y)
                     (* (raise (- a) (* x y))
                        (raise -1 (* x y)))))
   :hints (("Goal"
            :use ((:instance lemma-1)
                  (:instance exp-sum
                             (x (* x (acl2-ln (- a))))
                             (y (* x (* #c(0 1) (acl2-pi)))))
                  )
            :in-theory (disable exp-sum
                                e^ix-cos-i-sin)
            ))
   )
  )
)
|#

(defthmd ln-of-powers-positive
    (implies (and (realp a)
                  (< 0 a)
                  (realp x)
                  (< 0 x))
             (equal (acl2-ln (raise a x))
                    (* x (acl2-ln a))))
  :hints (("Goal"
           :use ((:instance realp-ln (y a))
                 )
           :in-theory (disable realp-ln)))
  )


(defthm exp-of-powers-real-1
    (implies (and (realp x)
                  (acl2-numberp y))
             (equal (raise (acl2-exp x) y)
                    (acl2-exp (* x y))))
  :hints (("Goal"
           :use ((:instance power-of-powers
                            (a (acl2-exp 1))
                            (x x)
                            (y y))
                 )
           :in-theory (disable power-of-powers)
           )))


(defthm raise-a---x
  (implies (acl2-numberp x)
           (equal (raise a (- x))
                  (/ (raise a x))))
  )

(defthm raise-sqrt
  (implies (and (realp x)
                (<= 0 x))
           (equal (raise x 1/2) (acl2-sqrt x)))
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x
                            (x x)
                            (y (raise x 1/2))))
           :in-theory (disable y*y=x->y=sqrt-x))
          ("Subgoal 3"
           :use ((:instance acl2-exp->-0-for-reals
                            (x (* 1/2 (acl2-ln x)))))
           :in-theory (disable acl2-exp->-0-for-reals))
          ("Subgoal 2"
           :use ((:instance exp-sum
                            (x (* 1/2 (acl2-ln x)))
                            (y (* 1/2 (acl2-ln x)))))
           :in-theory (disable exp-sum))))
