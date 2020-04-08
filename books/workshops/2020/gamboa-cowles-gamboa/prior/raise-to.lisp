(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nonstd/nsa/ln" :dir :system)

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

(defun raise-to (a x)
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
             (equal (raise-to a i)
                    (expt a i)))))

 (local
  (defthm raise-expt-for-negative-exponents
    (implies (and (integerp i)
                  (< i 0))
             (equal (raise-to a i)
                    (expt a i)))
    :hints (("Goal"
             :use ((:instance raise-expt-for-non-negative-exponents
                              (i (- i))))
             :in-theory (disable raise-expt-for-non-negative-exponents)))))

 (defthm raise-expt
   (implies (integerp i)
             (equal (raise-to a i)
                    (expt a i)))
    :hints (("Goal"
             :cases ((<= 0 i)))))

 )

(defthm raise-acl2-exp
  (implies (acl2-numberp x)
           (equal (raise-to (acl2-exp 1) x)
                  (acl2-exp x))))

(defthm power-of-sums
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (raise-to a (+ x y))
                  (if (equal (+ x y) 0)
                      1
                    (* (raise-to a x) (raise-to a y))))))

(defthm raise-a---x
  (implies (acl2-numberp x)
           (equal (raise-to a (- x))
                  (/ (raise-to a x)))))

(defthm raise-sqrt
  (implies (and (realp x)
                (<= 0 x))
           (equal (raise-to x 1/2) (acl2-sqrt x)))
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x
                            (x x)
                            (y (raise-to x 1/2))))
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
