; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "sqrt")


(local (deftheory jared-disables-1
         #!acl2
         '(SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE)
           (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE)
           )))

(local (deftheory jared-disables-2
         #!acl2
         '((:TYPE-PRESCRIPTION NOT-INTEGERP-3B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))))

(local (deftheory jared-disables-3
         #!acl2
         '((:TYPE-PRESCRIPTION NOT-INTEGERP-4B)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT)
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT)
           (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION)
           )))

(local (deftheory jared-disables-4
         #!acl2
         '(not-integerp-1a
           not-integerp-2a
           not-integerp-3a
           not-integerp-4a
           not-integerp-1d
           not-integerp-2d
           not-integerp-3d
           not-integerp-4d
           not-integerp-1f
           not-integerp-2f
           not-integerp-3f
           not-integerp-4f
           default-plus-1
           default-plus-2
           default-times-1
           default-times-2
           default-less-than-1
           default-less-than-2
           default-expt-2
           default-minus)))

(local (deftheory jared-disables-5
         #!acl2
         '(EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
           EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
           EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
           EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
           not-integerp-1a-expt
           not-integerp-2a-expt
           not-integerp-3a-expt
           not-integerp-4a-expt
           not-integerp-1d-expt
           not-integerp-2d-expt
           not-integerp-3d-expt
           not-integerp-4d-expt
           default-expt-1
           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
           EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
           EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)))

(local-defthm lemma-4-1-1
  (implies (and (not (zp k))
                (not (zp rho))
                (rationalp x)
                (>= (* k rho) 2)
                (< 1/4 x)
                (< x 1))
           (and (< (* (expt 2 (* k rho)) x)
                   (expt 2 (* k rho)))
                (> (* (expt 2 (* k rho)) x)
                   (expt 2 (- (* k rho) 2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-strongly-monotonic (x (expt 2 (* k rho)))
                                                        (y x) (y+ 1))
                        (:instance *-strongly-monotonic (x (expt 2 (* k rho)))
                                                        (y+ x) (y 1/4))))))

(local-defthm lemma-4-1-2
  (implies (and (rationalp x)
                (integerp a)
                (integerp b)
                (< x a)
                (> x b))
           (and (< (fl x) a)
                (>= (fl x) b)))
  :rule-classes ())

(local-defthm lemma-4-1-3
  (implies (and (not (zp k))
                (not (zp rho))
                (rationalp x)
                (>= (* k rho) 2)
                (< 1/4 x)
                (< x 1))
            (let ((l (fl (* (expt 2 (* k rho)) x))))
              (and (< l (expt 2 (* k rho)))
                   (>= l (expt 2 (- (* k rho) 2))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-1
                        (:instance lemma-4-1-2 (x (* (expt 2 (* k rho)) x))
                                               (a (expt 2 (* k rho)))
                                               (b (expt 2 (- (* k rho) 2))))))))

(local-defthm lemma-4-1-5
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (and (< q 1)
                  (<= 1/2 q))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5
                               )
           :use (lemma-4-1-3
                 (:instance *-weakly-monotonic (x (expt 2 (* k rho)))
                            (y 1/2)
                            (y+ (* (expt 2 (- (* k rho))) s)))
                 (:instance *-strongly-monotonic (x (expt 2 (* k rho)))
                            (y+ 1)
                            (y (* (expt 2 (- (* k rho))) s)))))))

(local-defthm lemma-4-1-7
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (<= (* (expt 2 (- (* k rho)))
                    (expt (1- (* q (expt 2 (* k rho)))) 2))
                 l)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-4-1-3))))

(local-defthm lemma-4-1-8
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (<= (* (expt 2 (* k rho))
                    (expt (- q (expt 2 (- (* k rho)))) 2))
                 l)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-7))))

(local-defthm lemma-4-1-9
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (<= (expt (- q (expt 2 (- (* k rho)))) 2)
                 (* (expt 2 (- (* k rho)))
                    l))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-8
                        (:instance *-weakly-monotonic
                         (x (expt 2 (* k rho)))
                         (y+ (* (expt 2 (- (* k rho)))
                                (fl (* (expt 2 (* k rho)) x))))
                         (y  (expt (- (* (expt 2 (- (* k rho))) s)
                                      (expt 2 (- (* k rho))))
                                   2)))))))

(local-defthm lemma-4-1-10
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= (* (expt 2 (- (* k rho)))
                    (expt (1+ (* q (expt 2 (* k rho)))) 2))
                 (1+ l))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-3))))

(local-defthm lemma-4-1-11
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= (* (expt 2 (* k rho))
                    (expt (+ q (expt 2 (- (* k rho)))) 2))
                 (1+ l))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-10))))

(local-defthm lemma-4-1-12
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho)))s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= (expt (+ q (expt 2 (- (* k rho)))) 2)
                 (* (expt 2 (- (* k rho)))
                    (1+ l)))))
  :rule-classes ()
  :hints (("Goal"
           :use (lemma-4-1-11
                 (:instance *-weakly-monotonic
                            (x (expt 2 (* k rho)))
                            (y (* (expt 2 (- (* k rho)))
                                  (1+ (fl (* (expt 2 (* k rho)) x)))))
                            (y+  (expt (+ (* (expt 2 (- (* k rho))) s)
                                          (expt 2 (- (* k rho))))
                                       2)))))))

(local-defthm lemma-4-1-13
  (let* ((l (fl (* (expt 2 (* k rho)) x))))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
              (and (<= l (* x (expt 2 (* k rho))))
                   (> (1+ l) (* x (expt 2 (* k rho)))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-1
                        (:instance fl-def (x (* (expt 2 (* k rho)) x)))))))

(local-defthm lemma-4-1-14
  (implies (and (not (zp k))
                (not (zp rho))
                (rationalp x)
                (>= (* k rho) 2)
                (< 1/4 x)
                (< x 1))
            (let ((l (fl (* (expt 2 (* k rho)) x))))
              (<= (* (expt 2 (- (* k rho))) l)
                  x)))
  :rule-classes ()
  :hints (("Goal"
           :use (lemma-4-1-13
                 (:instance *-weakly-monotonic (x (expt 2 (* k rho)))
                            (y (* (fl (* (expt 2 (* k rho)) x))
                                  (expt 2 (- (* k rho)))))
                            (y+ x))))))

(local-defthm lemma-4-1-15
  (implies (and (not (zp k))
                (not (zp rho))
                (rationalp x)
                (>= (* k rho) 2)
                (< 1/4 x)
                (< x 1))
            (let ((l (fl (* (expt 2 (* k rho)) x))))
              (> (* (expt 2 (- (* k rho))) (1+ l))
                 x)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-13
                        (:instance *-strongly-monotonic
                                   (x (expt 2 (* k rho)))
                                   (y+ (* (1+ (fl (* (expt 2 (* k rho)) x)) )
                                          (expt 2 (- (* k rho)))))
                                   (y x))))))

(local-defthm lemma-4-1-16
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (< x (expt (+ q (expt 2 (- (* k rho)))) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-12 lemma-4-1-15))))

(local-defthm lemma-4-1-17
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s)))
    (implies (and (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= x (expt (- q (expt 2 (- (* k rho)))) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-9 lemma-4-1-14))))

(local-defthm lemma-4-1-a-1
  (implies (and (not (zp k))
                (not (zp rho))
                (rationalp x)
                (>= (* k rho) 2)
                (< 1/4 x)
                (< x 1))
    (let ((l (fl (* (expt 2 (* k rho)) x))))
      (implies (and (integerp s)
                    (<= (expt 2 (1- (* k rho))) s)
                    (< s (expt 2 (* k rho)))
                    (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                        l)
                    (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                        (1+ l)))
               (let ((q (* (expt 2 (- (* k rho))) s)))
                 (and (<= 1/2 q)
                      (< q 1)
                      (>= x (expt (- q (expt 2 (- (* k rho)))) 2))
                      (< x (expt (+ q (expt 2 (- (* k rho)))) 2)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-5 lemma-4-1-16 lemma-4-1-17))))

(encapsulate (((rho**) => *) ((k**) => *) ((x**) => *) ((s**) => *))

(local (defun k** () 1))

(local (defun rho** () 2))

(defthm k**-rho**-constraint
  (and (not (zp (k**)))
       (not (zp (rho**)))
       (>= (* (k**) (rho**)) 2))
  :rule-classes ())

(local (defun x** () 1/2))

(defthm x**-constraint
  (and (rationalp (x**))
       (> (x**) 1/4)
       (< (x**) 1))
  :rule-classes ())

(defun l** () (fl (* (expt 2 (* (k**) (rho**))) (x**))))

(local (defun s** () 3))

(defthm s**-constraint
  (and (integerp (s**))
       (<= (expt 2 (1- (* (k**) (rho**)))) (s**))
       (< (s**) (expt 2 (* (k**) (rho**))))
       (<= (* (expt 2 (- (* (k**) (rho**)))) (expt (1- (s**)) 2))
           (l**))
       (>= (* (expt 2 (- (* (k**) (rho**)))) (expt (1+ (s**)) 2))
           (1+ (l**))))
  :rule-classes ())

(defun q0** () (* (expt 2 (- (* (k**) (rho**)))) (s**)))

)

(defthm lemma-4-1-a
  (and (<= 1/2 (q0**))
       (< (q0**) 1)
       (>= (x**) (expt (- (q0**) (expt 2 (- (* (k**) (rho**))))) 2))
       (< (x**) (expt (+ (q0**) (expt 2 (- (* (k**) (rho**))))) 2)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5)
           :use (k**-rho**-constraint
                 x**-constraint
                 s**-constraint
                 (:instance lemma-4-1-a-1 (k (k**)) (rho (rho**)) (x (x**)) (s (s**)))))))

(local-defthm cg-sqrt-1
  (implies (and (rationalp x)
                (rationalp y)
                (<= 0 x)
                (<= 0 y))
           (iff (<= x y)
                (<= (* x x) (* y y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x (+ x y)) (y 0) (y+ (- y x)))))))

(local-defthm lemma-4-1-18
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s))))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (> q 1/2)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5
                               )
           :use ((:instance cg-sqrt-1 (x (* (expt 2 (- (* k rho))) s))
                            (y 1/2))))))

(local-defthm lemma-4-1-19
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s))))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (> s (expt 2 (1- (* k rho))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-5)
           :use (lemma-4-1-18
                 (:instance *-strongly-monotonic (x (expt 2 (* k rho))) (y 1/2) (y+ q))))))

(local-defthm lemma-4-1-20
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s))))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= s1 (expt 2 (1- (* k rho))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               ;jared-disables-5
                               )
           :use (lemma-4-1-19))))


(local-defthm lemma-4-1-21
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s)))
         (q1 (* (expt 2 (- (* k rho))) s1)))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= q1 1/2)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               )
           :use (lemma-4-1-20
                 (:instance *-weakly-monotonic (x (expt 2 (- (* k rho)))) (y (expt 2 (1- (* k rho)))) (y+ (1- s)))))))

(local-defthm lemma-4-1-22
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s)))
         (q1 (* (expt 2 (- (* k rho))) s1)))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (< q1 q)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-20
                        (:instance *-strongly-monotonic (x (expt 2 (- (* k rho)))) (y (1- s)) (y+ s))))))

(local-defthm lemma-4-1-23
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (> x (* q q)))
                 s
               (1- s)))
         (q1 (* (expt 2 (- (* k rho))) s1)))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (>= q1 (expt 2 (- (* k rho))))))
  :rule-classes ()
  :hints (("Goal"
           :use (lemma-4-1-21))))

(local-defthm lemma-4-1-24
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s)))
         (q1 (* (expt 2 (- (* k rho))) s1)))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (<= (expt (- q1 (expt 2 (- (* k rho)))) 2)
                 (expt (- q (expt 2 (- (* k rho)))) 2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5)
           :use (lemma-4-1-23
                 lemma-4-1-22
                 (:instance cg-sqrt-1 (x (- (* (expt 2 (- (* k rho))) s) (expt 2 (- (* k rho)))))
                            (y (- (* (expt 2 (- (* k rho))) (1- s)) (expt 2 (- (* k rho))))))))))

(local-defthm lemma-4-1-25
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s)))
         (q1 (* (expt 2 (- (* k rho))) s1)))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (< x (expt (+ q1 (expt 2 (- (* k rho)))) 2))))
  :rule-classes ())

(local-defthm lemma-4-1-26
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x y)
                (>= y z))
           (>= x z))
  :rule-classes ())

(local-defthm lemma-4-1-27
  (let* ((l (fl (* (expt 2 (* k rho)) x)))
         (q (* (expt 2 (- (* k rho))) s))
         (s1 (if (or (= (mod s 2) 1)
                     (>= x (* q q)))
                 s
               (1- s)))
         (q1 (* (expt 2 (- (* k rho))) s1)))
    (implies (and (= s1 (1- s))
                  (not (zp k))
                  (not (zp rho))
                  (rationalp x)
                  (>= (* k rho) 2)
                  (< 1/4 x)
                  (< x 1)
                  (integerp s)
                  (<= (expt 2 (1- (* k rho))) s)
                  (< s (expt 2 (* k rho)))
                  (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                      l)
                  (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                      (1+ l)))
             (<= (expt (- q1 (expt 2 (- (* k rho)))) 2) x)))
  :rule-classes ()
  :hints (("Goal"
           ;; 7.62 --> 2.87
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5)
           :use (lemma-4-1-24
                 lemma-4-1-a-1
                 (:instance lemma-4-1-26 (y (expt (- (* (expt 2 (- (* k rho))) s) (expt 2 (- (* k rho)))) 2))
                            (z (expt (- (* (expt 2 (- (* k rho))) (1- s)) (expt 2 (- (* k rho)))) 2)))))))

(local-defthm lemma-4-1-b-1
  (implies (and (not (zp k))
                (not (zp rho))
                (rationalp x)
                (>= (* k rho) 2)
                (< 1/4 x)
                (< x 1))
    (let ((l (fl (* (expt 2 (* k rho)) x))))
      (implies (and (integerp s)
                    (<= (expt 2 (1- (* k rho))) s)
                    (< s (expt 2 (* k rho)))
                    (<= (* (expt 2 (- (* k rho))) (expt (1- s) 2))
                        l)
                    (>= (* (expt 2 (- (* k rho))) (expt (1+ s) 2))
                        (1+ l)))
               (let* ((q (* (expt 2 (- (* k rho))) s))
                      (s1 (if (or (= (mod s 2) 1)
                                  (>= x (* q q)))
                              s
                            (1- s)))
                      (q1 (* (expt 2 (- (* k rho))) s1)))
                 (and (<= 1/2 q1)
                      (< q1 1)
                      (>= x (expt (- q1 (expt 2 (- (* k rho)))) 2))
                      (< x (expt (+ q1 (expt 2 (- (* k rho)))) 2)))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5
                               )
           :use (lemma-4-1-a-1
                 lemma-4-1-25
                 lemma-4-1-27
                 lemma-4-1-22
                 lemma-4-1-21))))

(defun s1** ()
  (if (or (= (mod (s**) 2) 1)
          (>= (x**) (* (q0**) (q0**))))
      (s**)
    (1- (s**))))

(defun q1** () (* (expt 2 (- (* (k**) (rho**)))) (s1**)))

(defthm lemma-4-1-b
  (and (<= 1/2 (q1**))
       (< (q1**) 1)
       (>= (x**) (expt (- (q1**) (expt 2 (- (* (k**) (rho**))))) 2))
       (< (x**) (expt (+ (q1**) (expt 2 (- (* (k**) (rho**))))) 2)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5)
           :use (s1**
                 k**-rho**-constraint
                 x**-constraint
                 s**-constraint
                 (:instance lemma-4-1-b-1 (k (k**)) (rho (rho**)) (x (x**)) (s (s**)))))))

(encapsulate (((h** *) => *) ((q** *) => *))

(local (defun h** (k) (declare (ignore k)) 0))

(defthm h**-constraint
  (implies (and (not (zp k))
                (> k (k**)))
           (and (integerp (h** k))
                (< (abs (h** k)) (expt 2 (rho**)))))
  :rule-classes ())

(local (defun q** (k)
  (if (or (zp k)
          (<= k (k**)))
      (q1**)
    (+ (q** (1- k))
       (* (expt 2 (- (* k (rho**))))
          (h** k))))))

(defthm q**-constraint
  (and (= (q** (k**)) (q1**))
       (implies (and (not (zp k))
                     (> k (k**)))
                (= (q** k)
                   (+ (q** (1- k))
                      (* (expt 2 (- (* k (rho**))))
                         (h** k))))))
  :hints (("Goal" ;:in-theory (theory 'minimal-theory)
                  :use (q** s**-constraint k**-rho**-constraint
                        (:instance q** (k (k**))))))
  :rule-classes ())

)

(local-defthm intp-s1
  (integerp (s1**))
  :hints (("Goal" :use (s1** s**-constraint)))
  :rule-classes (:type-prescription :rewrite))

(in-theory (disable (l**) (s1**) (q1**)))

(local-defthm ratp-q1
  (rationalp (q** (k**)))
  :hints (("Goal" :use (q**-constraint k**-rho**-constraint)))
  :rule-classes (:type-prescription :rewrite))

(local
 (encapsulate
  ()
  (local (in-theory (disable ;jared-disables-1
                             jared-disables-2
                             jared-disables-3
                             jared-disables-4
                             jared-disables-5
                             )))
  (defthm lemma-4-1-28
    (implies (and (integerp s)
                  (= (q** (k**)) (* (expt 2 (- (* (k**) (rho**)))) s))
                  (not (zp k))
                  (>= k (k**)))
             (rationalp (q** k)))
    :rule-classes (:type-prescription :rewrite)
    :hints (("Goal" :use (k**-rho**-constraint h**-constraint))
            ("Goal'" :induct (natp-induct k))
            ("Subgoal *1/2" :use q**-constraint)
            ("Subgoal *1/1" :use (:instance h**-constraint (k (1- k))))))))

(local-defthm lemma-4-1-28-2
  (implies (and (not (zp k))
                (>= k (k**)))
           (rationalp (q** k)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (q**-constraint
                        (:instance lemma-4-1-28 (s (s1**)))))))

(local-defthm lemma-4-1-29
  (implies (and (integerp a) (integerp b))
           (integerp (* a b)))
  :rule-classes ())

(local-defthm lemma-4-1-30
  (implies (and (not (zp k))
                (> k (k**))
                (integerp (* (expt 2 (* (1- k) (rho**)))
                          (q** (1- k)))))
           (integerp (* (expt 2 (* k (rho**)))
                        (q** k))))
  :rule-classes ()
  :hints (("Goal"


; Wow, slowest theorem ever.  Baseline on my AMD-8350 with a 16 GB memory threshold
; in ACL2(h) is 651 seconds.

           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               jared-disables-5
                               ;; down to 171 secs with the above
                               acl2::default-mod-1
                               acl2::default-mod-ratio
                               abs
                               acl2::zp-open
                               ;; the above were splitting.  removing them gets it to 6s
                               ;; then this one shows up heavily in accumulated persistence
                               LEMMA-4-1-28
                               ;; and removing it (the type prescription mainly) gets us
                               ;; down to .35 seconds.
                               )

; Hooray, not the slowest theorem ever, anymore.

           :use (k**-rho**-constraint
                 h**-constraint
                 q**-constraint
                 (:instance lemma-4-1-29
                            (a (* (expt 2 (* (1- k) (rho**))) (q** (1- k))))
                            (b (expt 2 (rho**))))))))

(local-defthm lemma-4-1-30-1
  (integerp (* (expt 2 (* (k**) (rho**)))
               (q1**)))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint s**-constraint h**-constraint q1**))))

(local-defthm lemma-4-1-30-2
  (integerp (* (expt 2 (* (k**) (rho**)))
               (q** (k**))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-30-1 k**-rho**-constraint h**-constraint q**-constraint))))

(local
 (encapsulate ()
  (local (in-theory (disable jared-disables-1
                             jared-disables-2
                             jared-disables-3
                             jared-disables-4
                             jared-disables-5
                             LEMMA-4-1-28
                             )))

  (defthm lemma-4-1-31
    (implies (and (not (zp k))
                  (>= k (k**)))
             (integerp (* (expt 2 (* k (rho**)))
                          (q** k))))
    :rule-classes (:type-prescription :rewrite)
    :hints (("Goal" :use (k**-rho**-constraint h**-constraint))
            ("Goal'" :induct (natp-induct k))
            ("Subgoal *1/2" :use (lemma-4-1-30-2 lemma-4-1-30))
            ("Subgoal *1/1" :use (:instance h**-constraint (k (1- k))))))))

(local-defthmd q**-rewrite
  (implies (and (not (zp k))
                (> k (k**)))
           (equal (q** k)
                  (+ (q** (1- k))
                     (* (expt 2 (- (* k (rho**))))
                        (h** k)))))
  :hints (("Goal" :use (q**-constraint))))

; well, this seems good enough for the rest.  i won't pay much attention to whether
; it speeds things up...
(local (in-theory (disable jared-disables-2
                           jared-disables-3
                           jared-disables-4
                           LEMMA-4-1-28
                           )))

(local-defthm lemma-4-1-32
  (implies (and (not (zp k))
                (> k (k**)))
           (<= (abs (- (q** (1- k)) (q** k)))
               (* (1- (expt 2 (rho**)))
                  (expt 2 (- (* k (rho**)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite)
                  :use (k**-rho**-constraint h**-constraint
                        (:instance *-weakly-monotonic (x (expt 2 (- (* k (rho**))))) (y (h** k)) (y+ (1- (expt 2 (rho**)))))
                        (:instance *-weakly-monotonic (x (expt 2 (- (* k (rho**))))) (y+ (h** k)) (y (- 1 (expt 2 (rho**)))))))))

(local-defthm lemma-4-1-33
  (implies (and (not (zp k))
                (> k (k**)))
           (<= (abs (- (q** k) (q** (k**))))
               (+ (abs (- (q** (1- k)) (q** (k**))))
                  (abs (- (q** (1- k)) (q** k))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint h**-constraint))))

(local-defthm lemma-4-1-34
  (implies (and (not (zp k))
                (> k (k**)))
           (and (rationalp (abs (- (q** k) (q** (k**)))))
                (rationalp (abs (- (q** (1- k)) (q** (k**)))))
                (rationalp (abs (- (q** (1- k)) (q** k))))
                (rationalp (* (1- (expt 2 (rho**)))
                              (expt 2 (- (* k (rho**))))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint))))

(local-defthm lemma-4-1-35
  (implies (and (not (zp k))
                (> k (k**)))
           (<= (abs (- (q** k) (q** (k**))))
               (+ (abs (- (q** (1- k)) (q** (k**))))
                  (* (1- (expt 2 (rho**)))
                     (expt 2 (- (* k (rho**))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-34 lemma-4-1-33 lemma-4-1-32))))

(local-defthm lemma-4-1-36
  (implies (and (not (zp k))
                (> k (k**)))
           (rationalp (- (expt 2 (- (* (k**) (rho**))))
                         (expt 2 (- (* (1- k) (rho**)))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint))))

(local-defthm lemma-4-1-37
  (implies (and (not (zp k))
                (> k (k**))
                (<= (abs (- (q** (1- k)) (q** (k**))))
                    (- (expt 2 (- (* (k**) (rho**))))
                       (expt 2 (- (* (1- k) (rho**)))))))
           (<= (abs (- (q** k) (q** (k**))))
               (+ (- (expt 2 (- (* (k**) (rho**))))
                     (expt 2 (- (* (1- k) (rho**)))))
                  (* (1- (expt 2 (rho**)))
                     (expt 2 (- (* k (rho**))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-34 lemma-4-1-33 lemma-4-1-32 lemma-4-1-36 lemma-4-1-35))))

(local-defthm lemma-4-1-38
  (implies (and (not (zp k))
                (> k (k**)))
           (= (+ (- (expt 2 (- (* (k**) (rho**))))
                    (expt 2 (- (* (1- k) (rho**)))))
                 (* (1- (expt 2 (rho**)))
                    (expt 2 (- (* k (rho**))))))
              (- (expt 2 (- (* (k**) (rho**))))
                 (expt 2 (- (* k (rho**)))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint))))

(local-defthm lemma-4-1-39
  (implies (and (not (zp k))
                (> k (k**))
                (<= (abs (- (q** (1- k)) (q** (k**))))
                    (- (expt 2 (- (* (k**) (rho**))))
                       (expt 2 (- (* (1- k) (rho**)))))))
           (<= (abs (- (q** k) (q** (k**))))
               (- (expt 2 (- (* (k**) (rho**))))
                  (expt 2 (- (* k (rho**)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-1-34 lemma-4-1-36 lemma-4-1-38 lemma-4-1-37))))

(local-defthm lemma-4-1-40
  (implies (and (not (zp k))
                (>= k (k**)))
           (<= (abs (- (q** k) (q** (k**))))
               (- (expt 2 (- (* (k**) (rho**))))
                  (expt 2 (- (* k (rho**)))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint))
          ("Goal'" :induct (natp-induct k))
          ("Subgoal *1/" :use lemma-4-1-39)))

(local-defthm lemma-4-1-41
  (implies (and (not (zp k))
                (>= k (k**)))
           (< (abs (- (q** k) (q** (k**))))
              (expt 2 (- (* (k**) (rho**))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-40 k**-rho**-constraint))))

(local-defthmd q**-rewrite-2
  (equal (q** (k**)) (q1**))
  :hints (("Goal" :use q**-constraint)))

(in-theory (disable s1**))

(local-defthm lemma-4-1-42
  (implies (and (not (zp k))
                (>= k (k**)))
           (< (* (expt 2 (* (k**) (rho**))) (q** k))
              (1+ (s1**))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (lemma-4-1-41 k**-rho**-constraint
                        (:instance *-strongly-monotonic (x (expt 2 (* (k**) (rho**))))
                                                        (y (q** k))
                                                        (y+ (+ (q** (k**)) (expt 2 (- (* (k**) (rho**)))))))))))

(local-defthm lemma-4-1-43
  (implies (and (not (zp k))
                (>= k (k**)))
           (<= (fl (* (expt 2 (* (k**) (rho**))) (q** k)))
               (* (expt 2 (* (k**) (rho**))) (q** (k**)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (lemma-4-1-42 k**-rho**-constraint
                        (:instance fl-def (x (* (expt 2 (* (k**) (rho**))) (q** k))))))))

(local-defthm lemma-4-1-44
  (implies (and (not (zp k))
                (>= k (k**)))
           (<= (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** k)))
               (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** (k**))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-43 k**-rho**-constraint
                        (:instance fl-monotone-linear (x (/ (fl (* (expt 2 (* (k**) (rho**))) (q** k))) 2))
                                                      (y (/ (* (expt 2 (* (k**) (rho**))) (q** (k**))) 2)))
                        (:instance *-weakly-monotonic (x 1/2)
                                                      (y (fl (* (expt 2 (* (k**) (rho**))) (q** k))))
                                                      (y+ (* (expt 2 (* (k**) (rho**))) (q** (k**)))))))))

(local-defthm lemma-4-1-45
  (implies (and (not (zp k))
                (>= k (k**))
                (>= (q** k) (q** (k**))))
           (>= (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** k)))
               (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** (k**))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint
                        (:instance fl-monotone-linear (x (* (expt 2 (1- (* (k**) (rho**)))) (q** (k**))))
                                                      (y (* (expt 2 (1- (* (k**) (rho**)))) (q** k))))
                        (:instance *-weakly-monotonic (x (expt 2 (1- (* (k**) (rho**)))))
                                                      (y (q** (k**)))
                                                      (y+ (q** k)))))))

(local-defthm lemma-4-1-46
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (>= (x**) (* (q0**) (q0**))))
           (= (q1**) (q0**)))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint q1** q0** s1**))))

(local-defthm lemma-4-1-47
  (implies (and (not (zp k))
                (>= k (k**)))
           (integerp (* (expt 2 (* k (rho**)))
                        (q** (k**)))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint
                        (:instance lemma-4-1-31 (k (k**)))
                        (:instance lemma-4-1-29 (a (* (expt 2 (* (k**) (rho**))) (q** (k**))))
                                                (b (expt 2 (* (- k (k**)) (rho**)))))))))

(local-defthm lemma-4-1-48
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**))))
           (< (* (expt 2 (* k (rho**))) (q** k))
              (* (expt 2 (* k (rho**))) (q** (k**)))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint
                        (:instance *-strongly-monotonic (x (expt 2 (* k (rho**))))
                                                        (y (q** k))
                                                        (y+ (q** (k**))))))))

(local-defthm lemma-4-1-49
  (implies (and (integerp a) (integerp b) (< a b))
           (<= a (1- b)))
  :rule-classes ())

(local-defthm lemma-4-1-50
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**))))
           (<= (* (expt 2 (* k (rho**))) (q** k))
               (1- (* (expt 2 (* k (rho**))) (q** (k**))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint lemma-4-1-31 lemma-4-1-47 lemma-4-1-48
                        (:instance lemma-4-1-49 (a (* (expt 2 (* k (rho**))) (q** k))) (b (* (expt 2 (* k (rho**))) (q** (k**)))))))))

(local-defthm lemma-4-1-51
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**))))
           (<= (q** k)
               (- (q** (k**))
                  (expt 2 (- (* k (rho**)))))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint lemma-4-1-50
                        (:instance *-weakly-monotonic (x (expt 2 (- (* k (rho**)))))
                                                      (y (* (expt 2 (* k (rho**))) (q** k)))
                                                      (y+ (1- (* (expt 2 (* k (rho**))) (q** (k**))))))))))

(local-defthm lemma-4-1-52
  (implies (and (not (zp k))
                (>= k (k**)))
           (< (abs (- (q** k) (q** (k**))))
              1/4))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-1-41 k**-rho**-constraint))))

(local-defthm lemma-4-1-53
  (implies (and (not (zp k))
                (>= k (k**)))
           (> (q** k) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (lemma-4-1-52 lemma-4-1-b))))

(local-defthm lemma-4-1-54
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**))))
           (<= (expt (+ (q** k) (expt 2 (- (* k (rho**))))) 2)
               (* (q** (k**)) (q** (k**)))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint lemma-4-1-51 lemma-4-1-53
                        (:instance cg-sqrt-1 (x (+ (q** k) (expt 2 (- (* k (rho**))))))
                                             (y (q** (k**))))))))

(local-defthm lemma-4-1-55
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (>= (x**) (* (q0**) (q0**))))
           (<= (expt (+ (q** k) (expt 2 (- (* k (rho**))))) 2)
               (* (q0**) (q0**))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (k**-rho**-constraint lemma-4-1-46 lemma-4-1-54))))

(local-defthm lemma-4-1-56
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (>= (x**) (* (q0**) (q0**))))
           (<= (expt (+ (q** k) (expt 2 (- (* k (rho**))))) 2)
               (x**)))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint lemma-4-1-55))))

(local-defthm lemma-4-1-57
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (< (x**) (* (q0**) (q0**))))
           (= (mod (s1**) 2) 1))
  :rule-classes ()
  :hints (("Goal" :expand ((s1**))
                  :use (k**-rho**-constraint s**-constraint
                        (:instance mod-mod-2-not-equal (m (s**)))
                        (:instance mod012 (m (s**)))))))

(local-defthm lemma-4-1-58
  (implies (and (integerp a) (= (mod a 2) 1))
           (= (fl (/ a 2))
              (- (/ a 2) 1/2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-def (x a) (y 2))))))

(local-defthm lemma-4-1-59
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (< (x**) (* (q0**) (q0**))))
           (= (fl (* (expt 2 (1- (* (k**) (rho**)))) (q1**)))
                  (- (* (expt 2 (1- (* (k**) (rho**)))) (q1**))
                     1/2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (k**-rho**-constraint lemma-4-1-47 lemma-4-1-57
                        (:instance lemma-4-1-58 (a (* (expt 2 (* (k**) (rho**))) (q1**))))))))

(local-defthm lemma-4-1-60
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (< (x**) (* (q0**) (q0**))))
           (> (* (expt 2 (1- (* (k**) (rho**)))) (q** k))
              (- (* (expt 2 (1- (* (k**) (rho**)))) (q1**))
                 1/2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (k**-rho**-constraint lemma-4-1-41
                        (:instance *-strongly-monotonic (x (expt 2 (1- (* (k**) (rho**)))))
                                                        (y+ (q** k))
                                                        (y (- (q1**) (expt 2 (- (* (k**) (rho**)))))))))))

(local-defthm lemma-4-1-61
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (< (x**) (* (q0**) (q0**))))
           (> (* (expt 2 (1- (* (k**) (rho**)))) (q** k))
              (fl (* (expt 2 (1- (* (k**) (rho**)))) (q1**)))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint lemma-4-1-60 lemma-4-1-59))))

(local-defthm lemma-4-1-62
  (implies (and (not (zp k))
                (>= k (k**))
                (< (q** k) (q** (k**)))
                (< (x**) (* (q0**) (q0**))))
           (>= (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** k)))
               (fl (* (expt 2 (1- (* (k**) (rho**)))) (q1**)))))
  :rule-classes ()
  :hints (("Goal" :use (k**-rho**-constraint lemma-4-1-61))))

(defthm lemma-4-1-c
  (implies (and (not (zp k))
                (>= k (k**))
                (< (x**) (expt (+ (q** k) (expt 2 (- (* k (rho**))))) 2)))
           (= (fl (* (expt 2 (1- (* (k**) (rho**)))) (q** k)))
              (fl (* (expt 2 (1- (* (k**) (rho**)))) (q1**)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q**-rewrite-2)
                  :use (k**-rho**-constraint lemma-4-1-44 lemma-4-1-45 lemma-4-1-56 lemma-4-1-62))))

(defun cg-sqrt (x min max)
  (declare (xargs :measure (nfix (- (1+ max) min))))
  (if (and (natp min)
           (natp max)
           (<= min max))
      (if (>= (* min min) x)
          min
        (cg-sqrt x (1+ min) max))
    0))

(defun seed (l k rho)
  (1- (cg-sqrt (* (expt 2 (* k rho)) (1+ l))
               (if (= (* k rho) 1)
                   1
                 (expt 2 (- (* k rho) 2)))
               (expt 2 (* k rho)))))

(local-defthm cg-sqrt-2
  (implies (and (rationalp x)
                (not (zp min))
                (not (zp max))
                (<= min max)
                (< (* (1- min) (1- min)) x)
                (<= x (* max max)))
           (let ((y (cg-sqrt x min max)))
             (and (<= x (* y y))
                  (< (* (1- y) (1- y)) x))))
  :rule-classes ()
  :hints (("Subgoal *1/3" :use ((:instance cg-sqrt-1 (x min) (y max))))))

(defthm cg-sqrt-lemma
  (implies (and (rationalp x)
                (not (zp min))
                (not (zp max))
                (<= (* min min) x)
                (<= x (* max max)))
           (let ((y (cg-sqrt x min max)))
             (and (<= x (* y y))
                  (< (* (1- y) (1- y)) x))))
  :rule-classes ()
  :hints (("Goal" :use (cg-sqrt-2
                        (:instance cg-sqrt-1 (x min) (y max))))))

(local-defthm natp-cg
  (implies (natp min)
           (natp (cg-sqrt x min max)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable cg-sqrt))

(local-defthm lemma-4-2-1
  (IMPLIES (AND (NOT (ZP K))
                (NOT (ZP RHO)))
           (< (EXPT 2 (+ -4 (* K RHO)))
              (EXPT 2 (+ -2 (* K RHO)))))
:rule-classes ())

(local-defthm lemma-4-2-2
  (IMPLIES (AND (< l (EXPT 2 (+ -4 (* K RHO))))
                (NOT (ZP K))
                (NOT (ZP RHO))
                (INTEGERP L))
           (> (EXPT 2 (+ -2 (* K RHO))) L))
  :hints (("Goal" :use (lemma-4-2-1)
                  :in-theory (theory 'minimal-theory))))

(local-defthm lemma-4-2-3
  (IMPLIES (AND (< (+ 1 L) (EXPT 2 (+ -4 (* K RHO))))
                (NOT (ZP K))
                (NOT (ZP RHO))
                (INTEGERP L))
           (not (<= (EXPT 2 (+ -2 (* K RHO))) L)))
  :hints (("Goal" :use (lemma-4-2-2))))

(local-defthm lemma-4-2-4
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (>= (expt (1+ (seed l k rho)) 2)
               (* (expt 2 (* k rho)) (1+ l))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cg-sqrt-lemma (x (* (expt 2 (* k rho)) (1+ l)))
                                                 (min (expt 2 (- (* k rho) 2)))
                                                 (max (expt 2 (* k rho))))))))

(local-defthm lemma-4-2-5
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (< (expt (seed l k rho) 2)
              (* (expt 2 (* k rho)) (1+ l))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance cg-sqrt-lemma (x (* (expt 2 (* k rho)) (1+ l)))
                                                 (min (expt 2 (- (* k rho) 2)))
                                                 (max (expt 2 (* k rho))))))))

(local-defthm lemma-4-2-6
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (> (* (expt 2 (* k rho)) (1+ l))
              (expt 2 (- (* 2 k rho) 2))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-4
                        (:instance *-strongly-monotonic (x (expt 2 (* k rho))) (y+ (1+ l)) (y (expt 2 (- (* k rho) 2))))))))

(local-defthm lemma-4-2-7
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (> (expt (1+ (seed l k rho)) 2)
              (expt 2 (- (* 2 k rho) 2))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-4 lemma-4-2-6)
                  :in-theory (theory 'minimal-theory))))

(in-theory (disable seed))

(local-defthm lemma-4-2-8
  (implies (integerp n)
           (equal (expt 4 n)
                  (expt 2 (* 2 n)))))

(local-defthm lemma-4-2-9
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (> (1+ (seed l k rho))
              (expt 2 (1- (* k rho)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-7
                        (:instance cg-sqrt-1 (x (1+ (seed l k rho))) (y (expt 2 (1- (* k rho)))))))
          ("Goal'''" :in-theory (enable seed))))

(local (in-theory (disable lemma-4-2-8)))

(local-defthm lemma-4-2-10
  (implies (and (not (zp k))
                (not (zp rho))
                (natp l)
                (< l (expt 2 (* k rho))))
           (<= (* (expt 2 (* k rho)) (1+ l))
               (expt 2 (* 2 k rho))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x (expt 2 (* k rho))) (y (1+ l)) (y+ (expt 2 (* k rho))))))))

(local-defthm lemma-4-2-11
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (< (expt (seed l k rho) 2)
              (expt 2 (* 2 k rho))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-2-5 lemma-4-2-10))))

(local-defthm lemma-4-2-12
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (< (seed l k rho)
              (expt 2 (* k rho))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-11
                        (:instance cg-sqrt-1 (y (seed l k rho)) (x (expt 2 (* k rho))))))))

(local (encapsulate ()
 (local #!acl2
        (set-default-hints
         '((nonlinearp-default-hint stable-under-simplificationp
                                    hist pspv))))
 (defthm lemma-4-2-13
   (implies (and (rationalp a)
                 (rationalp b)
                 (rationalp c)
                 (<= 1 a)
                 (< 0 b)
                 (< 0 c)
                 (<= (expt a 2) (* b (+ c 1)))
                 (<= b (* 4 c)))
            (< (expt (- a 1) 2) (* b c))))))

(local-defthm lemma-4-2-14
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l))
           (<= (expt 2 (* k rho))
               (* 4 l)))
  :rule-classes ())

(local-defthm lemma-4-2-15
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (<= (expt (1- (seed l k rho)) 2)
               (* (expt 2 (* k rho)) l)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-5 lemma-4-2-9 lemma-4-2-14
                        (:instance lemma-4-2-13 (a (seed l k rho)) (b (expt 2 (* k rho))) (c l))))))

(local-defthm lemma-4-2-16
  (implies (and (natp l)
                (<= 1/2 l)
                (< l 2))
           (= l 1))
  :rule-classes ())

(local-defthm lemma-4-2-18
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (>= (* (expt 2 (- (* k rho))) (expt (1+ (seed l k rho)) 2))
               (1+ l)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-4
                        (:instance *-weakly-monotonic (x (expt 2 (* k rho)))
                                                      (y (1+ l))
                                                      (y+ (* (expt 2 (- (* k rho))) (expt (1+ (seed l k rho)) 2))))))))

(local-defthm lemma-4-2-19
  (implies (and (not (zp k))
                (not (zp rho))
                (>= (* k rho) 2)
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (<= (* (expt 2 (- (* k rho))) (expt (1- (seed l k rho)) 2))
               l))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-15
                        (:instance *-weakly-monotonic (x (expt 2 (* k rho)))
                                                      (y+ l)
                                                      (y (* (expt 2 (- (* k rho))) (expt (1- (seed l k rho)) 2))))))))

(defthm lemma-4-2-20
  (implies (and (not (zp k))
                (not (zp rho))
                (< (* k rho) 2))
           (and (= k 1)
                (= rho 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x k) (y 2) (y+ rho))
                        (:instance *-weakly-monotonic (x rho) (y 2) (y+ k))))))

(defthm lemma-4-2
  (implies (and (not (zp k))
                (not (zp rho))
                (natp l)
                (<= (expt 2 (- (* k rho) 2)) l)
                (< l (expt 2 (* k rho))))
           (and (integerp (seed l k rho))
                (<= (expt 2 (1- (* k rho))) (seed l k rho))
                (< (seed l k rho) (expt 2 (* k rho)))
                (<= (* (expt 2 (- (* k rho))) (expt (1- (seed l k rho)) 2))
                    l)
                (>= (* (expt 2 (- (* k rho))) (expt (1+ (seed l k rho)) 2))
                    (1+ l))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-2-9 lemma-4-2-12 lemma-4-2-18 lemma-4-2-19 lemma-4-2-16 lemma-4-2-20))))

(defund digit (i seed k rho )
  (bits seed (1- (* (- (1+ k) i) rho)) (* (- k i) rho)))

(defund root (i seed k rho)
  (if (zp i)
      0
    (+ (root (1- i) seed k rho)
       (* (expt 2 (- (* i rho)))
          (digit i seed k rho)))))

(local-defthm lemma-4-3-1
  (implies (and (not (zp k))
                (not (zp rho))
                (natp seed)
                (<= (expt 2 (- (* k rho) 2)) seed)
                (< seed (expt 2 (* k rho))))
           (= (* (expt 2 (* rho))
                 (root 1 seed k rho))
              (bits seed (1- (* k rho)) (* (- k 1) rho))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable root digit))))

(local-defthm lemma-4-3-2
  (implies (and (not (zp i))
                (not (zp rho))
                (> i 1))
           (>= (* i rho) (* 2 rho)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x rho) (y 2) (y+ i))))))

(local-defthm lemma-4-3-3
  (implies (and (not (zp i))
                (not (zp rho))
                (> i 1))
           (>= (* 2 rho) (1+ rho)))
  :rule-classes ())

(local-defthm lemma-4-3-4
  (implies (and (not (zp i))
                (not (zp rho))
                (> i 1))
           (>= (* i rho) (1+ rho)))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (lemma-4-3-2 lemma-4-3-3))))

(local-defthm lemma-4-3-5
  (implies (and (not (zp k))
                (not (zp rho))
                (natp seed)
                (<= (expt 2 (- (* k rho) 2)) seed)
                (< seed (expt 2 (* k rho)))
                (not (zp i))
                (> i 1)
                (<= i k)
                (= (* (expt 2 (* (1- i) rho))
                      (root (1- i) seed k rho))
                   (bits seed (1- (* k rho)) (* (- k (1- i)) rho))))
           (= (* (expt 2 (* i rho))
                 (root i seed k rho))
              (bits seed (1- (* k rho)) (* (- k i) rho))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable root digit)
                  :use (lemma-4-3-4
                        (:instance bits-plus-bits (x seed)
                                                  (n (1- (* k rho)))
                                                  (m (* (- k i) rho))
                                                  (p (* (- k (1- i)) rho)))))))

(local-defthm lemma-4-3-6
  (implies (and (not (zp k))
                (not (zp rho))
                (natp seed)
                (<= (expt 2 (- (* k rho) 2)) seed)
                (< seed (expt 2 (* k rho)))
                (not (zp i))
                (<= i k))
           (= (* (expt 2 (* i rho))
                 (root i seed k rho))
              (bits seed (1- (* k rho)) (* (- k i) rho))))
  :rule-classes ()
  :hints (("Goal" :induct (natp-induct i))
          ("Subgoal *1/" :use (lemma-4-3-5 lemma-4-3-1))))

(local-defthm lemma-4-3-7
  (implies (and (not (zp k))
                (not (zp rho))
                (natp seed)
                (<= (expt 2 (- (* k rho) 2)) seed)
                (< seed (expt 2 (* k rho))))
           (= (* (expt 2 (* k rho))
                 (root k seed k rho))
              seed))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance lemma-4-3-6 (i k))
                        (:instance bits-tail (x seed) (i (1- (expt 2 (* k rho)))))))))

(defthm lemma-4-3
  (implies (and (not (zp k))
                (not (zp rho))
                (natp seed)
                (<= (expt 2 (- (* k rho) 2)) seed)
                (< seed (expt 2 (* k rho))))
           (= (root k seed k rho)
              (* (expt 2 (- (* k rho))) seed)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-4-3-7))))
