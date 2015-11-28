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

(include-book "division")


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


;;**********************************************************************************

(encapsulate (((rho$$) => *) ((x$$) => *) ((h$$ *) => *))
  (local (defun rho$$ () 1))
  (local (defun x$$ () 0))
  (local (defun h$$ (k) (declare (ignore k)) 0))
  (defthm rho$$-constraint
    (integerp (rho$$))
    :rule-classes (:rewrite :type-prescription))
  (defthm x$$-constraint
    (rationalp (x$$))
    :rule-classes (:rewrite :type-prescription))
  (defthm integerp-h$$
    (implies (not (zp k))
             (integerp (h$$ k)))
    :rule-classes (:rewrite :type-prescription)))

(defund q$$ (k)
  (if (zp k)
      0
    (+ (q$$ (1- k))
       (/ (h$$ k) (expt 2 (* k (rho$$)))))))

(defund p$$ (k)
  (if (zp k)
      (x$$)
    (- (* (expt 2 (rho$$)) (p$$ (1- k)))
       (* (h$$ k)
          (+ (* 2 (q$$ (1- k)))
             (/ (h$$ k) (expt 2 (* k (rho$$)))))))))

(local-defthm lemma-3-1-1
  (implies (not (zp k))
           (= (* (expt 2 (* k (rho$$)))
                 (- (x$$) (* (q$$ k) (q$$ k))))
              (- (* (expt 2 (* k (rho$$)))
                    (- (x$$) (* (q$$ (1- k)) (q$$ (1- k)))))
                 (* (h$$ k) (+ (* 2 (q$$ (1- k))) (/ (h$$ k) (expt 2 (* k (rho$$)))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable q$$))))

(local-defthm lemma-3-1-2
  (implies (and (not (zp k))
                (= (p$$ (1- k))
                   (* (expt 2 (* (1- k) (rho$$)))
                      (- (x$$) (* (q$$ (1- k)) (q$$ (1- k)))))))
           (= (* (expt 2 (* k (rho$$)))
                 (- (x$$) (* (q$$ (1- k)) (q$$ (1- k)))))
              (* (expt 2 (rho$$))
                 (p$$ (1- k)))))
  :rule-classes ())

(local-defthm lemma-3-1-3
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d)
                (= a (- b c))
                (= b d))
           (= a (- d c)))
:rule-classes ())

(local-defthm lemma-3-1-4
  (implies (and (not (zp k))
                (= (p$$ (1- k))
                   (* (expt 2 (* (1- k) (rho$$)))
                      (- (x$$) (* (q$$ (1- k)) (q$$ (1- k)))))))
           (= (* (expt 2 (* k (rho$$)))
                 (- (x$$) (* (q$$ k) (q$$ k))))
              (- (* (expt 2 (rho$$))
                    (p$$ (1- k)))
                 (* (h$$ k) (+ (* 2 (q$$ (1- k))) (/ (h$$ k) (expt 2 (* k (rho$$)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-1-1
                 lemma-3-1-2
                 (:instance lemma-3-1-3 (a (* (expt 2 (* k (rho$$))) (- (x$$) (* (q$$ k) (q$$ k)))))
                            (b (* (expt 2 (* k (rho$$))) (- (x$$) (* (q$$ (1- k)) (q$$ (1- k))))))
                            (c (* (h$$ k) (+ (* 2 (q$$ (1- k))) (/ (h$$ k) (expt 2 (* k (rho$$)))))))
                            (d (* (expt 2 (rho$$)) (p$$ (1- k)))))))))

(local-defthm lemma-3-1-5
  (implies (and (not (zp k))
                (= (p$$ (1- k))
                   (* (expt 2 (* (1- k) (rho$$)))
                      (- (x$$) (* (q$$ (1- k)) (q$$ (1- k)))))))
           (= (p$$ k)
              (* (expt 2 (* k (rho$$)))
                 (- (x$$) (* (q$$ k) (q$$ k))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-1-4)
                  :in-theory (e/d (q$$ p$$)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4)
                                  ))))

(local-defthm lemma-3-1-6
  (implies (zp k)
           (= (p$$ k)
              (- (x$$) (* (q$$ k) (q$$ k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p$$ q$$))))

(defthmd lemma-3-1
  (implies (natp k)
           (equal (p$$ k)
                  (* (expt 2 (* k (rho$$)))
                     (- (x$$) (* (q$$ k) (q$$ k))))))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/2" :use lemma-3-1-5)
          ("Subgoal *1/1" :use lemma-3-1-6)))

;;**********************************************************************************

(defthm *-weakly-monotonic
  (implies (and (rationalp y)
                (rationalp y+)
                (rationalp x)
                (> x 0))
           (iff (<= y y+)
                (<= (* x y) (* x y+))))
  :rule-classes ())

(defthm *-strongly-monotonic
  (implies (and (rationalp y)
                (rationalp y+)
                (rationalp x)
                (> x 0))
           (iff (< y y+)
                (< (* x y) (* x y+))))
  :rule-classes ())

(defthm *-weakly-monotonic-neg
  (implies (and (rationalp y)
                (rationalp y+)
                (rationalp x)
                (< x 0))
           (iff (<= y y+)
                (>= (* x y) (* x y+))))
  :rule-classes ())

(defthm *-strongly-monotonic-neg
  (implies (and (rationalp y)
                (rationalp y+)
                (rationalp x)
                (< x 0))
           (iff (< y y+)
                (> (* x y) (* x y+))))
  :rule-classes ())

(local-defthm lemma-3-2-1
  (implies (not (zp k))
           (iff (<= (* (- (q$$ k) (expt 2 (- (* k (rho$$))))) (- (q$$ k) (expt 2 (- (* k (rho$$))))))
                    (x$$))
                (<= (+ (* (q$$ k) (q$$ k)) (- (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k))) (expt 2 (- (* 2 k (rho$$)))))
                    (x$$))))
  :rule-classes ())

(local-defthm lemma-3-2-2
  (implies (not (zp k))
           (iff (<= (+ (* (q$$ k) (q$$ k)) (- (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k))) (expt 2 (- (* 2 k (rho$$)))))
                    (x$$))
                (<= (- (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                    (* (expt 2 (* k (rho$$))) (- (x$$) (* (q$$ k) (q$$ k)))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use ((:instance *-weakly-monotonic
                                   (x (expt 2 (* k (rho$$))))
                                   (y (+ (* (q$$ k) (q$$ k)) (- (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k))) (expt 2 (- (* 2 k (rho$$))))))
                                   (y+ (x$$)))))))

(local-defthm lemma-3-2-3
  (implies (not (zp k))
           (iff (<= (+ (* (q$$ k) (q$$ k)) (- (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k))) (expt 2 (- (* 2 k (rho$$)))))
                    (x$$))
                (<= (- (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                    (p$$ k))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-2-2)
                  :in-theory (enable lemma-3-1))))

(local-defthm lemma-3-2-4
  (implies (not (zp k))
           (iff (<= (* (- (q$$ k) (expt 2 (- (* k (rho$$))))) (- (q$$ k) (expt 2 (- (* k (rho$$))))))
                    (x$$))
                (<= (- (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                    (p$$ k))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-2-1 lemma-3-2-3))))

(local-defthm lemma-3-2-5
  (implies (not (zp k))
           (iff (> (* (+ (q$$ k) (expt 2 (- (* k (rho$$))))) (+ (q$$ k) (expt 2 (- (* k (rho$$))))))
                   (x$$))
                (> (+ (* (q$$ k) (q$$ k)) (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k)) (expt 2 (- (* 2 k (rho$$)))))
                   (x$$))))
  :rule-classes ())

(local-defthm lemma-3-2-6
  (implies (not (zp k))
           (iff (> (+ (* (q$$ k) (q$$ k)) (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k)) (expt 2 (- (* 2 k (rho$$)))))
                   (x$$))
                (> (+ (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                   (* (expt 2 (* k (rho$$))) (- (x$$) (* (q$$ k) (q$$ k)))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use ((:instance *-strongly-monotonic
                            (x (expt 2 (* k (rho$$))))
                            (y+ (+ (* (q$$ k) (q$$ k)) (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k)) (expt 2 (- (* 2 k (rho$$))))))
                            (y (x$$)))))))

(local-defthm lemma-3-2-7
  (implies (not (zp k))
           (iff (> (+ (* (q$$ k) (q$$ k)) (* (expt 2 (- 1 (* k (rho$$)))) (q$$ k)) (expt 2 (- (* 2 k (rho$$)))))
                   (x$$))
                (> (+ (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                   (p$$ k))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-2-6)
                  :in-theory (enable lemma-3-1))))

(local-defthm lemma-3-2-8
  (implies (not (zp k))
           (iff (> (* (+ (q$$ k) (expt 2 (- (* k (rho$$))))) (+ (q$$ k) (expt 2 (- (* k (rho$$))))))
                   (x$$))
                (> (+ (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                   (p$$ k))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-2-5 lemma-3-2-7))))

(defthm lemma-3-2-a-b
  (implies (not (zp k))
           (iff (and (<= (* (- (q$$ k) (expt 2 (- (* k (rho$$))))) (- (q$$ k) (expt 2 (- (* k (rho$$))))))
                         (x$$))
                     (< (x$$)
                        (* (+ (q$$ k) (expt 2 (- (* k (rho$$))))) (+ (q$$ k) (expt 2 (- (* k (rho$$))))))))
                (and (<= (- (* 2 (q$$ k)))
                         (- (p$$ k) (expt 2 (- (* k (rho$$))))))
                     (< (- (p$$ k) (expt 2 (- (* k (rho$$)))))
                        (* 2 (q$$ k))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-2-4 lemma-3-2-8))))

(local-defthm lemma-3-2-9
  (implies (not (zp k))
           (iff (> (+ (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                   (p$$ k))
                (< (* (expt 2 (rho$$)) (p$$ (1- k)))
                   (* (1+ (h$$ k))
                      (+ (* 2 (q$$ (1- k)))
                         (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$))))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p$$ q$$))))

(local-defthm lemma-3-2-10
  (implies (not (zp k))
           (iff (< (* (expt 2 (rho$$)) (p$$ (1- k)))
                   (* (1+ (h$$ k))
                      (+ (* 2 (q$$ (1- k)))
                         (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$))))))))
                (< (p$$ (1- k))
                   (* (expt 2 (- (rho$$)))
                      (1+ (h$$ k))
                      (+ (* 2 (q$$ (1- k)))
                         (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use ((:instance *-strongly-monotonic
                            (x (expt 2 (- (rho$$))))
                            (y (* (expt 2 (rho$$)) (p$$ (1- k))))
                            (y+ (* (1+ (h$$ k))
                                   (+ (* 2 (q$$ (1- k)))
                                      (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$)))))))))))))

(local-defthm lemma-3-2-11
  (implies (not (zp k))
           (iff (> (+ (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                   (p$$ k))
                (< (p$$ (1- k))
                   (* (expt 2 (- (rho$$)))
                      (1+ (h$$ k))
                      (+ (* 2 (q$$ (1- k)))
                         (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$))))))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-2-9 lemma-3-2-10))))

(local-defthm lemma-3-2-12
  (implies (not (zp k))
           (iff (<= (- (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                    (p$$ k))
                (>= (* (expt 2 (rho$$)) (p$$ (1- k)))
                    (* (1- (h$$ k))
                       (+ (* 2 (q$$ (1- k)))
                          (* (1- (h$$ k)) (expt 2 (- (* k (rho$$))))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p$$ q$$))))

(local-defthm lemma-3-2-13
  (implies (not (zp k))
           (iff (>= (* (expt 2 (rho$$)) (p$$ (1- k)))
                    (* (1- (h$$ k))
                       (+ (* 2 (q$$ (1- k)))
                          (* (1- (h$$ k)) (expt 2 (- (* k (rho$$))))))))
                (>= (p$$ (1- k))
                    (* (expt 2 (- (rho$$)))
                       (1- (h$$ k))
                       (+ (* 2 (q$$ (1- k)))
                          (* (1- (h$$ k)) (expt 2 (- (* k (rho$$))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use ((:instance *-weakly-monotonic
                            (x (expt 2 (- (rho$$))))
                            (y+ (* (expt 2 (rho$$)) (p$$ (1- k))))
                            (y (* (1- (h$$ k))
                                  (+ (* 2 (q$$ (1- k)))
                                     (* (1- (h$$ k)) (expt 2 (- (* k (rho$$)))))))))))))

(local-defthm lemma-3-2-14
  (implies (not (zp k))
           (iff (<= (- (expt 2 (- (* k (rho$$)))) (* 2 (q$$ k)))
                    (p$$ k))
                (>= (p$$ (1- k))
                    (* (expt 2 (- (rho$$)))
                       (1- (h$$ k))
                       (+ (* 2 (q$$ (1- k)))
                          (* (1- (h$$ k)) (expt 2 (- (* k (rho$$))))))))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-2-12 lemma-3-2-13))))

(defthm lemma-3-2-b-c
  (implies (not (zp k))
           (iff (and (<= (- (* 2 (q$$ k)))
                         (- (p$$ k) (expt 2 (- (* k (rho$$))))))
                     (< (- (p$$ k) (expt 2 (- (* k (rho$$)))))
                        (* 2 (q$$ k))))
                (and (<= (* (expt 2 (- (rho$$)))
                            (1- (h$$ k))
                            (+ (* 2 (q$$ (1- k)))
                               (* (1- (h$$ k)) (expt 2 (- (* k (rho$$)))))))
                         (p$$ (1- k)))
                     (< (p$$ (1- k))
                        (* (expt 2 (- (rho$$)))
                           (1+ (h$$ k))
                           (+ (* 2 (q$$ (1- k)))
                              (* (1+ (h$$ k)) (expt 2 (- (* k (rho$$)))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-2-11 lemma-3-2-14))))

;;**********************************************************************************

(local-defthm lemma-3-3-1
  (implies (and (not (zp (rho$$)))
                (integerp n))
           (integerp (* (expt 2 (rho$$)) n)))
  :rule-classes())

(local-defthm lemma-3-3-2
  (implies (and (not (zp k))
                (not (zp (rho$$)))
                (integerp (* (expt 2 (* (1- k) (rho$$))) (q$$ (1- k)))))
           (integerp (* (expt 2 (* k (rho$$))) (q$$ k))))
  :rule-classes()
  :hints (("Goal" :in-theory (enable q$$)
                  :use (:instance lemma-3-3-1 (n (* (expt 2 (* (1- k) (rho$$))) (q$$ (1- k))))))))

(local-defthm lemma-3-3-3
  (implies (and (natp k)
                (not (zp (rho$$))))
           (integerp (* (expt 2 (* k (rho$$))) (q$$ k))))
  :rule-classes()
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/2" :use lemma-3-3-2)
          ("Subgoal *1/1" :in-theory (enable q$$))))

(local-defthm lemma-3-3-4
  (implies (and (rationalp x)
                (not (zp m))
                (integerp (* x m))
                (< x 1))
           (< (* x m) m))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-strongly-monotonic (x m) (y x) (y+ 1)))))

(local-defthm lemma-3-3-5
  (implies (and (integerp n)
                (integerp m)
                (< n m))
           (<= n (1- m)))
  :rule-classes ())

(local-defthm lemma-3-3-6
  (implies (and (rationalp x)
                (not (zp m))
                (integerp (* x m))
                (< x 1))
           (<= (* x m) (1- m)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-3-4
                        (:instance lemma-3-3-5 (n (* x m)))))))

(local-defthm lemma-3-3-7
  (implies (and (rationalp x)
                (not (zp m))
                (integerp (* x m))
                (< x 1))
           (<= x (- 1 (/ m))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-3-6
                        (:instance *-weakly-monotonic (x m) (y x) (y+ (- 1 (/ m))))))))

(local-defthm lemma-3-3-8
  (implies (and (natp k)
                (not (zp (rho$$)))
                (< (q$$ k) 1))
           (<= (q$$ k) (- 1 (expt 2 (- (* k (rho$$)))))))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-3
                        (:instance lemma-3-3-7 (x (q$$ k)) (m (expt 2 (* k (rho$$)))))))))

(local-defthm lemma-3-3-9
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (<= (- (* 2 (q$$ (1- k))))
                    (- (p$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))))
                (< (- (p$$ (1- k)) (expt 2 (- (* (1- k) (rho$$)))))
                   (* 2 (q$$ (1- k)))))
           (< (abs (p$$ (1- k))) 2))
  :rule-classes()
  :hints (("Goal" :use ((:instance lemma-3-3-8 (k (1- k)))))))

(defthm lemma-3-3-a
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (<= (* (- (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))) (- (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))))
                    (x$$))
                (< (x$$)
                   (* (+ (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))) (+ (q$$ (1- k)) (expt 2 (- (* (1- k) (rho$$))))))))
           (< (abs (p$$ (1- k))) 2))
  :rule-classes()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               acl2::zp-open)
           :use (lemma-3-3-9
                 (:instance lemma-3-2-a-b (k (1- k)))))))

(local-defthm lemma-3-3-10
  (implies (and (not (zp k))
                (< (h$$ k) (expt 2 (rho$$))))
           (< (* (expt 2 (- (* k (rho$$)))) (h$$ k))
              (expt 2 (* (- 1 k) (rho$$)))))
  :rule-classes()
  :hints (("Goal" :use ((:instance *-strongly-monotonic (x (expt 2 (- (* k (rho$$))))) (y (h$$ k)) (y+ (expt 2 (rho$$))))))))

(local-defthm lemma-3-3-11
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (< (h$$ k) (expt 2 (rho$$))))
           (<= (q$$ k) (+ 1 (- (expt 2 (* (- 1 k) (rho$$)))) (* (h$$ k) (expt 2 (- (* k (rho$$))))))))
  :rule-classes()
  :hints (("Goal" :in-theory (enable q$$)
                  :use ((:instance lemma-3-3-8 (k (1- k)))))))

(local-defthm lemma-3-3-12
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (<= x (+ 1 (- y) z))
                (< z y))
           (< x 1))
:rule-classes ())

(local-defthm lemma-3-3-13
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (< (h$$ k) (expt 2 (rho$$))))
           (< (q$$ k) 1))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-10
                        lemma-3-3-11
                        (:instance lemma-3-3-12 (x (q$$ k)) (y (expt 2 (* (- 1 k) (rho$$)))) (z (* (h$$ k) (expt 2 (- (* k (rho$$)))))))))))

(local-defthm lemma-3-3-14
  (implies (and (rationalp x)
                (not (zp m))
                (integerp (* x (* 2 m)))
                (< x 1/2))
           (< (* 2 x m) m))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-strongly-monotonic (x m) (y x) (y+ 1/2)))))

(local-defthm lemma-3-3-16
  (implies (and (rationalp x)
                (not (zp m))
                (integerp (* 2 x m))
                (< x 1/2))
           (<= (* 2 x m) (1- m)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-3-14
                        (:instance lemma-3-3-5 (n (* 2 x m)))))))

(local-defthm lemma-3-3-17
  (implies (and (rationalp x)
                (not (zp m))
                (integerp (* 2 x m))
                (< x 1/2))
           (<= x (- 1/2 (/ (* 2 m)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-3-16
                        (:instance *-weakly-monotonic (x (* 2 m)) (y x) (y+ (- 1/2 (/ (* 2 m)))))))))

(local-defthm lemma-3-3-18
  (implies (and (not (zp k))
                (not (zp (rho$$)))
                (< (q$$ k) 1/2))
           (<= (q$$ k) (- 1/2 (expt 2 (- (* k (rho$$)))))))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-3
                        (:instance lemma-3-3-17 (x (q$$ k)) (m (expt 2 (1- (* k (rho$$))))))))))

(local-defthm lemma-3-3-19
  (implies (and (not (zp k))
                (> (h$$ k) (- (expt 2 (rho$$)))))
           (> (* (expt 2 (- (* k (rho$$)))) (h$$ k))
              (- (expt 2 (* (- 1 k) (rho$$))))))
  :rule-classes()
  :hints (("Goal" :use ((:instance *-strongly-monotonic (x (expt 2 (- (* k (rho$$))))) (y+ (h$$ k)) (y (- (expt 2 (rho$$)))))))))

(local-defthm lemma-3-3-20
  (implies (and (integerp a)
                (integerp b)
                (<= a b))
           (<= (expt 2 a) (expt 2 b)))
  :rule-classes ())

(local-defthm lemma-3-3-21
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1))
           (>= (- (expt 2 (* (- 1 k) (rho$$))))
               -1/2))
  :rule-classes()
  :hints (("Goal" :use (:instance lemma-3-3-20 (a (* (- 1 k) (rho$$))) (b -1)))))

(local-defthm lemma-3-3-22
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (> a b)
                (>= b c))
           (> a c))
  :rule-classes ())

(local-defthm lemma-3-3-23
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (> (h$$ k) (- (expt 2 (rho$$)))))
           (> (* (expt 2 (- (* k (rho$$)))) (h$$ k))
              -1/2))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-19
                        lemma-3-3-21
                        (:instance lemma-3-3-22 (a (* (expt 2 (- (* k (rho$$)))) (h$$ k)))
                                                (b (- (expt 2 (* (- 1 k) (rho$$)))))
                                                (c -1/2))))))

(local-defthm lemma-3-3-24
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (> (h$$ k) (- (expt 2 (rho$$)))))
           (> (q$$ k) 0))
  :rule-classes()
  :hints (("Goal" :in-theory (enable q$$)
                  :use (lemma-3-3-23))))

(local-defthm lemma-3-3-25
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ k) 1/2)
                (> (h$$ k) (- (expt 2 (rho$$)))))
           (and (< 0  (+ (q$$ k) (expt 2 (- (* k (rho$$))))))
                (<= (+ (q$$ k) (expt 2 (- (* k (rho$$))))) 1/2)))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-18 lemma-3-3-24))))

(local-defthm lemma-3-3-26
  (implies (and (rationalp x)
                (rationalp y)
                (<= 0 x)
                (<= x y))
           (<= (* x x) (* y y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (y x) (y+ y))
                        (:instance *-weakly-monotonic (x y) (y x) (y+ y))))))

(local-defthm lemma-3-3-27
  (implies (and (not (zp (rho$$)))
                (natp k)
                (> k 1)
                (> x 1/4)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ k) 1/2)
                (> (h$$ k) (- (expt 2 (rho$$)))))
              (< (* (+ (q$$ k) (expt 2 (- (* k (rho$$)))))
                    (+ (q$$ k) (expt 2 (- (* k (rho$$))))))
                 x))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-25
                        (:instance lemma-3-3-26 (x (+ (q$$ k) (expt 2 (- (* k (rho$$))))))
                                                (y 1/2))))))

(defthm lemma-3-3-b
  (implies (and (not (zp (rho$$)))
                (> (x$$) 1/4)
                (natp k)
                (> k 1)
                (<= 1/2 (q$$ (1- k)))
                (< (q$$ (1- k)) 1)
                (< (h$$ k) (expt 2 (rho$$)))
                (> (h$$ k) (- (expt 2 (rho$$))))
                (<= (x$$) (* (+ (q$$ k) (expt 2 (- (* k (rho$$)))))
                             (+ (q$$ k) (expt 2 (- (* k (rho$$))))))))
           (and (<= 1/2 (q$$ k))
                (< (q$$ k) 1)))
  :rule-classes()
  :hints (("Goal" :use (lemma-3-3-13
                        (:instance lemma-3-3-27 (x (x$$)))))))

;;**********************************************************************************

(defund sqrt-accessible-p (i j k rho m n)
  (and (< (- (expt 2 (* (- 1 k) rho)) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
          (pi0 i m))
       (< (pi0 i m)
          (+ (delta0 j n) (/ (expt 2 n)) (expt 2 (* (- 1 k) rho))))))

(defund check-upper-bound (entry i j k rho m n)
  (or (= entry (1- (expt 2 rho)))
      (<= (+ (pi0 i m) (expt 2 (- 3 m)))
          (if (or (< i (expt 2 (1- m)))
                  (= i (1- (expt 2 m))))
              (* (/ (1+ entry) (expt 2 rho))
                 (+ (delta0 j n) (* (1+ entry) (expt 2 (- (* k rho))))))
            (* (/ (1+ entry) (expt 2 rho))
               (+ (delta0 j n) (expt 2 (- n)) (* (1+ entry) (expt 2 (- (* k rho))))))))))

(defund check-lower-bound (entry i j k rho m n)
  (or (= entry (- 1 (expt 2 rho)))
      (>= (pi0 i m)
          (if (< i (expt 2 (1- m)))
              (* (/ (1- entry) (expt 2 rho))
                 (+ (delta0 j n) (expt 2 (- n)) (* (1- entry) (expt 2 (- (* k rho))))))
            (* (/ (1- entry) (expt 2 rho))
               (+ (delta0 j n) (* (1- entry) (expt 2 (- (* k rho))))))))))

(defund check-sqrt-entry (i j k rho m n entry)
  (or (not (sqrt-accessible-p i j k rho m n))
      (and (< (- (expt 2 rho)) entry)
           (< entry (expt 2 rho))
           (check-upper-bound entry i j k rho m n)
           (check-lower-bound entry i j k rho m n))))

(defund check-sqrt-row (i j k rho m n row)
  (if (zp j)
      t
    (and (check-sqrt-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
         (check-sqrt-row i (1- j) k rho m n row))))

(defund check-sqrt-rows (i k rho m n rows)
  (if (zp i)
      t
    (and (check-sqrt-row (1- i) (expt 2 n) k rho m n (nth (1- i) rows))
         (check-sqrt-rows (1- i) k rho m n rows))))

(defund admissible-for-iteration-p (k rho m n table)
  (check-sqrt-rows (expt 2 m) k rho m n table))

(local-defthm check-sqrt-row-lemma
  (implies (and (natp j)
                (natp jj)
                (< jj j)
                (check-sqrt-row i j k rho m n row))
           (check-sqrt-entry i jj k rho m n (ifix (nth jj row))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-row))))

(local-defthm check-sqrt-rows-lemma
  (implies (and (natp i)
                (natp ii)
                (< ii i)
                (check-sqrt-rows i k rho m n rows))
           (check-sqrt-row ii (expt 2 n) k rho m n (nth ii rows)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-rows))))

(local-defthm check-sqrt-table-lemma
  (implies (and (natp m)
                (natp n)
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (admissible-for-iteration-p k rho m n table))
           (check-sqrt-entry i j k rho m n (lookup i j table)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lookup admissible-for-iteration-p)
                  :use ((:instance check-sqrt-rows-lemma (rows table) (ii i) (i (expt 2 m)))
                        (:instance check-sqrt-row-lemma (row (nth i table)) (jj j) (j (expt 2 n)))))))

(local-defthm sqrt-table-1
  (implies (and (natp k)
                (natp rho)
                (natp m)
                (natp n)
                (rationalp d)
                (rationalp p)
                (<= (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                (natp j)
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3))))))
           (sqrt-accessible-p i j k rho m n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sqrt-accessible-p))))

(local-defthm sqrt-table-2
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
           (and (integerp h)
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-entry)
                  :use (check-sqrt-table-lemma sqrt-table-1))))

(local-defthm sqrt-table-3
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
           (or (= h (1- (expt 2 rho)))
               (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                   (if (or (< i (expt 2 (1- m)))
                           (= i (1- (expt 2 m))))
                       (* (/ (1+ h) (expt 2 rho))
                          (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))
                     (* (/ (1+ h) (expt 2 rho))
                        (+ (delta0 j n) (expt 2 (- n)) (* (1+ h) (expt 2 (- (* k rho))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-sqrt-entry check-upper-bound)
                           (;jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            ))
           :use (check-sqrt-table-lemma sqrt-table-1))))

(local-defthm sqrt-table-4
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
           (or (= h (- 1 (expt 2 rho)))
               (>= (pi0 i m)
                   (if (< i (expt 2 (1- m)))
                       (* (/ (1- h) (expt 2 rho))
                          (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho))))))
                     (* (/ (1- h) (expt 2 rho))
                        (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (check-sqrt-entry check-lower-bound)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
                  :use (check-sqrt-table-lemma sqrt-table-1))))

(local-defthm sqrt-table-5
  (implies (and (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (= h (1- (expt 2 rho))))
           (< p (* (/ (1+ h) (expt 2 rho))
                   (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ())

(local-defthm sqrt-table-6
  (implies (and (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (= h (- 1 (expt 2 rho))))
           (>= p (* (/ (1- h) (expt 2 rho))
                    (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ())

(local-defthm sqrt-table-7
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (rationalp (delta0 j n))
                (rationalp (pi0 i m))
                (>= (delta0 j n) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0 pi0))))

(local-defthm sqrt-table-8
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (integerp h)
                (>= (1+ h) 0))
          (<= (* (/ (1+ h) (expt 2 rho))
                 (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))
              (* (/ (1+ h) (expt 2 rho))
                 (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 (:instance *-weakly-monotonic (x (/ (1+ h) (expt 2 rho))) (y (delta0 j n)) (y+ d))))))

(local-defthm sqrt-table-9
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (rationalp w)
                (< x y)
                (<= y z)
                (<= z w))
           (< x w))
  :rule-classes ())

(local-defthm sqrt-table-10
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (natp i)
                (< i (expt 2 m))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                    (* (/ (1+ h) (expt 2 rho))
                       (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))))
                (>= (1+ h) 0))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 sqrt-table-8
                 (:instance sqrt-table-9 (x p)
                            (y (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                            (z (* (/ (1+ h) (expt 2 rho))
                                  (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))))
                            (w (* (/ (1+ h) (expt 2 rho))
                                  (+ d (* (1+ h) (expt 2 (- (* k rho))))))))))))

(local-defthm sqrt-table-11
  (implies (and (natp m)
                (natp i)
                (< i (expt 2 m))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m)))))
          (> (+ (pi0 i m) (expt 2 (- 3 m))) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0))))

(local-defthm sqrt-table-12
  (implies (and (natp k)
                (natp rho)
                (integerp h)
                (> h (- (expt 2 rho))))
           (> (* (1+ h) (expt 2 (- (* k rho))))
              (- (expt 2 (* (- 1 k) rho)))))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-strongly-monotonic (x (expt 2 (- (* k rho)))) (y (- (expt 2 rho))) (y+ (1+ h))))))

(local-defthm sqrt-table-13
  (implies (and (not (zp k))
                (natp rho))
           (>= (- (expt 2 (* (- 1 k) rho)))
               -1))
  :rule-classes ())

(local-defthm sqrt-table-14
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (> x y)
                (>= y z))
           (> x z))
  :rule-classes ())

(local-defthm sqrt-table-15
  (implies (and (not (zp k))
                (natp rho)
                (integerp h)
                (> h (- (expt 2 rho))))
           (> (* (1+ h) (expt 2 (- (* k rho))))
              -1))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-12
                        sqrt-table-13
                        (:instance sqrt-table-14 (x (* (1+ h) (expt 2 (- (* k rho))))) (y (- (expt 2 (* (- 1 k) rho)))) (z -1))))))

(local-defthm sqrt-table-16
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (not (zp k))
                (integerp h)
                (> h (- (expt 2 rho))))
           (> (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))
              0))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-7
                        sqrt-table-15))))

(local-defthm sqrt-table-17
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (not (zp k))
                (integerp h)
                (< (1+ h) 0)
                (> h (- (expt 2 rho))))
           (< (* (/ (1+ h) (expt 2 rho))
                 (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))
              0))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-16
                 sqrt-table-7
                 (:instance *-strongly-monotonic-neg (x (/ (1+ h) (expt 2 rho)))
                            (y 0)
                            (y+ (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))))))))

(local-defthm sqrt-table-18
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (natp i)
                (< i (expt 2 m))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m))))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (> h (- (expt 2 rho)))
                (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                    (* (/ (1+ h) (expt 2 rho))
                       (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))))
           (>= (1+ h) 0))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-17
                 sqrt-table-11))))

(local-defthm sqrt-table-19
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (natp i)
                (< i (expt 2 m))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m))))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (> h (- (expt 2 rho)))
                (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                    (* (/ (1+ h) (expt 2 rho))
                       (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-10
                 sqrt-table-18))))

(local-defthm sqrt-table-20
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m))))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               acl2::|(* x (+ y z))|
                               acl2::not-integerp-1a-expt
                               acl2::not-integerp-2a-expt
                               acl2::not-integerp-3a-expt
                               acl2::not-integerp-4a-expt
                               acl2::default-less-than-2
                               )
           :use (sqrt-table-19 sqrt-table-2 sqrt-table-3 sqrt-table-5))))

(local-defthm sqrt-table-21
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (integerp h)
                (<= (1+ h) 0))
          (<= (* (/ (1+ h) (expt 2 rho))
                 (+ (delta0 j n) (expt 2 (- n)) (* (1+ h) (expt 2 (- (* k rho))))))
              (* (/ (1+ h) (expt 2 rho))
                 (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 (:instance *-weakly-monotonic-neg (x (/ (1+ h) (expt 2 rho))) (y+ (+ (delta0 j n) (expt 2 (- n)))) (y d))))))

(local-defthm sqrt-table-22
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                    (* (/ (1+ h) (expt 2 rho))
                       (+ (delta0 j n) (expt 2 (- n)) (* (1+ h) (expt 2 (- (* k rho)))))))
                (<= (1+ h) 0))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 sqrt-table-21
                 (:instance sqrt-table-9 (x p)
                            (y (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                            (z (* (/ (1+ h) (expt 2 rho))
                                  (+ (delta0 j n) (expt 2 (- n)) (* (1+ h) (expt 2 (- (* k rho)))))))
                            (w (* (/ (1+ h) (expt 2 rho))
                                  (+ d (* (1+ h) (expt 2 (- (* k rho))))))))))))

(local-defthm sqrt-table-23
  (implies (and (natp m)
                (natp i)
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
           (and (rationalp (pi0 i m))
                (<= (+ (pi0 i m) 4)
                    (* (/ (expt 2 (- m 2))) (- (expt 2 m) 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0)
                  :use ((:instance *-weakly-monotonic (x (/ (expt 2 (- m 2)))) (y i) (y+ (- (expt 2 m) 2)))))))

(local-defthm sqrt-table-24
  (implies (and (natp m)
                (natp i)
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
           (= (* (/ (expt 2 (- m 2))) (- (expt 2 m) 2))
              (- 4 (expt 2 (- 3 m)))))
  :rule-classes ())

(local-defthm sqrt-table-25
  (implies (and (natp m)
                (natp i)
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m))))
           (and (rationalp (pi0 i m))
                (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                    0)))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-23 sqrt-table-24))))

(local-defthm sqrt-table-26
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (not (zp k))
                (integerp h)
                (>= (1+ h) 0)
                (> h (- (expt 2 rho))))
           (>= (* (/ (1+ h) (expt 2 rho))
                  (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))
               0))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-16
                        sqrt-table-7
                        (:instance *-weakly-monotonic (x (/ (1+ h) (expt 2 rho)))
                                                      (y 0)
                                                      (y+ (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))))))))

(local-defthm sqrt-table-27
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m)))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (>= (1+ h) 0)
                (> h (- (expt 2 rho))))
           (<= (+ (pi0 i m) (expt 2 (- 3 m)))
               (* (/ (1+ h) (expt 2 rho))
                  (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-26
                 sqrt-table-25))))

(local-defthm sqrt-table-28
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m)))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (>= (1+ h) 0)
                (> h (- (expt 2 rho))))
           (<= (* (/ (1+ h) (expt 2 rho))
                  (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))
               (* (/ (1+ h) (expt 2 rho))
                  (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 (:instance *-weakly-monotonic (x (/ (1+ h) (expt 2 rho))) (y (delta0 j n)) (y+ d))))))

(local-defthm sqrt-table-29
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m)))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (integerp h)
                (>= (1+ h) 0)
                (> h (- (expt 2 rho))))
           (< p
              (* (/ (1+ h) (expt 2 rho))
                 (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-27
                 sqrt-table-28
                 sqrt-table-7
                 (:instance sqrt-table-9 (x p)
                            (y (* (/ (1+ h) (expt 2 rho))
                                  (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))))
                            (z (* (/ (1+ h) (expt 2 rho))
                                  (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho)))))))
                            (w (* (/ (1+ h) (expt 2 rho))
                                  (+ d (* (1+ h) (expt 2 (- (* k rho))))))))))))

(local-defthm sqrt-table-30
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (< i (expt 2 m))
                (< i (1- (expt 2 m)))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m)))
                (integerp h)
                (> h (- (expt 2 rho)))
                (<= (+ (pi0 i m) (expt 2 (- 3 m)))
                    (* (/ (1+ h) (expt 2 rho))
                       (+ (delta0 j n) (expt 2 (- n)) (* (1+ h) (expt 2 (- (* k rho))))))))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-22
                 sqrt-table-29))))

(local-defthm sqrt-table-31
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (< i (expt 2 m))
                (< i (1- (expt 2 m)))
                (< i (1- (expt 2 m)))
                (>= i (expt 2 (1- m)))
                (= h (lookup i j table)))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               )
           :use (sqrt-table-30
                 sqrt-table-2
                 sqrt-table-3
                 sqrt-table-5))))

(local-defthm sqrt-table-32
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
          (< p
             (* (/ (1+ h) (expt 2 rho))
                (+ d (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-31
                 sqrt-table-20))))

(local-defthm sqrt-table-33
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (integerp h)
                (>= (1- h) 0))
          (>= (* (/ (1- h) (expt 2 rho))
                 (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho))))))
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 (:instance *-weakly-monotonic (x (/ (1- h) (expt 2 rho))) (y+ (+ (delta0 j n) (expt 2 (- n)))) (y d))))))


(local-defthm sqrt-table-9-a
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (rationalp w)
                (<= x y)
                (<= y z)
                (<= z w))
           (<= x w))
  :rule-classes ())

(local-defthm sqrt-table-34
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (>= p (pi0 i m))
                (integerp h)
                (>= (pi0 i m)
                    (* (/ (1- h) (expt 2 rho))
                       (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho)))))))
                (>= (1- h) 0))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 sqrt-table-33
                 (:instance sqrt-table-9-a (w p)
                            (z (pi0 i m))
                            (y (* (/ (1- h) (expt 2 rho))
                                  (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho)))))))
                            (x (* (/ (1- h) (expt 2 rho))
                                  (+ d (* (1- h) (expt 2 (- (* k rho))))))))))))

(local-defthm sqrt-table-35
  (implies (and (natp k)
                (natp rho)
                (integerp h)
                (> h (- (expt 2 rho))))
           (>= (* (1- h) (expt 2 (- (* k rho))))
               (- (expt 2 (* (- 1 k) rho)))))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-weakly-monotonic (x (expt 2 (- (* k rho)))) (y (- (expt 2 rho))) (y+ (1- h))))))

(local-defthm sqrt-table-36
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x y)
                (>= y z))
           (>= x z))
  :rule-classes ())

(local-defthm sqrt-table-37
  (implies (and (not (zp k))
                (natp rho)
                (integerp h)
                (> h (- (expt 2 rho))))
           (>= (* (1- h) (expt 2 (- (* k rho))))
               -1))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-35
                        sqrt-table-13
                        (:instance sqrt-table-36 (x (* (1- h) (expt 2 (- (* k rho))))) (y (- (expt 2 (* (- 1 k) rho)))) (z -1))))))

(local-defthm sqrt-table-38
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (not (zp k))
                (integerp h)
                (rationalp d)
                (<= (delta0 j n) d)
                (> h (- (expt 2 rho))))
           (>= (+ d (* (1- h) (expt 2 (- (* k rho)))))
               0))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-7
                        sqrt-table-37))))

(local-defthm sqrt-table-39
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (not (zp k))
                (rationalp d)
                (<= (delta0 j n) d)
                (integerp h)
                (< (1- h) 0)
                (> h (- (expt 2 rho))))
           (<= (* (/ (1- h) (expt 2 rho))
                  (+ d (* (1- h) (expt 2 (- (* k rho))))))
               0))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-38
                 sqrt-table-7
                 (:instance *-weakly-monotonic-neg (x (/ (1- h) (expt 2 rho)))
                            (y 0)
                            (y+ (+ d (* (1- h) (expt 2 (- (* k rho)))))))))))

(local-defthm sqrt-table-40
  (implies (and (natp m)
                (natp i)
                (< i (expt 2 m))
                (< i (expt 2 (1- m))))
          (>= (pi0 i m) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0))))

(local-defthm sqrt-table-41
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (natp i)
                (< i (expt 2 m))
                (< i (expt 2 (1- m)))
                (>= p (pi0 i m))
                (integerp h)
                (> h (- (expt 2 rho)))
                (< p
                   (* (/ (1- h) (expt 2 rho))
                      (+ d (* (1- h) (expt 2 (- (* k rho))))))))
           (>= (1- h) 0))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-39
                 sqrt-table-40
                 (:instance sqrt-table-36 (x p) (y 0)
                            (z (* (/ (1- h) (expt 2 rho))
                                  (+ d (* (1- h) (expt 2 (- (* k rho))))))))))))

(local-defthm sqrt-table-42
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (< i (expt 2 (1- m)))
                (>= p (pi0 i m))
                (integerp h)
                (> h (- (expt 2 rho)))
                (>= (pi0 i m)
                    (* (/ (1- h) (expt 2 rho))
                       (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho))))))))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-34
                 sqrt-table-41))))

(local-defthm sqrt-table-43
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (/ (expt 2 n))))
                (natp i)
                (< i (expt 2 m))
                (< i (expt 2 (1- m)))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-42 sqrt-table-2 sqrt-table-4 sqrt-table-6))))

(local-defthm sqrt-table-44
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (>= d (delta0 j n))
                (integerp h)
                (<= (1- h) 0))
          (>= (* (/ (1- h) (expt 2 rho))
                 (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 (:instance *-weakly-monotonic-neg (x (/ (1- h) (expt 2 rho)))
                            (y (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))
                            (y+ (+ d (* (1- h) (expt 2 (- (* k rho)))))))))))

(local-defthm sqrt-table-45
  (implies (and (natp m)
                (natp n)
                (natp k)
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (>= d (delta0 j n))
                (natp i)
                (< i (expt 2 m))
                (>= p (pi0 i m))
                (integerp h)
                (>= (pi0 i m)
                    (* (/ (1- h) (expt 2 rho))
                       (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho)))))))
                (<= (1- h) 0))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-7
                 sqrt-table-44
                 (:instance sqrt-table-9-a (w p)
                            (z (pi0 i m))
                            (y (* (/ (1- h) (expt 2 rho))
                                  (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho)))))))
                            (x (* (/ (1- h) (expt 2 rho))
                                  (+ d (* (1- h) (expt 2 (- (* k rho))))))))))))

(local-defthm sqrt-table-46
  (implies (and (natp m)
                (natp i)
                (< i (expt 2 m))
                (>= i (expt 2 (1- m))))
           (and (rationalp (pi0 i m))
                (< (pi0 i m) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pi0)
                  :use ((:instance *-strongly-monotonic (x (expt 2 (- 2 m))) (y i) (y+ (expt 2 m)))))))

(local-defthm sqrt-table-47
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (not (zp k))
                (integerp h)
                (>= (1- h) 0)
                (> h (- (expt 2 rho))))
           (>= (* (/ (1- h) (expt 2 rho))
                  (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))
               0))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-37
                        sqrt-table-7
                        (:instance *-weakly-monotonic (x (/ (1- h) (expt 2 rho)))
                                                      (y 0)
                                                      (y+ (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho)))))))))))

(local-defthm sqrt-table-48
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (natp i)
                (< i (expt 2 m))
                (>= i (expt 2 (1- m)))
                (integerp h)
                (>= (1- h) 0)
                (> h (- (expt 2 rho))))
           (< (pi0 i m)
              (* (/ (1- h) (expt 2 rho))
                 (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal" :use (sqrt-table-47
                        sqrt-table-7
                        sqrt-table-46))))

(local-defthm sqrt-table-49
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (rationalp d)
                (rationalp p)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (>= p (pi0 i m))
                (< i (expt 2 m))
                (>= i (expt 2 (1- m)))
                (integerp h)
                (> h (- (expt 2 rho)))
                (>= (pi0 i m)
                    (* (/ (1- h) (expt 2 rho))
                       (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-48
                 sqrt-table-45))))

(local-defthm sqrt-table-50
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (>= i (expt 2 (1- m)))
                (= h (lookup i j table)))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-49
                 sqrt-table-2
                 sqrt-table-6
                 sqrt-table-4))))

(local-defthm sqrt-table-51
  (implies (and (natp m)
                (natp n)
                (not (zp k))
                (natp rho)
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
          (>= p
              (* (/ (1- h) (expt 2 rho))
                 (+ d (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (sqrt-table-50
                 sqrt-table-43))))

(defthm lemma-3-4
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (not (zp k))
                (admissible-for-iteration-p k rho m n table)
                (rationalp d)
                (rationalp p)
                (<= (- d) (- p (expt 2 (* (- 1 k) rho))))
                (< (- p (expt 2 (* (- 1 k) rho))) d)
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (< d (+ (delta0 j n) (expt 2 (- n))))
                (natp i)
                (< i (expt 2 m))
                (<= (pi0 i m) p)
                (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                (= h (lookup i j table)))
          (and (< h (expt 2 rho))
               (> h (- (expt 2 rho)))
               (< p
                 (* (/ (1+ h) (expt 2 rho))
                    (+ d (* (1+ h) (expt 2 (- (* k rho)))))))
               (>= p
                  (* (/ (1- h) (expt 2 rho))
                     (+ d (* (1- h) (expt 2 (- (* k rho)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (lookup)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            ))
           :use (sqrt-table-32
                 sqrt-table-51
                 sqrt-table-2))))

;;**********************************************************************************

;; Assume that dmin < dmax and pmin < pmax.  Consider the closed rectangle
;;   R = {(d,p) | dmin <= d <= dmax and pmin <= p <= pmax},
;; the half-closed rectangle
;;   R' = {(d,p) | dmin <= d < dmax and pmin <= p < pmax},
;; and the quarter-closed rectangle
;;   R" = {(d,p) | dmin < d < dmax and pmin <= p < pmax}.
;; If there exists (d,p) in R such that p < h*d + b, then (d5,p5) is a point
;; in R" with p5 < h*d5 + b:

(defund d5 (dmin pmin dmax pmax h b)
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h))))
    ;; (d1,p1) is in R' and p1 < h*d1 + b.
    (if (> d1 dmin)
        d1
      (if (>= (+ (* h dmax) b) p1)
          (/ (+ dmin dmax) 2)
        (/ (+ (/ (- p1 b) h) dmin) 2)))))

(defund p5 (dmin pmin dmax pmax h b)
  (+ b (p1 dmin (- pmin b) dmax (- pmax b) h)))

(local-defthm d5-p5-1
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b)))
             (and (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (< d1 dmax)
                  (<= pmin p1)
                  (< p1 pmax)
                  (< p1 (+ (* h d1) b)))))
  :rule-classes ()
  :hints (("Goal" :use (:instance d1-p1-lemma (p (- p b)) (pmin (- pmin b)) (pmax (- pmax b))))))

(local-defthm d5-p5-2
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (d5 (d5 dmin pmin dmax pmax h b))
        (p5 (p5 dmin pmin dmax pmax h b)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b))
                  (> d1 dmin))
             (and (rationalp d5)
                  (rationalp p5)
                  (< dmin d5)
                  (< d5 dmax)
                  (<= pmin p5)
                  (< p5 pmax)
                  (< p5 (+ (* h d5) b)))))
  :rule-classes ()
  :hints (("Goal" :use (d5-p5-1)
                  :in-theory (enable d5 p5))))

(local-defthm d5-p5-3
  (implies (and (rationalp a1)
                (rationalp a2)
                (rationalp a3)
                (<= a1 a2)
                (< a1 a3))
           (< a1 (/ (+ a2 a3) 2)))
  :rule-classes ())

(local-defthm d5-p5-4
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h)))
        (d5 (d5 dmin pmin dmax pmax h b))
        (p5 (p5 dmin pmin dmax pmax h b)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b))
                  (= d1 dmin)
                  (>= (+ (* h dmax) b) p1))
             (and (rationalp d5)
                  (rationalp p5)
                  (< dmin d5)
                  (< d5 dmax)
                  (<= pmin p5)
                  (< p5 pmax)
                  (< p5 (+ (* h d5) b)))))
  :rule-classes ()
  :hints (("Goal"
           :use (d5-p5-1
                 (:instance d5-p5-3 (a1 (p1 dmin (- pmin b) dmax (- pmax b) h))
                            (a2 (+ (* h dmax) b))
                            (a3 (+ (* h dmin) b))))
           :in-theory (e/d (d5 p5)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4)))))

(local-defthm d5-p5-5
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b))
                  (= d1 dmin)
                  (< (+ (* h dmax) b) p1))
             (< h 0)))
  :rule-classes ()
  :hints (("Goal" :use (d5-p5-1
                        (:instance *-weakly-monotonic (x h) (y (d1 dmin (- pmin b) dmax (- pmax b) h)) (y+ dmax))))))

(local-defthm d5-p5-6
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b))
                  (= d1 dmin)
                  (< (+ (* h dmax) b) p1))
             (< (/ (- p1 b) h) dmax)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d5-p5-1
                 d5-p5-5
                 (:instance *-strongly-monotonic-neg (x h) (y (/ (p1 dmin (- pmin b) dmax (- pmax b) h) h)) (y+ dmax))))))

(local-defthm d5-p5-7
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b))
                  (= d1 dmin)
                  (< (+ (* h dmax) b) p1))
             (> (/ (- p1 b) h) dmin)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d5-p5-1
                 d5-p5-5
                 (:instance *-strongly-monotonic-neg (x h) (y+ (/ (p1 dmin (- pmin b) dmax (- pmax b) h) h)) (y dmin))))))

(local-defthm d5-p5-8
  (let ((d1 (d1 dmin (- pmin b) dmax (- pmax b) h))
        (p1 (+ b (p1 dmin (- pmin b) dmax (- pmax b) h)))
        (d5 (d5 dmin pmin dmax pmax h b))
        (p5 (p5 dmin pmin dmax pmax h b)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (< p (+ (* h d) b))
                  (= d1 dmin)
                  (< (+ (* h dmax) b) p1))
             (and (rationalp d5)
                  (rationalp p5)
                  (< dmin d5)
                  (< d5 dmax)
                  (<= pmin p5)
                  (< p5 pmax)
                  (< p5 (+ (* h d5) b)))))
  :rule-classes ()
  :hints (("Goal"
           :use (d5-p5-1
                        d5-p5-7
                        d5-p5-6)
                  :in-theory (e/d (d5 p5)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4)))))

(defthm d5-p5-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (rationalp b)
                (< p (+ (* h d) b)))
           (let ((d5 (d5 dmin pmin dmax pmax h b))
                 (p5 (p5 dmin pmin dmax pmax h b)))
             (and (rationalp d5)
                  (rationalp p5)
                  (< dmin d5)
                  (< d5 dmax)
                  (<= pmin p5)
                  (< p5 pmax)
                  (< p5 (+ (* h d5) b)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d5-p5-1
                 d5-p5-2
                 d5-p5-4
                 d5-p5-8))))

;;**********************************************************************************

;; If there exists (d,p) in R such that p > h*d + b, then (d6,p6) is a point
;; in R" with p6 > h*d6 + b:

(defund d6 (dmin pmin dmax pmax h b)
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h))))
    ;; (d2,p2) is in R' and p2 > h*d2 + b.
    (if (> d2 dmin)
        d2
      (if (>= p2 (+ (* h dmax) b))
          (/ (+ dmin dmax) 2)
        (/ (+ (/ (- p2 b) h) dmin) 2)))))

(defund p6 (dmin pmin dmax pmax h b)
  (+ b (p2 dmin (- pmin b) dmax (- pmax b) h)))

(local-defthm d6-p6-1
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b)))
             (and (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (< d2 dmax)
                  (<= pmin p2)
                  (< p2 pmax)
                  (> p2 (+ (* h d2) b)))))
  :rule-classes ()
  :hints (("Goal" :use (:instance d2-p2-lemma (p (- p b)) (pmin (- pmin b)) (pmax (- pmax b))))))

(local-defthm d6-p6-2
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (d6 (d6 dmin pmin dmax pmax h b))
        (p6 (p6 dmin pmin dmax pmax h b)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b))
                  (not (= d2 dmin)))
             (and (rationalp d6)
                  (rationalp p6)
                  (< dmin d6)
                  (< d6 dmax)
                  (<= pmin p6)
                  (< p6 pmax)
                  (> p6 (+ (* h d6) b)))))
  :rule-classes ()
  :hints (("Goal" :use (d6-p6-1)
                  :in-theory (enable d6 p6))))

(local-defthm d6-p6-3
  (implies (and (rationalp a1)
                (rationalp a2)
                (rationalp a3)
                (>= a1 a2)
                (> a1 a3))
           (> a1 (/ (+ a2 a3) 2)))
  :rule-classes ())

(local-defthm d6-p6-4
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h)))
        (d6 (d6 dmin pmin dmax pmax h b))
        (p6 (p6 dmin pmin dmax pmax h b)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b))
                  (= d2 dmin)
                  (>= p2 (+ (* h dmax) b)))
             (and (rationalp d6)
                  (rationalp p6)
                  (< dmin d6)
                  (< d6 dmax)
                  (<= pmin p6)
                  (< p6 pmax)
                  (> p6 (+ (* h d6) b)))))
  :rule-classes ()
  :hints (("Goal" :use (d6-p6-1
                        (:instance d6-p6-3 (a1 (p2 dmin (- pmin b) dmax (- pmax b) h))
                                           (a2 (+ (* h dmax) b))
                                           (a3 (+ (* h dmin) b))))
                  :in-theory (enable d6 p6))))

(local-defthm d6-p6-5
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b))
                  (= d2 dmin)
                  (< p2 (+ (* h dmax) b)))
             (> h 0)))
  :rule-classes ()
  :hints (("Goal" :use (d6-p6-1
                        (:instance *-weakly-monotonic-neg (x h) (y (d2 dmin (- pmin b) dmax (- pmax b) h)) (y+ dmax))))))

(local-defthm d6-p6-6
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b))
                  (= d2 dmin)
                  (< p2 (+ (* h dmax) b)))
             (< (/ (- p2 b) h) dmax)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d6-p6-1
                 d6-p6-5
                 (:instance *-strongly-monotonic (x h) (y (/ (p2 dmin (- pmin b) dmax (- pmax b) h) h)) (y+ dmax))))))

(local-defthm d6-p6-7
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h))))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b))
                  (= d2 dmin)
                  (< p2 (+ (* h dmax) b)))
             (> (/ (- p2 b) h) dmin)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d6-p6-1
                 d6-p6-5
                 (:instance *-strongly-monotonic (x h) (y+ (/ (p2 dmin (- pmin b) dmax (- pmax b) h) h)) (y dmin))))))

(local-defthm d6-p6-8
  (let ((d2 (d2 dmin (- pmin b) dmax (- pmax b) h))
        (p2 (+ b (p2 dmin (- pmin b) dmax (- pmax b) h)))
        (d6 (d6 dmin pmin dmax pmax h b))
        (p6 (p6 dmin pmin dmax pmax h b)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (rationalp d)
                  (rationalp p)
                  (< 0 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (<= dmin d)
                  (<= d dmax)
                  (<= pmin p)
                  (<= p pmax)
                  (rationalp h)
                  (rationalp b)
                  (> p (+ (* h d) b))
                  (= d2 dmin)
                  (< p2 (+ (* h dmax) b)))
             (and (rationalp d6)
                  (rationalp p6)
                  (< dmin d6)
                  (< d6 dmax)
                  (<= pmin p6)
                  (< p6 pmax)
                  (> p6 (+ (* h d6) b)))))
  :rule-classes ()
  :hints (("Goal"
           :use (d6-p6-1
                 d6-p6-7
                 d6-p6-6)
           :in-theory (enable d6 p6))))

(defthm d6-p6-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (rationalp d)
                (rationalp p)
                (< 0 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (<= dmin d)
                (<= d dmax)
                (<= pmin p)
                (<= p pmax)
                (rationalp h)
                (rationalp b)
                (> p (+ (* h d) b)))
           (let ((d6 (d6 dmin pmin dmax pmax h b))
                 (p6 (p6 dmin pmin dmax pmax h b)))
             (and (rationalp d6)
                  (rationalp p6)
                  (< dmin d6)
                  (< d6 dmax)
                  (<= pmin p6)
                  (< p6 pmax)
                  (> p6 (+ (* h d6) b)))))
  :rule-classes ()
  :hints (("Goal" :use (d6-p6-2
                        d6-p6-4
                        d6-p6-8))))

;;**********************************************************************************

;; Assume h2 < h1 and h2 + b2 <= h1 + b1.  Then for all d > 1,
;
;;   (h1*d + b1) - (h2*d + b2) = (h1 - h2)*d + (b1 - b2)
;;                             > (h1 - h2) + (b1 - b2)
;;                             >= 0.
;;
;; Assume dmin >= 1.  If there exist (d1,p1) and (d2,p2) in R such that
;; p1 < h1*d1 + b1 and p2 > h2*d2 + b2, then (d7,p7) is in R" and
;; h2*d7 + b2 < p7 < h1*d7 + b1:

(defund d7 (dmin pmin dmax pmax h1 b1 h2 b2)
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2)))
    (if (> p5 (+ (* h2 d5) b2))
        d5
      (if (< p6 (+ (* h1 d6) b1))
          d6
        (if (<= p5 (+ (* h2 d6) b2))
            d6
          (if (>= p5 (+ (* h1 d6) b1))
              (/ (+ (/ (- p5 b1) h1) (/ (- p5 b2) h2)) 2)
            d6))))))

(defund p7 (dmin pmin dmax pmax h1 b1 h2 b2)
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2)))
    (if (> p5 (+ (* h2 d5) b2))
        p5
      (if (< p6 (+ (* h1 d6) b1))
          p6
        (if (<= p5 (+ (* h2 d6) b2))
            (/ (+ (* (+ h1 h2) d6) b1 b2) 2)
          p5)))))

;; We have p5 < h1*d5 + b1 and p6 > h2*d6 + b2.
;; The claim is proved by the following case analysis:

;; Case 1: p5 > h2*d5 + b2.
;;   (d7,p7) = (d5,p5).
;;   h2*d7 + b2 = h2*d5 + b2  < p5 = p7 < h1*d7 + b1.

;; Case 2: p6 < h1*d6 + b1.
;;   (d7,p7) = (d6,p6).
;;   h2*d7 + b2 = h2*d6 + b2 < p6 = p7 < h1*d6 + b1.

;; Case 3: p6 >= h1*d6 + b1, p5 <= h2*d6 + b2.
;;   (d7,p7) = (d6,((h1+h2)*d6+b1+b1)/2).
;;   Let y1 = h1*d6 + b1 and y2 = h2*d6 + b2.  Then p7 = (y1+y2)/2 and
;;   h2*d7 + b2 = h2*d6 + b2 < h1*d6 + b1 = h1*d7 + b1.
;;   Since p5 <= y2 < y1 <= p6, pmin < p5 < p7 < p6 < pmax.

;; Case 4: p5 <= h2*d5 + b2, p5 > h2*d6 + b2, p5 >= h1*d6 + b1.
;;   (d7,p7) = ((x1+x2)/2,p5), where x1 = (p5-b1)/h1 and x2 = (p5-b2)/h2.
;;   Since h2*d6 + b2 < p5 <= h2*d5 + b2, h2*(d5 - d6) > 0.

;;   Case 4a: d5 > d6.
;;     h1 > h2 > 0.
;;     Since h2*d6 + b2 < p5 <= h2*d5 + b2, d6 < (p5-b2)/h2 = x2 < d5.
;;     Since p5 >= h1*d6 + b1, x1 = (p5-b1)/h1 >= d6.
;;     Since h1*(x2 - x1) = h1*x2 - p5 + b1
;;                        = h1*x2 - (h2*x2 + b2) + b1
;;                        = (h1*x2 + b1) - (h2*x2 + b2)
;;                        > 0,
;;     x2 > x1.
;;     Thus, dmin < d6 <= x1 < x2 < d5 < dmax and
;;     (p5-b1)/h1 = x1 < d7 < x2 = (p5-b2)/h2, which implies
;;     h2*d7 + b2 < p5 < h1*d7 + b1.

;;   Case 4b: d5 < d6.
;;     h2 < 0 and d5 <= (p5-b2)/h2 = x2 < d6.
;;     Since h1*d5 + b1 > h2*d5 + b2 >= p5 >= h1*d6 + b1,
;;     h1*(d6 - d5) < 0, which implies h1 < 0.
;;     Since p5 >= h1*d6 + b1, x1 = (p5-b1)/h1 <= d6.
;;     Since p5 <= h2*d5 + b2 < h1*d5 + b1, (p5-b1)/h1 > d5 > 1.
;;     Since h2*(x1-x2) = h2*x1 - p5 + b2
;;                      = h2*x1 - (h2*x1 + b2) + b1
;;                      = (h2*x1 + b1) - (h2*x1 + b2)
;;                      < 0,
;;     x1 > x2.
;;     Thus, dmin < d5 <= x2 < x1 <= d6 < dmax and
;;     (p5-b2)/h2 = x2 < d7 < x1 = (p5-b1)/h1, which implies
;;     h2*d7 + b2 < p5 < h1*d7 + b1.

;;   Case 5: p5 > h2*d6 + b2, p5 < h1*d6 + b1.
;;     (d7,p7) = (d6,p5).
;;     h2*d7 + b2 = h2*d6 + b2 > p5 = p7 < h1*d7 + b1 = h1*d6 + b1.

(local-defthm d7-p7-1
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (rationalp h2)
                  (rationalp b2)
                  (> p2 (+ (* h2 d2) b2)))
             (and (rationalp d5)
                  (rationalp p5)
                  (< dmin d5)
                  (< d5 dmax)
                  (<= pmin p5)
                  (< p5 pmax)
                  (< p5 (+ (* h1 d5) b1))
                  (rationalp d6)
                  (rationalp p6)
                  (< dmin d6)
                  (< d6 dmax)
                  (<= pmin p6)
                  (< p6 pmax)
                  (> p6 (+ (* h2 d6) b2)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance d5-p5-lemma (d d1) (p p1) (h h1) (b b1))
                        (:instance d6-p6-lemma (d d2) (p p2) (h h2) (b b2))))))

(local-defthm d7-p7-2
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
        (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
  (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (rationalp h2)
                  (rationalp b2)
                  (> p2 (+ (* h2 d2) b2))
                  (or (> p5 (+ (* h2 d5) b2))
                      (< p6 (+ (* h1 d6) b1))))
             (and (rationalp d7)
                  (rationalp p7)
                  (< dmin d7)
                  (< d7 dmax)
                  (<= pmin p7)
                  (< p7 pmax)
                  (< p7 (+ (* h1 d7) b1))
                  (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal" :use (d7-p7-1)
                  :in-theory (enable d7 p7))))

(local-defthm d7-p7-3
  (implies (and (rationalp d)
                (> d 1)
                (rationalp h1)
                (rationalp b1)
                (rationalp h2)
                (rationalp b2)
                (< h2 h1)
                (<= (+ h2 b2) (+ h1 b1)))
           (< (+ (* h2 d) b2) (+ (* h1 d) b1)))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-strongly-monotonic (x (- h1 h2)) (y 1) (y+ d)))))

(local-defthm d7-p7-4
  (implies (and (rationalp x)
                (rationalp y)
                (< x y))
           (and (< x (/ (+ x y) 2))
                (> y (/ (+ x y) 2))))
  :rule-classes ())

(local-defthm d7-p7-5
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
        (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
  (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>=  p6 (+ (* h1 d6) b1))
                  (<= p5 (+ (* h2 d6) b2)))
             (and (rationalp d7)
                  (rationalp p7)
                  (< dmin d7)
                  (< d7 dmax)
                  (<= pmin p7)
                  (< p7 pmax)
                  (< p7 (+ (* h1 d7) b1))
                  (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal" :use (d7-p7-1
                        (:instance d7-p7-3 (d (d6 dmin pmin dmax pmax h2 b2)))
                        (:instance d7-p7-4 (x (+ (* h2 (d6 dmin pmin dmax pmax h2 b2)) b2))
                                           (y (+ (* h1 (d6 dmin pmin dmax pmax h2 b2)) b1))))
                  :in-theory (e/d (d7 p7)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4)))))


(local-defthm d7-p7-6
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
  (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1)))
             (> (* h2 (- d5 d6)) 0)))
  :rule-classes ()
  :hints (("Goal" :use (d7-p7-1))))

(local-defthm d7-p7-7
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
  (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (> h2 0)))
  :rule-classes ()
  :hints (("Goal" :use (d7-p7-1 d7-p7-6))))

(local-defthm d7-p7-8
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (< d6 (/ (- p5 b2) h2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-7
                 (:instance *-strongly-monotonic (x h2)
                            (y (d6 dmin pmin dmax pmax h2 b2))
                            (y+ (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)))))))

(local-defthm d7-p7-9
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (>= d5 (/ (- p5 b2) h2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-7
                 (:instance *-weakly-monotonic (x h2)
                            (y+ (d5 dmin pmin dmax pmax h1 b1))
                            (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)))))))

(local-defthm d7-p7-10
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (<= d6 (/ (- p5 b1) h1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-7
                 (:instance *-weakly-monotonic (x h1)
                            (y (d6 dmin pmin dmax pmax h2 b2))
                            (y+ (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))))))

(local-defthm d7-p7-11
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (> (* h1 (- (/ (- p5 b2) h2) (/ (- p5 b1) h1)))
                0)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-8
                 (:instance d7-p7-3 (d (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)))))))

(local-defthm d7-p7-12
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (> (/ (- p5 b2) h2) (/ (- p5 b1) h1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-7
                 d7-p7-11
                 (:instance *-strongly-monotonic (x h1)
                            (y+ (- (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)
                                   (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))
                            (y 0))))))

(local-defthm d7-p7-13
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (and (rationalp d7)
                  (< d7 (/ (- p5 b2) h2))
                  (> d7 (/ (- p5 b1) h1)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (d7 p7)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
           :use (d7-p7-1
                 d7-p7-12
                 (:instance d7-p7-4 (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2))
                            (x (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))))))

(local-defthm d7-p7-14
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (< p5 (+ (* h1 d7) b1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-13
                 d7-p7-7
                 (:instance *-strongly-monotonic (x h1)
                            (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1))
                            (y+ (d7 dmin pmin dmax pmax h1 b1 h2 b2)))))))

(local-defthm d7-p7-15
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (> p5 (+ (* h2 d7) b2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-13
                 d7-p7-7
                 (:instance *-strongly-monotonic (x h2)
                            (y+ (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2))
                            (y (d7 dmin pmin dmax pmax h1 b1 h2 b2)))))))

(local-defthm d7-p7-16
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
        (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (> d5 d6))
             (and (rationalp d7)
                  (rationalp p7)
                  (< dmin d7)
                  (< d7 dmax)
                  (<= pmin p7)
                  (< p7 pmax)
                  (< p7 (+ (* h1 d7) b1))
                  (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (p7)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            ))
           :use (d7-p7-1
                 d7-p7-8
                 d7-p7-9
                 d7-p7-10
                 d7-p7-12
                 d7-p7-13
                 d7-p7-14
                 d7-p7-15))))


(local-defthm d7-p7-17
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
  (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (< h2 0)))
  :rule-classes ()
  :hints (("Goal"
           :use (d7-p7-1 d7-p7-6))))

(local-defthm d7-p7-18
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (> d6 (/ (- p5 b2) h2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-17
                 (:instance *-strongly-monotonic-neg (x h2)
                            (y+ (d6 dmin pmin dmax pmax h2 b2))
                            (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)))))))

(local-defthm d7-p7-19
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (<= d5 (/ (- p5 b2) h2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4
                               acl2::default-less-than-2)
           :use (d7-p7-1
                 d7-p7-17
                 (:instance *-weakly-monotonic-neg (x h2)
                            (y (d5 dmin pmin dmax pmax h1 b1))
                            (y+ (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)))))))

(local-defthm d7-p7-20
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (< h1 0)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 (:instance d7-p7-3 (d (d5 dmin pmin dmax pmax h1 b1)))
                 (:instance *-weakly-monotonic (x h1)
                            (y 0)
                            (y+ (- (d6 dmin pmin dmax pmax h2 b2) (d5 dmin pmin dmax pmax h1 b1))))))))

(local-defthm d7-p7-21
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (>= d6 (/ (- p5 b1) h1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-20
                 (:instance *-weakly-monotonic-neg (x h1)
                            (y+ (d6 dmin pmin dmax pmax h2 b2))
                            (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))))))

(local-defthm d7-p7-22
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (< d5 (/ (- p5 b1) h1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-20
                 (:instance d7-p7-3 (d (d5 dmin pmin dmax pmax h1 b1)))
                 (:instance *-strongly-monotonic-neg (x h1)
                            (y (d5 dmin pmin dmax pmax h1 b1))
                            (y+ (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))))))

(local-defthm d7-p7-23
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (< (* h2 (- (/ (- p5 b1) h1) (/ (- p5 b2) h2)))
                0)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-22
                 (:instance d7-p7-3 (d (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))))))

(local-defthm d7-p7-24
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (< (/ (- p5 b2) h2) (/ (- p5 b1) h1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-17
                 d7-p7-23
                 (:instance *-strongly-monotonic-neg (x h2)
                            (y+ (- (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)
                                   (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2)))
                            (y 0))))))

(local-defthm d7-p7-25
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (and (rationalp d7)
                  (> d7 (/ (- p5 b2) h2))
                  (< d7 (/ (- p5 b1) h1)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (d7 p7)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
                  :use (d7-p7-1
                        d7-p7-24
                        (:instance d7-p7-4 (x (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2))
                                           (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1)))))))

(local-defthm d7-p7-26
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (< p5 (+ (* h1 d7) b1))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-25
                 d7-p7-20
                 (:instance *-strongly-monotonic-neg (x h1)
                            (y+ (/ (- (p5 dmin pmin dmax pmax h1 b1) b1) h1))
                            (y (d7 dmin pmin dmax pmax h1 b1 h2 b2)))))))

(local-defthm d7-p7-27
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (> p5 (+ (* h2 d7) b2))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-25
                 d7-p7-20
                 (:instance *-strongly-monotonic-neg (x h2)
                            (y (/ (- (p5 dmin pmin dmax pmax h1 b1) b2) h2))
                            (y+ (d7 dmin pmin dmax pmax h1 b1 h2 b2)))))))

(local-defthm d7-p7-28
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
        (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1))
                  (< d5 d6))
             (and (rationalp d7)
                  (rationalp p7)
                  (< dmin d7)
                  (< d7 dmax)
                  (<= pmin p7)
                  (< p7 pmax)
                  (< p7 (+ (* h1 d7) b1))
                  (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (p7)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
           :use (d7-p7-1
                 d7-p7-19
                 d7-p7-25
                 d7-p7-21
                 d7-p7-26
                 d7-p7-27))))

(local-defthm d7-p7-29
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
        (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (>= p5 (+ (* h1 d6) b1)))
             (and (rationalp d7)
                  (rationalp p7)
                  (< dmin d7)
                  (< d7 dmax)
                  (<= pmin p7)
                  (< p7 pmax)
                  (< p7 (+ (* h1 d7) b1))
                  (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-6
                 d7-p7-16
                 d7-p7-28))))

(local-defthm d7-p7-30
  (let ((d5 (d5 dmin pmin dmax pmax h1 b1))
        (p5 (p5 dmin pmin dmax pmax h1 b1))
        (d6 (d6 dmin pmin dmax pmax h2 b2))
        (p6 (p6 dmin pmin dmax pmax h2 b2))
        (d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
        (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
    (implies (and (rationalp dmin)
                  (rationalp pmin)
                  (rationalp dmax)
                  (rationalp pmax)
                  (<= 1 dmin)
                  (< dmin dmax)
                  (< pmin pmax)
                  (rationalp d1)
                  (rationalp p1)
                  (<= dmin d1)
                  (<= d1 dmax)
                  (<= pmin p1)
                  (<= p1 pmax)
                  (rationalp h1)
                  (rationalp b1)
                  (rationalp h2)
                  (rationalp b2)
                  (< h2 h1)
                  (<= (+ h2 b2) (+ h1 b1))
                  (< p1 (+ (* h1 d1) b1))
                  (rationalp d2)
                  (rationalp p2)
                  (<= dmin d2)
                  (<= d2 dmax)
                  (<= pmin p2)
                  (<= p2 pmax)
                  (> p2 (+ (* h2 d2) b2))
                  (<= p5 (+ (* h2 d5) b2))
                  (>= p6 (+ (* h1 d6) b1))
                  (> p5 (+ (* h2 d6) b2))
                  (< p5 (+ (* h1 d6) b1)))
             (and (rationalp d7)
                  (rationalp p7)
                  (< dmin d7)
                  (< d7 dmax)
                  (<= pmin p7)
                  (< p7 pmax)
                  (< p7 (+ (* h1 d7) b1))
                  (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal" :use (d7-p7-1)
                  :in-theory (enable d7 p7))))

(defthm d7-p7-lemma
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp dmax)
                (rationalp pmax)
                (<= 1 dmin)
                (< dmin dmax)
                (< pmin pmax)
                (rationalp h1)
                (rationalp b1)
                (rationalp h2)
                (rationalp b2)
                (< h2 h1)
                (<= (+ h2 b2) (+ h1 b1))
                (rationalp d1)
                (rationalp p1)
                (<= dmin d1)
                (<= d1 dmax)
                (<= pmin p1)
                (<= p1 pmax)
                (< p1 (+ (* h1 d1) b1))
                (rationalp d2)
                (rationalp p2)
                (<= dmin d2)
                (<= d2 dmax)
                (<= pmin p2)
                (<= p2 pmax)
                (> p2 (+ (* h2 d2) b2)))
            (let ((d7 (d7 dmin pmin dmax pmax h1 b1 h2 b2))
                  (p7 (p7 dmin pmin dmax pmax h1 b1 h2 b2)))
               (and (rationalp d7)
                    (rationalp p7)
                    (< dmin d7)
                    (< d7 dmax)
                    (<= pmin p7)
                    (< p7 pmax)
                    (< p7 (+ (* h1 d7) b1))
                    (> p7 (+ (* h2 d7) b2)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (d7-p7-1
                 d7-p7-2
                 d7-p7-5
                 d7-p7-29
                 d7-p7-30))))

;;**********************************************************************************

;; Suppose that (admissible-for-iteration-p k rho m n table) = NIL.
;; Let i = (i-sqrt k rho m n table), j = (j-sqrt k rho m n table),
;; and h = (lookup i j table).
;; Then 0 <= i < 2^m, 0 <= j < 2^n, and
;; (check-sqrt-entry i j k rho m n h) = NIL.
;; Let d = (d-sqrt k rho m n table) and p = (p-sqrt k rho m n table).
;; Then (d,p) is in S_ij and |p - 2^((1-k)*rho)| <= d.
;; If -2^rho < h < 2^rho, then either
;;   p < ((h-1)/2^rho)*(d + (h-1)2^(-k*rho))
;; or
;;   p > ((h+1)/2^rho)*(d + (h+1)2^(-k*rho)).

(defund i-sqrt-aux (i k rho m n table)
  (if (zp i)
      ()
    (if (check-sqrt-row (1- i) (expt 2 n) k rho m n (nth (1- i) table))
        (i-sqrt-aux (1- i) k rho m n table)
      (1- i))))

(defund i-sqrt (k rho m n table)
  (i-sqrt-aux (expt 2 m) k rho m n table))

(defund j-sqrt-aux (i j k rho m n row)
  (if (zp j)
      ()
    (if (check-sqrt-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
        (j-sqrt-aux i (1- j) k rho m n row)
      (1- j))))

(defund j-sqrt (k rho m n table)
  (let ((i (i-sqrt k rho m n table)))
    (j-sqrt-aux i (expt 2 n) k rho m n (nth i table))))

(defund d-sqrt (k rho m n table)
  (let* ((i (i-sqrt k rho m n table))
         (j (j-sqrt k rho m n table))
         (h (lookup i j table)))
    (if (or (not (integerp h))
            (>= h (expt 2 rho))
            (<= h (- (expt 2 rho))))
        (d7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            1
            (expt 2 (* (- 1 k) rho))
            -1
            (expt 2 (* (- 1 k) rho)))
      (if (not (check-upper-bound h i j k rho m n))
          (d7 (delta0 j n)
              (pi0 i m)
              (+ (delta0 j n) (expt 2 (- n)))
              (+ (pi0 i m) (expt 2 (- 3 m)))
              1
              (expt 2 (* (- 1 k) rho))
              (/ (1+ h) (expt 2 rho))
              (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
        (d7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            (/ (1- h) (expt 2 rho))
            (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
            -1
            (expt 2 (* (- 1 k) rho)))))))

(defund p-sqrt (k rho m n table)
  (let* ((i (i-sqrt k rho m n table))
         (j (j-sqrt k rho m n table))
         (h (lookup i j table)))
    (if (or (not (integerp h))
            (>= h (expt 2 rho))
            (<= h (- (expt 2 rho))))
        (p7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            1
            (expt 2 (* (- 1 k) rho))
            -1
            (expt 2 (* (- 1 k) rho)))
      (if (not (check-upper-bound h i j k rho m n))
          (p7 (delta0 j n)
              (pi0 i m)
              (+ (delta0 j n) (expt 2 (- n)))
              (+ (pi0 i m) (expt 2 (- 3 m)))
              1
              (expt 2 (* (- 1 k) rho))
              (/ (1+ h) (expt 2 rho))
              (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
        (p7 (delta0 j n)
            (pi0 i m)
            (+ (delta0 j n) (expt 2 (- n)))
            (+ (pi0 i m) (expt 2 (- 3 m)))
            (/ (1- h) (expt 2 rho))
            (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
            -1
            (expt 2 (* (- 1 k) rho)))))))

(local-defthm converse-33
  (implies (and (natp i)
                (not (check-sqrt-rows i k rho m n table)))
           (let ((w (i-sqrt-aux i k rho m n table)))
             (and (natp w)
                  (< w i)
                  (not (check-sqrt-row w (expt 2 n) k rho m n (nth w table))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable i-sqrt-aux check-sqrt-rows))))

(local-defthm converse-34
  (implies (and (natp m)
                (not (admissible-for-iteration-p k rho m n table)))
           (let ((i (i-sqrt k rho m n table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (not (check-sqrt-row i (expt 2 n) k rho m n (nth i table))))))
  :rule-classes ()
  :hints (("Goal" :use (:instance converse-33 (i (expt 2 m)))
                  :in-theory (enable i-sqrt admissible-for-iteration-p))))

(local-defthm converse-35
  (implies (and (natp j)
                (not (check-sqrt-row i j k rho m n row)))
           (let ((w (j-sqrt-aux i j k rho m n row)))
             (and (natp w)
                  (< w j)
                  (not (check-sqrt-entry i w k rho m n (ifix (nth w row)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable j-sqrt-aux check-sqrt-row))))

(local-defthm converse-36
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (h (lookup i j table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (sqrt-accessible-p i j k rho m n)
                  (not (and (integerp h)
                            (< (- (expt 2 rho)) h)
                            (< h (expt 2 rho))
                            (check-upper-bound h i j k rho m n)
                            (check-lower-bound h i j k rho m n))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-34
                        (:instance converse-35 (i (i-sqrt k rho m n table))
                                               (j (expt 2 n))
                                               (row (nth (i-sqrt k rho m n table) table))))
                  :in-theory (enable lookup check-sqrt-entry j-sqrt))))

(local-defthm converse-37
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-sqrt-entry i j k rho m n h)))
           (and (< (- (expt 2 (* (- 1 k) rho)) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
                   (pi0 i m))
                (< (pi0 i m)
                   (+ (delta0 j n) (/ (expt 2 n)) (expt 2 (* (- 1 k) rho))))
                (or (not (check-upper-bound h i j k rho m n))
                    (not (check-lower-bound h i j k rho m n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-entry sqrt-accessible-p))))

(local-defthm converse-38
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-upper-bound h i j k rho m n)))
           (<= h (- (expt 2 rho) 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-upper-bound))))

(local-defthm converse-39
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (rationalp (delta0 j n))
                (rationalp (pi0 i m))
                (>= (delta0 j n) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable delta0 pi0))))

(local-defthm converse-40
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m))))
                (not (check-upper-bound h i j k rho m n)))
           (> (+ (pi0 i m) (expt 2 (- 3 m)))
                 (* (/ (1+ h) (expt 2 rho))
                    (+ (delta0 j n) (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-upper-bound))))

(local-defthm converse-41
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-upper-bound h i j k rho m n)))
           (< (/ (1+ h) (expt 2 rho)) 1))
  :rule-classes ()
  :hints (("Goal" :use (converse-38
                        (:instance *-strongly-monotonic (x (/ (expt 2 rho)))
                                                        (y (1+ h))
                                                        (y+ (expt 2 rho)))))))

(local-defthm converse-42
  (implies (and (not (zp x))
                (not (zp y)))
           (not (zp (* x y))))
  :rule-classes ())

(local-defthm converse-43
  (implies (and (integerp x)
                (natp y)
                (< x y)
                (> x (- y)))
           (< (* x x) (* y y)))
  :rule-classes ()
  :hints (("Goal" :use (:instance converse-42 (x (+ y x)) (y (- y x))))))

(local-defthm converse-44
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-upper-bound h i j k rho m n)))
           (< (* (1+ h) (1+ h))
              (expt 2 (* 2 rho))))
  :rule-classes ()
  :hints (("Goal" :use (converse-38
                        (:instance converse-43 (x (1+ h)) (y (expt 2 rho)))))))

(local-defthm converse-45
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (not (zp k))
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-upper-bound h i j k rho m n)))
           (< (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho))))
              (expt 2 (* (- 1 k) rho))))
  :rule-classes ()
  :hints (("Goal" :use (converse-44
                        (:instance *-strongly-monotonic (x (expt 2 (- (* (1+ k) rho))))
                                                        (y (* (1+ h) (1+ h)))
                                                        (y+ (expt 2 (* 2 rho))))))))

(local-defthm converse-46
  (implies (and (rationalp h1)
                (rationalp b1)
                (rationalp h2)
                (rationalp b2)
                (< h2 h1)
                (< b2 b1))
           (< (+ h2 b2) (+ h1 b1)))
  :rule-classes ())


(local-defthm converse-47
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (not (zp k))
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-upper-bound h i j k rho m n)))
           (< (+ (/ (1+ h) (expt 2 rho))
                 (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
              (1+ (expt 2 (* (- 1 k) rho)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-45
                 converse-41
                 (:instance converse-46 (h1 1)
                            (b1 (expt 2 (* (- 1 k) rho)))
                            (h2 (/ (1+ h) (expt 2 rho)))
                            (b2 (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho))))))))))


(local-defthm converse-48
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (not (check-upper-bound h i j k rho m n))
                           (or (< i (expt 2 (1- m)))
                               (= i (1- (expt 2 m)))))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (< p (+ d (expt 2 (* (- 1 k) rho))))
                           (> p (* (/ (1+ h) (expt 2 rho)) (+ d (* (1+ h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-sqrt-entry d-sqrt p-sqrt)
                           (jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                            acl2::not-integerp-1a-expt
                            acl2::not-integerp-2a-expt
                            acl2::not-integerp-3a-expt
                            acl2::not-integerp-4a-expt
                            acl2::not-integerp-1d-expt
                            acl2::not-integerp-2d-expt
                            acl2::not-integerp-3d-expt
                            acl2::not-integerp-4d-expt
                            acl2::default-expt-1
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                            acl2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
           :use (converse-36
                 (:instance converse-37 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance converse-39 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table)))
                 (:instance converse-40 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance converse-41 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance converse-47 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance d7-p7-lemma (dmin (delta0 (j-sqrt k rho m n table) n))
                            (dmax (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                            (pmin (pi0 (i-sqrt k rho m n table) m))
                            (pmax (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                            (d1 (+ (delta0 (j-sqrt k rho m n table) n) (/ (expt 2 n))))
                            (p1 (pi0 (i-sqrt k rho m n table) m))
                            (d2 (delta0 (j-sqrt k rho m n table) n))
                            (p2 (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                            (h1 1)
                            (b1 (expt 2 (* (- 1 k) rho)))
                            (h2 (/ (1+ (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 rho)))
                            (b2 (* (1+ (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (1+ (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 (- (* (1+ k) rho))))))))
          ))

(local-defthm converse-49
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (>= i (expt 2 (1- m)))
                (not (= i (1- (expt 2 m))))
                (not (check-upper-bound h i j k rho m n)))
           (> (+ (pi0 i m) (expt 2 (- 3 m)))
                 (* (/ (1+ h) (expt 2 rho))
                    (+ (delta0 j n) (expt 2 (- n)) (* (1+ h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-upper-bound))))

(local-defthm converse-50
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (not (check-upper-bound h i j k rho m n))
                           (>= i (expt 2 (1- m)))
                           (not (= i (1- (expt 2 m)))))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (< p (+ d (expt 2 (* (- 1 k) rho))))
                           (> p (* (/ (1+ h) (expt 2 rho)) (+ d (* (1+ h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           ;; baseline 22.19, now 7.55
           ;;           :in-theory (enable check-sqrt-entry d-sqrt p-sqrt)
           :in-theory (e/d (check-sqrt-entry d-sqrt p-sqrt)
                           (jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                            acl2::not-integerp-1a-expt
                            acl2::not-integerp-2a-expt
                            acl2::not-integerp-3a-expt
                            acl2::not-integerp-4a-expt
                            acl2::not-integerp-1d-expt
                            acl2::not-integerp-2d-expt
                            acl2::not-integerp-3d-expt
                            acl2::not-integerp-4d-expt
                            acl2::default-expt-1
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                            acl2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
           :use (converse-36
                        (:instance converse-37 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance converse-39 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table)))
                        (:instance converse-49 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance converse-41 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance converse-47 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance d7-p7-lemma (dmin (delta0 (j-sqrt k rho m n table) n))
                                               (dmax (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                                               (pmin (pi0 (i-sqrt k rho m n table) m))
                                               (pmax (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                                               (d1 (+ (delta0 (j-sqrt k rho m n table) n) (/ (expt 2 n))))
                                               (p1 (pi0 (i-sqrt k rho m n table) m))
                                               (d2 (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                                               (p2 (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                                               (h1 1)
                                               (b1 (expt 2 (* (- 1 k) rho)))
                                               (h2 (/ (1+ (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 rho)))
                                               (b2 (* (1+ (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (1+ (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm converse-51
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (not (check-upper-bound h i j k rho m n)))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (< p (+ d (expt 2 (* (- 1 k) rho))))
                           (> p (* (/ (1+ h) (expt 2 rho)) (+ d (* (1+ h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-50 converse-48))))

(local-defthm converse-52
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-lower-bound h i j k rho m n)))
           (>= h (- 2 (expt 2 rho))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound))))

(local-defthm converse-53
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-lower-bound h i j k rho m n)))
           (> (/ (1- h) (expt 2 rho)) -1))
  :rule-classes ()
  :hints (("Goal" :use (converse-52
                        (:instance *-strongly-monotonic (x (/ (expt 2 rho)))
                                                        (y+ (1- h))
                                                        (y (- (expt 2 rho))))))))

(local-defthm converse-54
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (>= i (expt 2 (1- m)))
                (not (check-lower-bound h i j k rho m n)))
           (< (pi0 i m)
              (* (/ (1- h) (expt 2 rho))
                 (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound))))

(local-defthm converse-55
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (< i (expt 2 (1- m)))
                (not (check-lower-bound h i j k rho m n)))
           (< (pi0 i m)
              (* (/ (1- h) (expt 2 rho))
                 (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound))))

(local-defthm converse-56
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-lower-bound h i j k rho m n)))
           (>= (/ (1- h) (expt 2 rho))
               (- (expt 2 (- rho)) 1)))
  :rule-classes ()
  :hints (("Goal" :use (converse-52
                        (:instance *-weakly-monotonic (x (expt 2 rho)) (y+ (/ (1- h) (expt 2 rho))) (y (- (expt 2 (- rho)) 1)))))))

(local-defthm converse-57
  (implies (rationalp x)
           (>= (* x x) 0))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-weakly-monotonic (y 0) (y+ x)))))

(local-defthm converse-58
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-lower-bound h i j k rho m n)))
           (>= (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
               0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-57 (x (1- h)))))))

(local-defthm converse-59
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-lower-bound h i j k rho m n)))
           (>= (expt 2 (- rho))
               (expt 2 (* (- 1 k) rho))))
  :rule-classes ())

(local-defthm converse-60
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (rationalp w)
                (>= x (1- z))
                (>= y 0)
                (>= z w))
           (>= (+ x y) (1- w)))
  :rule-classes ())

(local-defthm converse-61
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho))
                (not (check-lower-bound h i j k rho m n)))
           (>= (+ (/ (1- h) (expt 2 rho))
                  (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho)))))
               (- (expt 2 (* (- 1 k) rho)) 1)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-56
                 converse-58
                 converse-59
                 (:instance converse-60 (x (/ (1- h) (expt 2 rho)))
                            (y (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho)))))
                            (z (expt 2 (- rho)))
                            (w (expt 2 (* (- 1 k) rho))))))))

(local-defthm converse-62
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (check-upper-bound h i j k rho m n)
                           (not (check-lower-bound h i j k rho m n))
                           (< i (expt 2 (1- m))))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (> p (- (expt 2 (* (- 1 k) rho)) d))
                           (< p (* (/ (1- h) (expt 2 rho)) (+ d (* (1- h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           ;; baseline 24.75
           ;; :in-theory (enable check-sqrt-entry d-sqrt p-sqrt)
           ;; now 7.2
           :in-theory (e/d (check-sqrt-entry d-sqrt p-sqrt)
                           (jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                            acl2::not-integerp-1a-expt
                            acl2::not-integerp-2a-expt
                            acl2::not-integerp-3a-expt
                            acl2::not-integerp-4a-expt
                            acl2::not-integerp-1d-expt
                            acl2::not-integerp-2d-expt
                            acl2::not-integerp-3d-expt
                            acl2::not-integerp-4d-expt
                            acl2::default-expt-1
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                            acl2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))

           :use (converse-36
                        (:instance converse-37 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance converse-39 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table)))
                        (:instance converse-55 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance converse-53 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance converse-61 (i (i-sqrt k rho m n table))
                                               (j (j-sqrt k rho m n table))
                                               (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                        (:instance d7-p7-lemma (dmin (delta0 (j-sqrt k rho m n table) n))
                                               (dmax (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                                               (pmin (pi0 (i-sqrt k rho m n table) m))
                                               (pmax (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                                               (d1 (+ (delta0 (j-sqrt k rho m n table) n) (/ (expt 2 n))))
                                               (p1 (pi0 (i-sqrt k rho m n table) m))
                                               (d2 (+ (delta0 (j-sqrt k rho m n table) n) (/ (expt 2 n))))
                                               (p2 (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                                               (h2 -1)
                                               (b2 (expt 2 (* (- 1 k) rho)))
                                               (h1 (/ (1- (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 rho)))
                                               (b1 (* (1- (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (1- (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm converse-63
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (check-upper-bound h i j k rho m n)
                           (not (check-lower-bound h i j k rho m n))
                           (>= i (expt 2 (1- m))))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (> p (- (expt 2 (* (- 1 k) rho)) d))
                           (< p (* (/ (1- h) (expt 2 rho)) (+ d (* (1- h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           ;; baseline 20.77
           ;;:in-theory (enable check-sqrt-entry d-sqrt p-sqrt)
           ;; now 7.36
           :in-theory (e/d (check-sqrt-entry d-sqrt p-sqrt)
                           (jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                            acl2::not-integerp-1a-expt
                            acl2::not-integerp-2a-expt
                            acl2::not-integerp-3a-expt
                            acl2::not-integerp-4a-expt
                            acl2::not-integerp-1d-expt
                            acl2::not-integerp-2d-expt
                            acl2::not-integerp-3d-expt
                            acl2::not-integerp-4d-expt
                            acl2::default-expt-1
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                            acl2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
           :use (converse-36
                 (:instance converse-37 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance converse-39 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table)))
                 (:instance converse-54 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance converse-53 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance converse-61 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))
                 (:instance d7-p7-lemma (dmin (delta0 (j-sqrt k rho m n table) n))
                            (dmax (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                            (pmin (pi0 (i-sqrt k rho m n table) m))
                            (pmax (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                            (d1 (delta0 (j-sqrt k rho m n table) n))
                            (p1 (pi0 (i-sqrt k rho m n table) m))
                            (d2 (+ (delta0 (j-sqrt k rho m n table) n) (/ (expt 2 n))))
                            (p2 (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                            (h2 -1)
                            (b2 (expt 2 (* (- 1 k) rho)))
                            (h1 (/ (1- (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 rho)))
                            (b1 (* (1- (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (1- (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm converse-64
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (check-upper-bound h i j k rho m n)
                           (not (check-lower-bound h i j k rho m n)))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (> p (- (expt 2 (* (- 1 k) rho)) d))
                           (< p (* (/ (1- h) (expt 2 rho)) (+ d (* (1- h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (check-sqrt-entry d-sqrt p-sqrt)
                                  (jared-disables-1
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
           :use (converse-62 converse-63))))

(local-defthm converse-65
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (rationalp d)
                (<= (delta0 j n) d))
           (< (* (/ (1- h) (expt 2 rho)) d) d))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        (:instance *-strongly-monotonic (x (/ d (expt 2 rho))) (y (1- h)) (y+ (expt 2 rho)))))) )

(local-defthm converse-66
  (implies (and (integerp x)
                (not (zp y))
                (<= x y)
                (>= x (- y)))
           (<= (* x x) (* y y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x (- y x)) (y 0) (y+ (+ y x)))))))

(local-defthm converse-67
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (rationalp d)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d))
           (<= (* (1- h) (1- h))
               (expt 2 (* 2 rho))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-66 (x (1- h)) (y (expt 2 rho)))))))

(local-defthm converse-68
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (rationalp d)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d)
                (rationalp x)
                (>= x 0))
           (<= (* (1- h) (1- h) x)
               (* (expt 2 (* 2 rho)) x)))
  :rule-classes ()
  :hints (("Goal" :use (converse-67
                        (:instance *-weakly-monotonic (y (* (1- h) (1- h)))
                                                      (y+ (expt 2 (* 2 rho))))))))

(local-defthm converse-69
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (rationalp d)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d))
           (<= (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
               (* (expt 2 (* 2 rho)) (expt 2 (- (* (1+ k) rho))))))
  :rule-classes ()
  :hints (("Goal" :do-not '(preprocess)
                  :use (:instance converse-68 (x (expt 2 (- (* (1+ k) rho))))))))

(local-defthm converse-70
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (rationalp d)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d))
           (<= (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))
               (* (expt 2 (* (- 1 k) rho)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-69))))

(local-defthm converse-71
  (implies (and (rationalp x1)
                (rationalp y1)
                (rationalp x2)
                (rationalp y2)
                (<= x1 x2)
                (<= y1 y2))
           (<= (+ x1 y1) (+ x2 y2)))
  :rule-classes ())

(local-defthm converse-72
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (rationalp d)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (<= (delta0 j n) d))
           (<= (* (/ (1- h) (expt 2 rho)) (+ d (* (1- h) (expt 2 (- (* k rho))))))
               (+ d (expt 2 (* (- 1 k) rho)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)

           :use (converse-65
                 converse-70
                 (:instance converse-71 (x1 (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho)))))
                            (x2 (* (expt 2 (* (- 1 k) rho))))
                            (y1 (* (/ (1- h) (expt 2 rho)) d))
                            (y2 d))))))

(local-defthm converse-73
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (check-upper-bound h i j k rho m n)
                           (not (check-lower-bound h i j k rho m n)))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (< (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                           (< p (* (/ (1- h) (expt 2 rho)) (+ d (* (1- h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-64
                 (:instance converse-72 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (d (d-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))))))


(local-defthm converse-74
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho)))
           (>= (/ (1+ h) (expt 2 rho))
               (- (expt 2 (- rho)) 1)))
  :rule-classes ()
  :hints (("Goal" :use (converse-52
                        (:instance *-weakly-monotonic (x (expt 2 rho)) (y+ (/ (1+ h) (expt 2 rho))) (y (- (expt 2 (- rho)) 1)))))))

(local-defthm converse-75
  (implies (and (rationalp x)
                (rationalp y)
                (>= x 0)
                (>= y 0))
           (>= (* x y) 0))
  :rule-classes ())

(local-defthm converse-76
  (implies (and (natp rho)
                (natp k)
                (integerp h))
           (>= (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho))))
               0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-57 (x (1+ h)))
                        (:instance converse-75 (x (* (1+ h) (1+ h))) (y (expt 2 (- (* (1+ k) rho)))))))))

(local-defthm converse-77
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho)))
           (>= (expt 2 (- rho))
               (expt 2 (* (- 1 k) rho))))
  :rule-classes ())

(local-defthm converse-78
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho)))
           (>= (+ (/ (1+ h) (expt 2 rho))
                  (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
               (- (expt 2 (* (- 1 k) rho)) 1)))
  :rule-classes ()
  :hints (("Goal"
           :use (converse-74
                 converse-76
                 converse-77
                 (:instance converse-60 (x (/ (1+ h) (expt 2 rho)))
                            (y (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
                            (z (expt 2 (- rho)))
                            (w (expt 2 (* (- 1 k) rho))))))))

(local-defthm converse-79
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho)))
           (> (/ (1+ h) (expt 2 rho))
              -1))
  :rule-classes ()
  :hints (("Goal" :use (converse-74))))

(local-defthm converse-80
  (implies (and (rationalp d)
                (>= d 1)
                (rationalp h1)
                (rationalp b1)
                (rationalp h2)
                (rationalp b2)
                (< h2 h1)
                (<= (+ h2 b2) (+ h1 b1)))
           (<= (+ (* h2 d) b2) (+ (* h1 d) b1)))
  :rule-classes ()
  :hints (("Goal" :use (:instance *-weakly-monotonic (x (- h1 h2)) (y 1) (y+ d)))))

(local-defthm converse-81
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (> k 1)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (rationalp d)
                (>= d (delta0 j n))
                (< h (expt 2 rho)))
           (>= (+ (* (/ (1+ h) (expt 2 rho)) d)
                  (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
               (- (expt 2 (* (- 1 k) rho)) d)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-79
                 converse-39
                 converse-78
                 (:instance converse-80 (h1 (/ (1+ h) (expt 2 rho)))
                            (b1 (* (1+ h) (1+ h) (expt 2 (- (* (1+ k) rho)))))
                            (h2 -1)
                            (b2 (expt 2 (* (- 1 k) rho))))))))

(local-defthm converse-82
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (h (lookup i j table)))
             (implies (and (integerp h)
                           (< h (expt 2 rho))
                           (> h (- (expt 2 rho)))
                           (not (check-upper-bound h i j k rho m n)))
                      (and (natp i)
                           (< i (expt 2 m))
                           (natp j)
                           (< j (expt 2 n))
                           (rationalp d)
                           (rationalp p)
                           (<= (delta0 j n) d)
                           (< d (+ (delta0 j n) (expt 2 (- n))))
                           (<= (pi0 i m) p)
                           (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                           (< (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                           (> p (* (/ (1+ h) (expt 2 rho)) (+ d (* (1+ h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-51
                 (:instance converse-81 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table))
                            (d (d-sqrt k rho m n table))
                            (h (lookup (i-sqrt k rho m n table) (j-sqrt k rho m n table) table)))))))

(local-defthm converse-83
  (let* ((i (i-sqrt k rho m n table))
         (j (j-sqrt k rho m n table))
         (d (d-sqrt k rho m n table))
         (p (p-sqrt k rho m n table))
         (h (lookup i j table)))
    (implies (and (not (zp m))
                  (not (zp n))
                  (not (zp rho))
                  (natp k)
                  (> k 1)
                  (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (sqrt-accessible-p i j k rho m n)
                  (not (and (integerp h)
                            (< (- (expt 2 rho)) h)
                            (< h (expt 2 rho)))))
             (and (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (expt 2 (- n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (expt 2 (- 3 m))))
                  (< (abs (- p (expt 2 (* (- 1 k) rho)))) d))))
  :rule-classes ()
  :hints (("Goal"
           ;; baseline 11.38 sec
           ;; :in-theory (enable d-sqrt p-sqrt sqrt-accessible-p)
           ;; now 1.71
           :in-theory (e/d (check-sqrt-entry d-sqrt p-sqrt sqrt-accessible-p)
                           (jared-disables-2
                            jared-disables-3
                            jared-disables-4
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B
                            acl2::not-integerp-1a-expt
                            acl2::not-integerp-2a-expt
                            acl2::not-integerp-3a-expt
                            acl2::not-integerp-4a-expt
                            acl2::not-integerp-1d-expt
                            acl2::not-integerp-2d-expt
                            acl2::not-integerp-3d-expt
                            acl2::not-integerp-4d-expt
                            acl2::default-expt-1
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE
                            acl2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A
                            acl2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
           :use ((:instance converse-39 (i (i-sqrt k rho m n table))
                            (j (j-sqrt k rho m n table)))
                 (:instance d7-p7-lemma
                            (dmin (delta0 (j-sqrt k rho m n table) n))
                            (dmax (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                            (pmin (pi0 (i-sqrt k rho m n table) m))
                            (pmax (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                            (d1 (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                            (p1 (pi0 (i-sqrt k rho m n table) m))
                            (d2 (+ (delta0 (j-sqrt k rho m n table) n) (expt 2 (- n))))
                            (p2 (+ (pi0 (i-sqrt k rho m n table) m) (expt 2 (- 3 m))))
                            (b2 (expt 2 (* (- 1 k) rho)))
                            (b1 (expt 2 (* (- 1 k) rho)))
                            (h2 -1)
                            (h1 1))))))

(defthm lemma-3-4-converse
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (> k 1)
                (not (admissible-for-iteration-p k rho m n table)))
           (let* ((i (i-sqrt k rho m n table))
                  (j (j-sqrt k rho m n table))
                  (p (p-sqrt k rho m n table))
                  (d (d-sqrt k rho m n table))
                  (h (lookup i j table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (rationalp d)
                  (rationalp p)
                  (<= (delta0 j n) d)
                  (< d (+ (delta0 j n) (/ (expt 2 n))))
                  (<= (pi0 i m) p)
                  (< p (+ (pi0 i m) (/ (expt 2 (- m 3)))))
                  (< (abs (- p (expt 2 (* (- 1 k) rho)))) d)
                  (or (<= h (- (expt 2 rho)))
                      (>= h (expt 2 rho))
                      (< p (* (/ (1- h) (expt 2 rho))
                              (+ d (* (1- h) (expt 2 (- (* k rho)))))))
                      (> p (* (/ (1+ h) (expt 2 rho))
                              (+ d (* (1+ h) (expt 2 (- (* k rho)))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-83 converse-82 converse-73 converse-36))))

;;**********************************************************************************

(defund accessible-p (i j k rho m n)
  (and (< (- (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))
          (pi0 i m))
       (< (pi0 i m)
          (+ (delta0 j n) (/ (expt 2 n)) (expt 2 (- (* k rho)))))))

(defthm div-accessible-accessible
  (implies (and (integerp m)
                (integerp n)
                (integerp rho)
                (integerp k)
                (integerp i)
                (integerp j)
                (div-accessible-p i j m n))
           (accessible-p i j k rho m n))
  :hints (("Goal" :in-theory (enable div-accessible-p accessible-p))))

(defund check-entry (i j k rho m n entry)
  (or (not (accessible-p i j k rho m n))
      (and (< (- (expt 2 rho)) entry)
           (< entry (expt 2 rho))
           (>= entry (lower i j rho m n))
           (check-lower-bound entry i j (1+ k) rho m n))))

(defund check-row (i j k rho m n row)
  (if (zp j)
      t
    (and (check-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
         (check-row i (1- j) k rho m n row))))

(defund check-rows (i k rho m n rows)
  (if (zp i)
      t
    (and (check-row (1- i) (expt 2 n) k rho m n (nth (1- i) rows))
         (check-rows (1- i) k rho m n rows))))

(defund admissible-srt-table-p (k rho m n table)
  (check-rows (expt 2 m) k rho m n table))


(local-defthm check-row-lemma
  (implies (and (natp j)
                (natp jj)
                (< jj j)
                (check-row i j k rho m n row))
           (check-entry i jj k rho m n (ifix (nth jj row))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-row))))

(local-defthm check-rows-lemma
  (implies (and (natp i)
                (natp ii)
                (< ii i)
                (check-rows i k rho m n rows))
           (check-row ii (expt 2 n) k rho m n (nth ii rows)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-rows))))

(local-defthm check-table-lemma
  (implies (and (natp m)
                (natp n)
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (admissible-srt-table-p k rho m n table))
           (check-entry i j k rho m n (lookup i j table)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lookup admissible-srt-table-p)
                  :use ((:instance check-rows-lemma (rows table) (ii i) (i (expt 2 m)))
                        (:instance check-row-lemma (row (nth i table)) (jj j) (j (expt 2 n)))))))

(local-defthm lemma-3-6-18
  (implies (and (integerp k)
                (integerp k1)
                (natp rho)
                (>= (1- k1) k))
           (<= (expt 2 (* (- 1 k1) rho))
               (expt 2 (- (* k rho)))))
  :rule-classes ())

(local-defthm lemma-3-6-19
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z1)
                (rationalp z2)
                (< x (+ y z1))
                (<= z1 z2))
           (< x (+ y z2)))
  :rule-classes ())

(local-defthm lemma-3-6-20
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (natp k1)
                (> k1 k)
                (< (PI0 I M)
                   (+ (EXPT 2 (- N))
                      (DELTA0 J N)
                      (EXPT 2 (* (- 1 K1) RHO)))))
           (< (PI0 I M)
              (+ (EXPT 2 (- N))
                 (DELTA0 J N)
                 (EXPT 2 (- (* K RHO))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-6-18
                        (:instance lemma-3-6-19 (x (PI0 I M))
                                                (y (+ (EXPT 2 (- N)) (DELTA0 J N)))
                                                (z1 (EXPT 2 (+ RHO (- (* K1 RHO)))))
                                                (z2 (EXPT 2 (- (* K RHO)))))))))

(local-defthm lemma-3-6-21
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (natp k1)
                (> k1 k)
                (sqrt-accessible-p i j k1 rho m n))
           (accessible-p i j k rho m n))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-6-20)
                  :in-theory (enable sqrt-accessible-p accessible-p))))

(defthm sqrt-accessible-accessible
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (bvecp i m)
                (bvecp j n)
                (natp k1)
                (> k1 k)
                (sqrt-accessible-p i j k1 rho m n))
           (accessible-p i j k rho m n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-3-6-20 (h 8)))
                  :in-theory (enable bvecp sqrt-accessible-p accessible-p))))

(local-defthm lemma-3-6-22
  (implies (and (integerp k)
                (integerp k1)
                (natp rho)
                (> k1 k))
           (>= (expt 2 (- (* (1+ k) rho)))
               (expt 2 (- (* k1 rho)))))
  :rule-classes ())

(local-defthm lemma-3-6-23
  (implies (and (integerp k)
                (integerp k1)
                (integerp h)
                (natp rho)
                (> k1 k))
           (>= (* (1- h) (1- h) (/ (expt 2 rho)) (expt 2 (- (* (1+ k) rho))))
               (* (1- h) (1- h) (/ (expt 2 rho)) (expt 2 (- (* k1 rho))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-6-22
                 (:instance converse-57 (x (1- h)))
                 (:instance *-weakly-monotonic (x (* (1- h) (1- h) (/ (expt 2 rho))))
                            (y (expt 2 (- (* k1 rho))))
                            (y+ (expt 2 (- (* (1+ k) rho)))))))))


(local-defthm lemma-3-6-24
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (natp k1)
                (> k1 k)
                (< (pi0 i m)
                   (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k1 rho))))))))
           (< (pi0 i m)
              (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* (1+ k) rho))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                 lemma-3-6-23
                 (:instance lemma-3-6-19 (x (PI0 I M))
                            (y (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n)))))
                            (z1 (* (1- h) (1- h) (/ (expt 2 rho)) (expt 2 (- (* k1 rho)))))
                            (z2 (* (1- h) (1- h) (/ (expt 2 rho)) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm lemma-3-6-25
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (natp k1)
                (> k1 k)
                (< (pi0 i m)
                   (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (* (1- h) (expt 2 (- (* k1 rho))))))))
           (< (pi0 i m)
              (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (* (1- h) (expt 2 (- (* (1+ k) rho))))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-6-23
                        (:instance lemma-3-6-19 (x (PI0 I M))
                                                (y (* (/ (1- h) (expt 2 rho)) (delta0 j n)))
                                                (z1 (* (1- h) (1- h) (/ (expt 2 rho)) (expt 2 (- (* k1 rho)))))
                                                (z2 (* (1- h) (1- h) (/ (expt 2 rho)) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm lemma-3-6-26
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (natp k1)
                (> k1 k)
                (check-lower-bound h i j (1+ k) rho m n))
           (check-lower-bound h i j k1 rho m n))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-lower-bound)
                           (jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4))
           :use (converse-39
                 lemma-3-6-24
                 lemma-3-6-25))))

(local-defthm lemma-3-6-27
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n))
                (not (= h (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m)))))
           (>= (1+ h)
               (cg (* (expt 2 rho)
                      (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                         (delta0 j n))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39)
                  :in-theory (enable lower))))

(local-defthm lemma-3-6-28
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n))
                (not (= h (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m)))))
           (>= (1+ h)
               (* (expt 2 rho)
                  (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                     (delta0 j n)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-6-27
                        (:instance cg-def (x (* (expt 2 rho) (/ (+ (pi0 i m) (/ (expt 2 (- m 3)))) (delta0 j n)))))))))

(local-defthm lemma-3-6-29
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n))
                (not (= h (1- (expt 2 rho))))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m)))))
           (>= (/ (* (1+ h) (delta0 j n)) (expt 2 rho))
               (+ (pi0 i m) (/ (expt 2 (- m 3))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-6-28
                        (:instance *-weakly-monotonic (x (/ (delta0 j n) (expt 2 rho)))
                                                      (y+ (1+ h))
                                                      (y (* (expt 2 rho)
                                                            (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                                               (delta0 j n)))))))))

(local-defthm lemma-3-6-30
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n))
                (not (= h (1- (expt 2 rho))))
                (>= i (expt 2 (1- m)))
                (not (= i (1- (expt 2 m)))))
           (>= (1+ h)
               (cg (* (expt 2 rho)
                      (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                         (+ (delta0 j n) (expt 2 (- n))))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39)
                  :in-theory (enable lower))))

(local-defthm lemma-3-6-31
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n))
                (not (= h (1- (expt 2 rho))))
                (>= i (expt 2 (1- m)))
                (not (= i (1- (expt 2 m)))))
           (>= (1+ h)
               (* (expt 2 rho)
                  (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                     (+ (delta0 j n) (expt 2 (- n)))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-6-30
                        (:instance cg-def (x (* (expt 2 rho) (/ (+ (pi0 i m) (/ (expt 2 (- m 3)))) (+ (delta0 j n) (expt 2 (- n)))))))))))

(local-defthm lemma-3-6-32
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n))
                (not (= h (1- (expt 2 rho))))
                (>= i (expt 2 (1- m)))
                (not (= i (1- (expt 2 m)))))
           (>= (/ (* (1+ h) (+ (delta0 j n) (expt 2 (- n)))) (expt 2 rho))
               (+ (pi0 i m) (/ (expt 2 (- m 3))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-6-31
                        (:instance *-weakly-monotonic (x (/ (+ (delta0 j n) (expt 2 (- n))) (expt 2 rho)))
                                                      (y+ (1+ h))
                                                      (y (* (expt 2 rho)
                                                            (/ (+ (pi0 i m) (/ (expt 2 (- m 3))))
                                                               (+ (delta0 j n) (expt 2 (- n)))))))))))

(local-defthm lemma-3-6-33
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (< h (expt 2 rho))
                (> h (- (expt 2 rho)))
                (>= h (lower i j rho m n)))
           (check-upper-bound h i j k rho m n))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-upper-bound)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
           :use (lemma-3-6-29
                 lemma-3-6-32
                 converse-76))))

(local-defthm lemma-3-6-34
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp i)
                (natp j)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (natp k1)
                (> k1 k)
                (check-entry i j k rho m n h))
           (check-sqrt-entry i j k1 rho m n h))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-entry check-entry)
                  :use ((:instance lemma-3-6-33 (k k1))
                        lemma-3-6-21
                        lemma-3-6-26))))

(defthm lemma-3-6-a
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (natp k1)
                (> k1 k)
                (admissible-srt-table-p k rho m n table))
           (admissible-for-iteration-p k1 rho m n table))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-entry check-div-entry check-entry)
                  :use ((:instance check-table-lemma (i (i-sqrt k1 rho m n table))
                                                     (j (j-sqrt k1 rho m n table)))
                        (:instance converse-36 (k k1))
                        (:instance lemma-3-6-34 (i (i-sqrt k1 rho m n table))
                                                (j (j-sqrt k1 rho m n table))
                                                (h (lookup (i-sqrt k1 rho m n table) (j-sqrt k1 rho m n table) table)))))))

(defthm admissible-srt-table-p-2-2-6-2
  (admissible-srt-table-p 2 2 6 2 (srt-table 2 6 2)))

(defthm admissible-srt-table-p-2-3-7-4
  (admissible-srt-table-p 2 3 7 4 (srt-table 3 7 4)))

(defthm admissible-srt-table-p-2-3-8-3
  (admissible-srt-table-p 2 3 8 3 (srt-table 3 8 3)))

(defthm admissible-for-iteration-p-2-2-6-2
  (implies (and (natp k)
                (> k 2))
           (admissible-for-iteration-p k 2 6 2 (srt-table 2 6 2)))
  :hints (("Goal" :use (:instance lemma-3-6-a (table (srt-table 2 6 2)) (m 6) (n 2) (rho 2) (k 2) (k1 k)))))

;;**********************************************************************************

(local-defthm local-lemma
  (implies (and (rationalp x)
                (rationalp y1)
                (rationalp y2)
                (rationalp z)
                (< x (+ y1 z))
                (< y1 y2))
           (< x (+ y2 z)))
  :rule-classes ())

(local-defthm rationalp-pi0
  (implies (and (integerp i)
                (integerp m))
           (rationalp (pi0 i m)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable pi0))))

(local-in-theory (disable i-bounds))

(encapsulate (((rho%%) => *) ((m%%) => *) ((n%%) => *) ((k%%) => *) ((table%%) => *))

(local (defun rho%% () 2))
(local (defun m%% () 6))
(local (defun n%% () 2))
(local (defun k%% () 2))
(local (defun table%% () (srt-table 2 6 2)))

(defthmd rho%%-constraint
  (not (zp (rho%%))))

(defthmd m%%-constraint
  (not (zp (m%%))))

(defthmd n%%-constraint
  (not (zp (n%%))))

(defthmd k%%-constraint
  (and (natp (k%%)) (> (k%%) 1)))

(defthm table%%-constraint
  (implies (and (natp k)
                (> k (k%%)))
           (admissible-for-iteration-p k (rho%%) (m%%) (n%%) (table%%)))
  :hints (("Goal" :in-theory (disable srt-table (table%%) (srt-table)))))

)

(defthm natp-rho%%
  (natp (rho%%))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use rho%%-constraint)))

(defthm natp-m%%
  (natp (m%%))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use m%%-constraint)))

(defthm natp-n%%
  (natp (n%%))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use n%%-constraint)))

(defthm natp-k%%
  (natp (k%%))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use k%%-constraint)))

(encapsulate (((x%%) => *) ((p%% *) => *) ((q%% *) => *) ((h%% *) => *) ((i%% *) => *) ((j%% *) => *))

(local (defun x%% () 1/2))

(local (mutual-recursion

(defun p%% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 2)))
  (if (zp k)
      (x%%)
    (- (* (expt 2 (rho%%)) (p%% (1- k)))
       (* (h%% k) (+ (* 2 (q%% (1- k))) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))))

(defun q%% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 2)))
  (if (zp k)
      0
    (+ (q%% (1- k)) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))

(defun h%% (k)
  (declare (xargs :measure (+ (* 3 (nfix k)) 1)))
  (lookup (i%% k) (j%% k) (table%%)))

(defun i%% (k)
  (declare (xargs :measure (* 3 (nfix k))))
  (if (zp k)
      ()
    (bits (fl (* (expt 2 (- (m%%) 2)) (p%% (1- k)))) (1- (m%%)) 0)))

(defun j%% (k)
  (declare (xargs :measure (* 3 (nfix k))))
  (if (zp k)
      ()
    (fl (* (expt 2 (n%%)) (1- (* 2 (q%% (1- k))))))))

))

(defthmd x%%-constraint
  (and (rationalp (x%%))
       (< 1/4 (x%%))
       (< (x%%) 1)))

(defthm p%%-def
  (equal (p%% k)
         (if (zp k)
             (x%%)
           (- (* (expt 2 (rho%%)) (p%% (1- k)))
              (* (h%% k) (+ (* 2 (q%% (1- k))) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))))
  :rule-classes (:definition))

(defthm q%%-def
  (equal (q%% k)
         (if (zp k)
             0
           (+ (q%% (1- k)) (* (expt 2 (- (* k (rho%%)))) (h%% k)))))
  :rule-classes (:definition))

(defthm integerp-h%%
  (integerp (h%% k))
  :rule-classes (:rewrite :type-prescription))

(defthmd h%%-def
  (implies (and (natp k)
                (> k (k%%)))
           (equal (h%% k)
                  (lookup (i%% k) (j%% k) (table%%))))
  :rule-classes (:definition))

(defun all-sqrt-accessible-p%% (k)
  (if (or (zp k) (<= k (k%%)))
      t
    (and (sqrt-accessible-p (i%% k) (j%% k) k (rho%%) (m%%) (n%%))
         (all-sqrt-accessible-p%% (1- k)))))

(defthmd i%%-constraint
  (implies (and (natp k)
                (> k (k%%))
                (rationalp (p%% (1- k)))
                (< (abs (p%% (1- k))) 2)
                (all-sqrt-accessible-p%% (1- k)))
           (and (bvecp (i%% k) (m%%))
                (<= (pi0 (i%% k) (m%%))
                    (p%% (1- k)))
                (< (p%% (1- k))
                   (+ (pi0 (i%% k) (m%%))
                      (/ (expt 2 (- (m%%) 3)))))))
  :hints (("Goal" :use (m%%-constraint
                        k%%-constraint
                        (:instance i-bounds (p (p%% (1- k))) (m (m%%)))
                        (:instance local-lemma (x (P%% (+ -1 K)))
                                               (y1 (EXPT 2 (+ 2 (- (M%%)))))
                                               (y2 (EXPT 2 (+ 3 (- (M%%)))))
                                               (z (pi0 (i%% k) (m%%))))))))

(defthmd j%%-constraint
  (implies (and (natp k)
                (> k (k%%))
                (rationalp (q%% (1- k)))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1))
           (and (bvecp (j%% k) (n%%))
                (<= (delta0 (j%% k) (n%%)) (* 2 (q%% (1- k))))
                (< (* 2 (q%% (1- k))) (+ (delta0 (j%% k) (n%%)) (expt 2 (- (n%%)))))))
  :hints (("Goal" :use (n%%-constraint (:instance j-bounds (d (* 2 (q%% (1- k)))) (n (n%%)))))))

)

(local-defthm rat-q%%
  (rationalp (q%% k))
  :hints (("Goal" :induct (natp-induct k)))
  :rule-classes (:rewrite :type-prescription))

(local-defthm rat-p%%
  (rationalp (p%% k))
  :hints (("Goal" :induct (natp-induct k)
                  :in-theory (enable x%%-constraint)))
  :rule-classes (:rewrite :type-prescription))

(local-defthm rat-x%%
  (rationalp (x%%))
  :hints (("Goal" :in-theory (enable x%%-constraint)))
  :rule-classes (:rewrite :type-prescription))

(local-defthm int-rho%%
  (integerp (rho%%))
  :hints (("Goal" :use (rho%%-constraint)))
  :rule-classes (:rewrite :type-prescription))

(local-defthm theorem-2-5
  (implies (and (not (zp (rho%%)))
                (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k)))))
           (< (abs (p%% (1- k))) 2))
  :hints (("Goal" :use (k%%-constraint
                        (:functional-instance lemma-3-3-9 (rho$$ rho%%)
                                                          (x$$ x%%)
                                                          (h$$ h%%)
                                                          (q$$ q%%)
                                                          (p$$ p%%)))))
  :rule-classes ())

(local-defthm theorem-2-20
  (implies (and (natp k)
                (>= k (k%%))
                (<= 1/2 (q%% k)))
           (iff (and (<= (- (* 2 (q%% k)))
                         (- (p%% k) (expt 2 (- (* k (rho%%))))))
                     (< (- (p%% k) (expt 2 (- (* k (rho%%)))))
                        (* 2 (q%% k))))
                (and (< (x%%) (* (+ (q%% k) (expt 2 (- (* k (rho%%)))))
                                 (+ (q%% k) (expt 2 (- (* k (rho%%)))))))
                     (>= (x%%) (* (- (q%% k) (expt 2 (- (* k (rho%%)))))
                                  (- (q%% k) (expt 2 (- (* k (rho%%))))))))))
  :rule-classes ()
  :hints (("Goal" :use (m%%-constraint
                        n%%-constraint
                        rho%%-constraint
                        k%%-constraint
                        (:functional-instance lemma-3-2-a-b (rho$$ rho%%)
                                                            (x$$ x%%)
                                                            (h$$ h%%)
                                                            (q$$ q%%)
                                                            (p$$ p%%))))))

(local-defthm theorem-2-6
  (implies (and (not (zp (rho%%)))
                (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k)))
           (and (equal (h%% k)
                       (lookup (i%% k) (j%% k) (table%%)))
                (bvecp (i%% k) (m%%))
                (<= (pi0 (i%% k) (m%%))
                    (p%% (1- k)))
                (< (p%% (1- k))
                   (+ (pi0 (i%% k) (m%%))
                      (/ (expt 2 (- (m%%) 3)))))
                (bvecp (j%% k) (n%%))
                (<= (delta0 (j%% k) (n%%)) (* 2 (q%% (1- k))))
                (< (* 2 (q%% (1- k))) (+ (delta0 (j%% k) (n%%)) (expt 2 (- (n%%)))))))
  :rule-classes ()
  :hints (("Goal" :use (theorem-2-5
                        h%%-def
                        i%%-constraint
                        j%%-constraint))))

(local-defthm theorem-2-7
  (implies (and (not (zp (rho%%)))
                (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k)))
           (and (< (h%% k) (expt 2 (rho%%)))
                (> (h%% k) (- (expt 2 (rho%%))))
                (< (p%% (1- k))
                   (* (/ (1+ (h%% k)) (expt 2 (rho%%)))
                      (+ (* 2 (q%% (1- k))) (* (1+ (h%% k)) (expt 2 (- (* k (rho%%))))))))
                (>= (p%% (1- k))
                    (* (/ (1- (h%% k)) (expt 2 (rho%%)))
                       (+ (* 2 (q%% (1- k))) (* (1- (h%% k)) (expt 2 (- (* k (rho%%))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (theorem-2-6
                 m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint
                 table%%-constraint
                 (:instance lemma-3-4 (m (m%%))
                            (n (n%%))
                            (rho (rho%%))
                            (table (table%%))
                            (p (p%% (1- k)))
                            (d (* 2 (q%% (1- k))))
                            (i (i%% k))
                            (j (j%% k))
                            (h (h%% k)))))))

(local-defthm theorem-2-8
  (implies (and (not (zp (rho%%)))
                (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k)))
           (and (<= (- (* 2 (q%% k)))
                    (- (p%% k) (expt 2 (- (* k (rho%%))))))
                (< (- (p%% k) (expt 2 (- (* k (rho%%)))))
                   (* 2 (q%% k)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (theorem-2-7
                 (:functional-instance lemma-3-2-b-c (rho$$ rho%%)
                                       (x$$ x%%)
                                       (h$$ h%%)
                                       (q$$ q%%)
                                       (p$$ p%%))))))

(local-defthm theorem-2-9
  (implies (and (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k)))
           (and (< (x%%) (* (+ (q%% k) (expt 2 (- (* k (rho%%)))))
                            (+ (q%% k) (expt 2 (- (* k (rho%%)))))))
                (>= (x%%) (* (- (q%% k) (expt 2 (- (* k (rho%%)))))
                             (- (q%% k) (expt 2 (- (* k (rho%%)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (theorem-2-8
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint
                 (:functional-instance lemma-3-2-a-b (rho$$ rho%%)
                                       (x$$ x%%)
                                       (h$$ h%%)
                                       (q$$ q%%)
                                       (p$$ p%%))))))

(local-defthm theorem-2-21
  (implies (<= 1/2 (q%% (k%%)))
           (iff (and (<= (- (* 2 (q%% (k%%))))
                         (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%))))))
                     (< (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                        (* 2 (q%% (k%%)))))
                (and (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                                 (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                     (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                                  (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%))))))))))
  :rule-classes ()
  :hints (("Goal" :use (k%%-constraint
                        (:instance theorem-2-20 (k (k%%)))))))

(local-defthm theorem-2-10
  (implies (and (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k)))
           (and (<= 1/2 (q%% k))
                (< (q%% k) 1)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (theorem-2-7
                 theorem-2-9
                 rho%%-constraint
                 m%%-constraint
                 n%%-constraint
                 x%%-constraint
                 k%%-constraint
                 (:functional-instance lemma-3-3-b (rho$$ rho%%)
                                       (x$$ x%%)
                                       (h$$ h%%)
                                       (q$$ q%%)
                                       (p$$ p%%))))))

(local-defthm theorem-2-11
  (implies (and (natp k)
                (> k (k%%))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k)))
           (and (<= 1/2 (q%% k))
                (< (q%% k) 1)
                (<= (- (* 2 (q%% k)))
                    (- (p%% k) (expt 2 (- (* k (rho%%))))))
                (< (- (p%% k) (expt 2 (- (* k (rho%%)))))
                   (* 2 (q%% k)))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint
                        theorem-2-10
                        theorem-2-8))))

(defthmd theorem-2-19
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (<= (abs (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%))))))
                    (* 2 (q%% (k%%))))
                (<= 1/2 (q%% (1- k)))
                (< (q%% (1- k)) 1)
                (<= (- (* 2 (q%% (1- k))))
                    (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%))))))
                (< (- (p%% (1- k)) (expt 2 (- (* (1- k) (rho%%)))))
                   (* 2 (q%% (1- k))))
                (all-sqrt-accessible-p%% (1- k))
                (natp k)
                (> k (k%%)))
           (all-sqrt-accessible-p%% k))
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :expand ((all-sqrt-accessible-p%% k))
                  :use (i%%-constraint
                        j%%-constraint
                        rho%%-constraint
                        m%%-constraint
                        n%%-constraint
                        theorem-2-5
                        (:instance sqrt-table-1 (i (i%% k)) (j (j%% k)) (rho (rho%%)) (m (m%%)) (n (n%%))
                                                (p (p%% (1- k))) (d (* 2 (q%% (1- k)))))))))

(local
 (encapsulate
  ()
  (local (in-theory (disable jared-disables-1
                             jared-disables-2
                             jared-disables-3
                             jared-disables-4)))
  (defthm theorem-2-12
    (implies (and (<= 1/2 (q%% (k%%)))
                  (< (q%% (k%%)) 1)
                  (<= (- (* 2 (q%% (k%%))))
                      (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%))))))
                  (< (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                     (* 2 (q%% (k%%))))
                  (natp k)
                  (>= k (k%%)))
             (and (<= 1/2 (q%% k))
                  (< (q%% k) 1)
                  (<= (- (* 2 (q%% k)))
                      (- (p%% k) (expt 2 (- (* k (rho%%))))))
                  (< (- (p%% k) (expt 2 (- (* k (rho%%)))))
                     (* 2 (q%% k)))
                  (all-sqrt-accessible-p%% k)))
    :rule-classes ()
    :hints (("Goal" :induct (natp-induct k))
            ("Subgoal *1/2" :use (k%%-constraint
                                  theorem-2-19
                                  theorem-2-11)
             :cases ((= k (k%%))))
            ("Subgoal *1/1" :use (k%%-constraint))))))

(defthm theorem-2-b
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (>= k (k%%)))
           (< (abs (p%% k)) 2))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (theorem-2-12
                 theorem-2-21
                 k%%-constraint
                 rho%%-constraint
                 (:instance theorem-2-5 (k (1+ k)))))))

(local-defthmd theorem-2-14
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (<= (- (* 2 (q%% (k%%))))
                    (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%))))))
                (< (- (p%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                   (* 2 (q%% (k%%))))
                (natp k)
                (>= k (k%%)))
           (equal (p%% k)
                  (* (expt 2 (* k (rho%%)))
                     (- (x%%) (* (q%% k) (q%% k))))))
  :hints (("Goal" :use (k%%-constraint
                        rho%%-constraint
                        (:functional-instance lemma-3-1 (rho$$ rho%%)
                                                        (x$$ x%%)
                                                        (h$$ h%%)
                                                        (q$$ q%%)
                                                        (p$$ p%%))))))

(defthm theorem-2-a
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                            (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (>= k (k%%)))
           (and (< (x%%) (* (+ (q%% k) (expt 2 (- (* k (rho%%)))))
                            (+ (q%% k) (expt 2 (- (* k (rho%%)))))))
                (>= (x%%) (* (- (q%% k) (expt 2 (- (* k (rho%%)))))
                             (- (q%% k) (expt 2 (- (* k (rho%%)))))))))
  :rule-classes ()
  :hints (("Goal" :use (theorem-2-12
                        theorem-2-20
                        theorem-2-21))))

(defthm theorem-2-b
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (>= k (k%%)))
           (< (abs (p%% k)) 2))
  :rule-classes ()
  :hints (("Goal" :use (theorem-2-12
                        theorem-2-21
                        k%%-constraint
                        rho%%-constraint
                        (:instance theorem-2-5 (k (1+ k)))))))

(defthmd theorem-2-c
  (implies (and (<= 1/2 (q%% (k%%)))
                (< (q%% (k%%)) 1)
                (< (x%%) (* (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                            (+ (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (>= (x%%) (* (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))
                             (- (q%% (k%%)) (expt 2 (- (* (k%%) (rho%%)))))))
                (natp k)
                (> k (k%%)))
           (sqrt-accessible-p (i%% k) (j%% k) k (rho%%) (m%%) (n%%)))
  :hints (("Goal" :in-theory (enable all-sqrt-accessible-p%%)
                  :use (theorem-2-12
                        theorem-2-21))))


;;**********************************************************************************

(local-defun pow2 (n)
  (if (zp n)
      0
    (+ 3 (pow2 (fl (/ n 2))))))

(local-defthm lemma-3-5-1
  (implies (and (not (zp n))
                (natp m)
                (> m (fl (/ n 2))))
           (> (* 8 m) n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (/ n 2)))
                        (:instance *-strongly-monotonic (x 8) (y (1- (/ n 2))) (y+ m))))))

(local-defthm lemma-3-5-2
  (implies (not (zp n))
           (> (expt 2 (pow2 n)) n))
  :rule-classes ()
  :hints (("Subgoal *1/2" :use ((:instance lemma-3-5-1 (m (expt 2 (pow2 (fl (/ n 2))))))))))

(local-defund k-witness (x)
  (pow2 (cg (/ x))))

(local-defthm lemma-3-5-3
  (implies (and (rationalp x)
                (> x 0))
           (and (natp (k-witness x))
                (> (expt 2 (k-witness x)) (/ x))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable k-witness)
                  :use ((:instance lemma-3-5-2 (n (cg (/ x))))))))

(local-defthm lemma-3-5-4
  (implies (and (rationalp x)
                (rationalp y)
                (> x 0)
                (> y 0))
           (iff (< x y) (< (/ y) (/ x))))
  :rule-classes ())

(local-defthm lemma-3-5-5
  (implies (and (rationalp x)
                (> x 0))
           (< (expt 2 (- (k-witness x))) x))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-3
                        (:instance lemma-3-5-4 (x (expt 2 (- (k-witness x)))) (y x))))))

(local-defthm lemma-3-5-6
  (implies (and (rationalp x)
                (> x 0))
           (natp (k-witness x)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (lemma-3-5-3
                        (:instance lemma-3-5-4 (x (expt 2 (- (k-witness x)))) (y x))))))

(local-defthm lemma-3-5-7
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (div-accessible-p i j m n))
           (> (pi0 i m)
              (+ (- (delta0 j n))
                 (- (/ (expt 2 n)))
                 (- (/ (expt 2 (- m 3))))
                 (expt 2 (- (k-witness (+ (pi0 i m) (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3))))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable div-accessible-p)
                  :use (converse-39
                        (:instance lemma-3-5-5 (x (+ (pi0 i m) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))))))))

(local-defthm lemma-3-5-8
  (implies (and (integerp a)
                (integerp b)
                (>= a b))
           (<= (expt 2 (- a)) (expt 2 (- b))))
  :rule-classes ())

(local-defthm lemma-3-5-9
  (implies (and (not (zp rho))
                (natp k))
           (<= k (* k rho)))
  :rule-classes ())

(local-defthm lemma-3-5-10
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (div-accessible-p i j m n)
                (natp k)
                (>= k (k-witness (+ (pi0 i m) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3))))))))
           (>= (expt 2 (- (k-witness (+ (pi0 i m) (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))))
               (expt 2 (- (* k rho)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-5-9
                        (:instance lemma-3-5-8 (a (* k rho))
                                               (b (k-witness (+ (pi0 i m) (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))))))))

(local-defthm lemma-3-5-11
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (div-accessible-p i j m n)
                (natp k)
                (>= k (k-witness (+ (pi0 i m) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3))))))))
           (>= (+ (- (delta0 j n))
                  (- (/ (expt 2 n)))
                  (- (/ (expt 2 (- m 3))))
                  (expt 2 (- (k-witness (+ (pi0 i m) (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3))))))))
               (+ (- (delta0 j n))
                  (- (/ (expt 2 n)))
                  (- (/ (expt 2 (- m 3))))
                  (expt 2 (- (* k rho))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-5-10))))

(local-defthm lemma-3-5-12
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (> x y)
                (>= y z))
           (> x z))
  :rule-classes ())

(local-defthm lemma-3-5-13
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (div-accessible-p i j m n)
                (natp k)
                (>= k (k-witness (+ (pi0 i m) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3))))))))
           (> (pi0 i m)
              (+ (- (delta0 j n))
                 (- (/ (expt 2 n)))
                 (- (/ (expt 2 (- m 3))))
                 (expt 2 (- (* k rho))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-5-7
                        lemma-3-5-11
                        (:instance lemma-3-5-12 (x (pi0 i m))
                                                (y (+ (- (delta0 j n))
                                                      (- (/ (expt 2 n)))
                                                      (- (/ (expt 2 (- m 3))))
                                                      (expt 2 (- (k-witness (+ (pi0 i m) (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3)))))))))
                                                (z (+ (- (delta0 j n))
                                                      (- (/ (expt 2 n)))
                                                      (- (/ (expt 2 (- m 3))))
                                                      (expt 2 (- (* k rho))))))))))

(local-defthm lemma-3-5-14
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (div-accessible-p i j m n)
                (natp k)
                (> k (k-witness (+ (pi0 i m) (+ (delta0 j n) (/ (expt 2 n)) (/ (expt 2 (- m 3))))))))
           (sqrt-accessible-p i j k rho m n))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        (:instance lemma-3-5-13 (k (1- k))))
                  :in-theory (enable div-accessible-p sqrt-accessible-p))))

(local-defthm lemma-3-5-15
  (implies (and (natp i)
                (natp j)
                (< i (expt 2 (m%%)))
                (< j (expt 2 (n%%)))
                (div-accessible-p i j (m%%) (n%%))
                (natp k)
                (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
           (let ((h (lookup i j (table%%))))
             (and (< (- (expt 2 (rho%%))) h)
                  (< h (expt 2 (rho%%)))
                  (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                  (check-lower-bound h i j k (rho%%) (m%%) (n%%)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-entry)
                  :use (table%%-constraint
                        rho%%-constraint
                        m%%-constraint
                        n%%-constraint
                        k%%-constraint
                        (:instance lemma-3-5-14 (rho (rho%%)) (m (m%%)) (n (n%%)))
                        (:instance check-sqrt-table-lemma (m (m%%)) (n (n%%)) (rho (rho%%)) (table (table%%)))))))

(local-defthm lemma-3-5-16
  (implies (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
           (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                  (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
                  (h (lookup i j (table%%))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (div-accessible-p i j (m%%) (n%%))
                  (not (and (< (- (expt 2 (rho%%))) h)
                            (< h (expt 2 (rho%%)))
                            (>= h (lower i j (rho%%) (m%%) (n%%)))
                            (<= h (upper i j (rho%%) (m%%) (n%%))))))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint
                        m%%-constraint
                        n%%-constraint
                        (:instance div-witness-lemma (m (m%%)) (n (n%%)) (rho (rho%%)) (table (table%%)))))))

(local-defthm lemma-3-5-17
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (natp k)
                  (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (< h (expt 2 (rho%%)))
                  (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                  (check-lower-bound h i j k (rho%%) (m%%) (n%%))
                  (not (and (>= h (lower i j (rho%%) (m%%) (n%%)))
                            (<= h (upper i j (rho%%) (m%%) (n%%))))))))

  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-16
                        (:instance lemma-3-5-15 (i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                                                (j (j-witness (rho%%) (m%%) (n%%) (table%%))))))))

(local-defthm lemma-3-5-18
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp i)
                (natp j)
                (natp k)
                (< i (expt 2 m))
                (< j (expt 2 n))
                (integerp h)
                (check-lower-bound h i j k rho m n)
                (= h (- 1 (expt 2 rho))))
           (<= h (upper i j rho m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound upper))))

(local-defthm lemma-3-5-19
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (< h (expt 2 rho)))
           (>= (* (1- h) (1- h) (expt 2 (- (* k rho))))
               0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance converse-57 (x (1- h)))))))

(local-defthm lemma-3-5-20
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (> (expt 2 rho) k)
                (> k (upper i j rho m n)))
           (and (> k (- 1 (expt 2 rho)))
                (if (>= i (expt 2 (1- m)))
                    (> (1- k)
                       (fl (* (expt 2 rho)
                              (/ (pi0 i m)
                                 (delta0 j n)))))
                  (> (1- k)
                     (fl (* (expt 2 rho)
                            (/ (pi0 i m)
                               (+ (delta0 j n) (/ (expt 2 n))))))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39)
                  :in-theory (enable upper))))

(local-defthm lemma-3-5-21
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (> (expt 2 rho) k)
                (> k (upper i j rho m n)))
           (and (> k (- 1 (expt 2 rho)))
                (if (>= i (expt 2 (1- m)))
                    (> (1- k)
                       (* (expt 2 rho)
                          (/ (pi0 i m)
                             (delta0 j n))))
                  (> (1- k)
                     (* (expt 2 rho)
                        (/ (pi0 i m)
                           (+ (delta0 j n) (/ (expt 2 n)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                 lemma-3-5-20
                 (:instance fl-unique
                            (x (* (expt 2 rho)
                                  (/ (pi0 i m)
                                     (+ (delta0 j n) (/ (expt 2 n))))))
                            (n (1- k)))
                 (:instance fl-unique
                            (x (* (expt 2 rho)
                                  (/ (pi0 i m)
                                     (+ (delta0 j n)))))
                            (n (1- k)))))))

(local-defthm converse-8
  (implies (and (rationalp dmin)
                (rationalp pmin)
                (rationalp h)
                (> h 0))
           (iff (< (* pmin h) (* dmin h))
                (< pmin dmin)))
  :rule-classes ())

(local-defthm lemma-3-5-22
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (> (1- k)
                   (* (expt 2 rho)
                      (/ (pi0 i m)
                         (delta0 j n)))))
           (> (* (/ (1- k) (expt 2 rho)) (delta0 j n))
              (pi0 i m)))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        (:instance converse-8
                                   (dmin (1- k))
                                   (h (/ (delta0 j n) (expt 2 rho)))
                                   (pmin (* (expt 2 rho)
                                            (/ (pi0 i m)
                                               (delta0 j n)))))))))

(local-defthm lemma-3-5-23
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (> (1- k)
                   (* (expt 2 rho)
                      (/ (pi0 i m)
                         (+ (delta0 j n) (expt 2 (- n)))))))
           (> (* (/ (1- k) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
              (pi0 i m)))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        (:instance converse-8
                                   (dmin (1- k))
                                   (h (/ (+ (delta0 j n) (expt 2 (- n))) (expt 2 rho)))
                                   (pmin (* (expt 2 rho)
                                            (/ (pi0 i m)
                                               (+ (delta0 j n) (expt 2 (- n)))))))))))

(local-defthm lemma-3-5-24
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp k)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) k)
                (> (expt 2 rho) k)
                (> k (upper i j rho m n)))
           (and (> k (- 1 (expt 2 rho))           )
                (if (>= i (expt 2 (1- m)))
                    (> (* (/ (1- k) (expt 2 rho)) (delta0 j n))
                       (pi0 i m))
                  (> (* (/ (1- k) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
                     (pi0 i m)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-21 lemma-3-5-22 lemma-3-5-23))))

(local-defthm lemma-3-5-25
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (< x y)
                (<= 0 z))
           (< x (+ y z)))
  :rule-classes ())

(local-defthm lemma-3-5-26
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (> h (upper i j rho m n))
                (>= i (expt 2 (1- m))))
            (> (* (/ (1- h) (expt 2 rho)) (delta0 j n))
               (pi0 i m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-3-5-24 (k h))))))

(local-defthm lemma-3-5-27
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (> h (upper i j rho m n))
                (>= i (expt 2 (1- m))))
            (> (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (* (1- h) (expt 2 (- (* k rho))))))
               (pi0 i m)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                 lemma-3-5-19
                 lemma-3-5-26
                 (:instance lemma-3-5-25 (x (pi0 i m))
                            (y (* (/ (1- h) (expt 2 rho)) (delta0 j n)))
                            (z (* (1- h) (1- h) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm lemma-3-5-28
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (check-lower-bound h i j k rho m n)
                (not (= h (- 1 (expt 2 rho))))
                (>= i (expt 2 (1- m))))
           (<= h (upper i j rho m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound)
                  :use (converse-39
                        lemma-3-5-27))))

(local-defthm lemma-3-5-29
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (> h (upper i j rho m n))
                (< i (expt 2 (1- m))))
            (> (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
               (pi0 i m)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-3-5-24 (k h))))))

(local-defthm lemma-3-5-30
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (> h (upper i j rho m n))
                (< i (expt 2 (1- m))))
            (> (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* k rho))))))
               (pi0 i m)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                 lemma-3-5-29
                 lemma-3-5-19
                 (:instance lemma-3-5-25 (x (pi0 i m))
                            (y (* (/ (1- h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n)))))
                            (z (* (1- h) (1- h) (expt 2 (- (* (+ 1 k) rho))))))))))

(local-defthm lemma-3-5-31
  (implies (and (natp m)
                (natp n)
                (natp rho)
                (natp k)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (check-lower-bound h i j k rho m n)
                (not (= h (- 1 (expt 2 rho)))))
           (<= h (upper i j rho m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound)
                  :use (converse-39
                        lemma-3-5-30
                        lemma-3-5-28))))

(local-defthm lemma-3-5-32
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (natp k)
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (< (- (expt 2 rho)) h)
                (> (expt 2 rho) h)
                (>= h (lower i j rho m n))
                (check-lower-bound h i j k rho m n))
           (<= h (upper i j rho m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-lower-bound)
                  :use (converse-39
                        lemma-3-5-18
                        lemma-3-5-31))))

(local-defthm lemma-3-5-33
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (natp k)
                  (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                  (< h (lower i j (rho%%) (m%%) (n%%))))))

  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-17
                        m%%-constraint
                        n%%-constraint
                        rho%%-constraint
                        k%%-constraint
                        (:instance lemma-3-5-32 (m (m%%)) (n (n%%)) (rho (rho%%)) (i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                                                (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
                                                (h (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))(j-witness (rho%%) (m%%) (n%%) (table%%))(table%%))))))))

(local-defthm lemma-3-5-3-a
  (implies (and (rationalp x)
                (> x 0)
                (natp k)
                (>= k (k-witness x)))
           (> (expt 2 k) (/ x)))
  :rule-classes ()
  :hints (("Goal" :use lemma-3-5-3)))

(local-defthm lemma-3-5-5-a
  (implies (and (rationalp x)
                (> x 0)
                (natp k)
                (>= k (k-witness x)))
           (< (expt 2 (- k)) x))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-3-a
                        (:instance lemma-3-5-4 (x (expt 2 (- k))) (y x))))))

(local-defthm lemma-3-5-34
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (> x y)
                (> z 0)
                (natp k)
                (> k (k-witness (/ (- x y) z))))
           (> x (+ y (* z (expt 2 (- k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-3-5-5-a (x (/ (- x y) z)))
                        (:instance *-strongly-monotonic (x z) (y (expt 2 (- k))) (y+ (/ (- x y) z)))))))

(local-defthm lemma-3-5-35
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (or (< i (expt 2 (1- (m%%))))
                    (= i (1- (expt 2 (m%%)))))
                (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                (< h (lower i j (rho%%) (m%%) (n%%))))
           (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
               (* (/ (1+ h) (expt 2 (rho%%)))
                  (+ (delta0 j (n%%)) (* (1+ h) (expt 2 (- (* k (rho%%)))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (lower check-upper-bound)
                                  (jared-disables-1 ;; 9.5 sec -> 1/2 sec
                                   jared-disables-2
                                   jared-disables-3
                                   jared-disables-4))
           :use (converse-39
                        m%%-constraint
                        n%%-constraint
                        rho%%-constraint))))

(local-defthm lemma-3-5-36
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0))
           (>= (* x x y) 0))
  :rule-classes ()
  :hints (("Goal" :use (converse-57))))

(local-defthm lemma-3-5-37
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (integerp h)
                (natp k)
                (> (* k (rho%%)) (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ h (expt 2 (rho%%))) (delta0 j (n%%))))
                                               (/ (* h h) (expt 2 (rho%%))))))
                (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                    (* (/ h (expt 2 (rho%%)))
                       (+ (delta0 j (n%%)) (* h (expt 2 (- (* k (rho%%)))))))))
           (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
               (* (/ h (expt 2 (rho%%))) (delta0 j (n%%)))))

  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 (:instance converse-39 (m (m%%)) (n (n%%)) (rho (rho%%)))
                 (:instance lemma-3-5-36 (x h) (y (/ (expt 2 (rho%%)))))
                 (:instance lemma-3-5-34 (k (* k (rho%%)))
                            (x (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))))
                            (y (* (/ h (expt 2 (rho%%))) (delta0 j (n%%))))
                            (z (/ (* h h) (expt 2 (rho%%)))))))))

(local-defthm lemma-3-5-38
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (integerp h)
                (or (< i (expt 2 (1- (m%%))))
                    (= i (1- (expt 2 (m%%)))))
                (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                (< h (lower i j (rho%%) (m%%) (n%%)))
                (natp k)
                (> (* k (rho%%)) (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                                               (/ (* (1+ h) (1+ h)) (expt 2 (rho%%)))))))
           (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
               (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))

  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 lemma-3-5-35
                 (:instance lemma-3-5-37 (h (1+ h)))))))

(local-defthm lemma-3-5-39
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (or (< i (expt 2 (1- (m%%))))
                      (= i (1- (expt 2 (m%%)))))
                  (natp k)
                  (> (* k (rho%%)) (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                                                 (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
                  (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))))

  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-5-33
                 m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint
                 (:instance lemma-3-5-38 (i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                            (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
                            (h (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))
                                       (j-witness (rho%%) (m%%) (n%%) (table%%))
                                       (table%%))))))))

(local-defthm lemma-3-5-40
  (implies (natp k)
           (<= k (* k (rho%%))))
  :rule-classes ()
  :hints (("Goal" :use rho%%-constraint)))

(local-defthm lemma-3-5-41
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (or (< i (expt 2 (1- (m%%))))
                      (= i (1- (expt 2 (m%%)))))
                  (natp k)
                  (> k (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                                                 (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
                  (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-5-39
                 lemma-3-5-40
                 m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint))))

(local-defund foo (k i j h)
  (and (natp k)
       (> k (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                          (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
       (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3))))))))))

(local-defthm lemma-3-5-42
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (or (< i (expt 2 (1- (m%%))))
                      (= i (1- (expt 2 (m%%)))))
                  (foo k i j h))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))))
  :rule-classes ()
  :hints (("Goal" :expand ((:free (k i j h) (foo k i j h)))
                  :in-theory (theory 'minimal-theory)
                  :use (lemma-3-5-41))))

(local-defthm lemma-3-5-43
  (let ((k (1+ (max (max (k%%)
                         (k-witness (+ (pi0 i (m%%))
                                       (delta0 j (n%%))
                                       (/ (expt 2 (n%%)))
                                       (/ (expt 2 (- (m%%) 3))))))
                    (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                                     (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                                  (/ (* (1+ h) (1+ h)) (expt 2 (rho%%)))))))))
    (and (natp k)
         (> k (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
            (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
         (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3))))))))))
  :rule-classes ()
  :hints (("Goal" :use (m%%-constraint
                        n%%-constraint
                        rho%%-constraint
                        k%%-constraint))))

(local-defund bar (i j h)
  (1+ (max (max (k%%)
                (k-witness (+ (pi0 i (m%%))
                              (delta0 j (n%%))
                              (/ (expt 2 (n%%)))
                              (/ (expt 2 (- (m%%) 3))))))
           (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                            (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                         (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))))

(local-defthm lemma-3-5-44
  (foo (bar i j h) i j h)
  :hints (("Goal" :expand ((:free (k i j h) (foo k i j h)) (:free (i j h) (bar i j h)))
                  :in-theory (theory 'minimal-theory)
                  :use (lemma-3-5-43))))

(local-defthm lemma-3-5-45
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (or (< i (expt 2 (1- (m%%))))
                      (= i (1- (expt 2 (m%%))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-3-5-42
                                   (k (bar (i-witness (rho%%) (m%%) (n%%) (table%%))
                                           (j-witness (rho%%) (m%%) (n%%) (table%%))
                                           (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))
                                                   (j-witness (rho%%) (m%%) (n%%) (table%%))
                                                   (table%%)))))))))

(local-defthm lemma-3-5-46
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m))))
                (< h (lower i j rho m n)))
           (< (1+ h) (/ (* (expt 2 rho) (+ (pi0 i m) (expt 2 (- 3 m)))) (delta0 j n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lower)
                  :use (converse-39
                        (:instance cg-def (x (/ (* (expt 2 rho) (+ (pi0 i m) (expt 2 (- 3 m)))) (delta0 j n))))))))

(local-defthm lemma-3-5-47
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (or (< i (expt 2 (1- m)))
                    (= i (1- (expt 2 m))))
                (< h (lower i j rho m n)))
           (< (* (/ (1+ h) (expt 2 rho)) (delta0 j n))
              (+ (pi0 i m) (expt 2 (- 3 m)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-5-46
                        (:instance *-strongly-monotonic (x (* (/ (expt 2 rho)) (delta0 j n)))
                                                        (y (1+ h))
                                                        (y+ (/ (* (expt 2 rho) (+ (pi0 i m) (expt 2 (- 3 m)))) (delta0 j n))))))))

(local-defthm lemma-3-5-48
  (let ((i (i-witness (rho%%) (m%%) (n%%) (table%%))))
    (implies (or (< i (expt 2 (1- (m%%))))
                 (= i (1- (expt 2 (m%%)))))
             (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-45
                        m%%-constraint
                        n%%-constraint
                        rho%%-constraint
                        (:instance lemma-3-5-47 (m (m%%)) (n (n%%)) (rho (rho%%))
                                                (h (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))
                                                           (j-witness (rho%%) (m%%) (n%%) (table%%))
                                                           (table%%)))
                                                (i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                                                (j (j-witness (rho%%) (m%%) (n%%) (table%%))))))))


(local-defthm lemma-3-5-49
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (>= i (expt 2 (1- (m%%))))
                (not (= i (1- (expt 2 (m%%)))))
                (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                (< h (lower i j (rho%%) (m%%) (n%%))))
           (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
               (* (/ (1+ h) (expt 2 (rho%%)))
                  (+ (delta0 j (n%%)) (expt 2 (- (n%%))) (* (1+ h) (expt 2 (- (* k (rho%%)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (lower check-upper-bound)
                           (jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4))
                  :use (converse-39
                        m%%-constraint
                        n%%-constraint
                        rho%%-constraint))))

(local-defthm lemma-3-5-50
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (integerp h)
                (natp k)
                (> (* k (rho%%)) (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ h (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                                               (/ (* h h) (expt 2 (rho%%))))))
                (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                    (* (/ h (expt 2 (rho%%)))
                       (+ (delta0 j (n%%)) (expt 2 (- (n%%))) (* h (expt 2 (- (* k (rho%%)))))))))
           (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
               (* (/ h (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))

  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 (:instance converse-39 (m (m%%)) (n (n%%)) (rho (rho%%)))
                 (:instance lemma-3-5-36 (x h) (y (/ (expt 2 (rho%%)))))
                 (:instance lemma-3-5-34 (k (* k (rho%%)))
                            (x (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))))
                            (y (* (/ h (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                            (z (/ (* h h) (expt 2 (rho%%)))))))))

(local-defthm lemma-3-5-51
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (integerp h)
                (>= i (expt 2 (1- (m%%))))
                (not (= i (1- (expt 2 (m%%)))))
                (check-upper-bound h i j k (rho%%) (m%%) (n%%))
                (< h (lower i j (rho%%) (m%%) (n%%)))
                (natp k)
                (> (* k (rho%%)) (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                                               (/ (* (1+ h) (1+ h)) (expt 2 (rho%%)))))))
           (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
               (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))

  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 lemma-3-5-49
                 (:instance lemma-3-5-50 (h (1+ h)))))))

(local-defthm lemma-3-5-52
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (>= i (expt 2 (1- (m%%))))
                  (not (= i (1- (expt 2 (m%%)))))
                  (natp k)
                  (> (* k (rho%%)) (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                                                 (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
                  (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))))

  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-5-33
                 m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint
                 (:instance lemma-3-5-51 (i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                            (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
                            (h (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))
                                       (j-witness (rho%%) (m%%) (n%%) (table%%))
                                       (table%%))))))))

(local-defthm lemma-3-5-53
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (>= i (expt 2 (1- (m%%))))
                  (not (= i (1- (expt 2 (m%%)))))
                  (natp k)
                  (> k (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                                                 (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
                  (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3)))))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (lemma-3-5-52
                 lemma-3-5-40
                 m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint))))

(local-defund foo1 (k i j h)
  (and (natp k)
       (> k (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                          (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
       (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3))))))))))

(local-defthm lemma-3-5-54
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (>= i (expt 2 (1- (m%%))))
                  (not (= i (1- (expt 2 (m%%)))))
                  (foo1 k i j h))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))))
  :rule-classes ()
  :hints (("Goal" :expand ((:free (k i j h) (foo1 k i j h)))
                  :in-theory (theory 'minimal-theory)
                  :use (lemma-3-5-53))))

(local-defthm lemma-3-5-55
  (let ((k (1+ (max (max (k%%)
                         (k-witness (+ (pi0 i (m%%))
                                       (delta0 j (n%%))
                                       (/ (expt 2 (n%%)))
                                       (/ (expt 2 (- (m%%) 3))))))
                    (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                                     (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                                  (/ (* (1+ h) (1+ h)) (expt 2 (rho%%)))))))))
    (and (natp k)
         (> k (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
            (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
         (> k (max (k%%) (k-witness (+ (pi0 i (m%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))) (/ (expt 2 (- (m%%) 3))))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (m%%-constraint
                 n%%-constraint
                 rho%%-constraint
                 k%%-constraint))))

(local-defund bar1 (i j h)
  (1+ (max (max (k%%)
                (k-witness (+ (pi0 i (m%%))
                              (delta0 j (n%%))
                              (/ (expt 2 (n%%)))
                              (/ (expt 2 (- (m%%) 3))))))
           (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                            (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                         (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))))

(local-defthm lemma-3-5-56
  (foo1 (bar1 i j h) i j h)
  :hints (("Goal" :expand ((:free (k i j h) (foo1 k i j h)) (:free (i j h) (bar1 i j h)))
                  :in-theory (theory 'minimal-theory)
                  :use (lemma-3-5-55))))

(local-defthm lemma-3-5-57
  (let* ((i (i-witness (rho%%) (m%%) (n%%) (table%%)))
         (j (j-witness (rho%%) (m%%) (n%%) (table%%)))
         (h (lookup i j (table%%))))
    (implies (and (not (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%)))
                  (>= i (expt 2 (1- (m%%))))
                  (not (= i (1- (expt 2 (m%%))))))
             (and (natp i)
                  (< i (expt 2 (m%%)))
                  (natp j)
                  (< j (expt 2 (n%%)))
                  (< (- (expt 2 (rho%%))) h)
                  (> (expt 2 (rho%%)) h)
                  (< h (lower i j (rho%%) (m%%) (n%%)))
                  (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                      (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-3-5-54
                                   (k (bar1 (i-witness (rho%%) (m%%) (n%%) (table%%))
                                           (j-witness (rho%%) (m%%) (n%%) (table%%))
                                           (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))
                                                   (j-witness (rho%%) (m%%) (n%%) (table%%))
                                                   (table%%)))))))))

(local-defthm lemma-3-5-58
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (>= i (expt 2 (1- m)))
                (not (= i (1- (expt 2 m))))
                (< h (lower i j rho m n)))
           (< (1+ h) (/ (* (expt 2 rho) (+ (pi0 i m) (expt 2 (- 3 m)))) (+ (delta0 j n) (expt 2 (- n))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lower)
                  :use (converse-39
                        (:instance cg-def (x (/ (* (expt 2 rho) (+ (pi0 i m) (expt 2 (- 3 m)))) (+ (delta0 j n) (expt 2 (- n))))))))))

(local-defthm lemma-3-5-59
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (integerp h)
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (>= i (expt 2 (1- m)))
                (not (= i (1- (expt 2 m))))
                (< h (lower i j rho m n)))
           (< (* (/ (1+ h) (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n))))
              (+ (pi0 i m) (expt 2 (- 3 m)))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-5-58
                        (:instance *-strongly-monotonic (x (* (/ (expt 2 rho)) (+ (delta0 j n) (expt 2 (- n)))))
                                                        (y (1+ h))
                                                        (y+ (/ (* (expt 2 rho) (+ (pi0 i m) (expt 2 (- 3 m))))
                                                               (+ (delta0 j n) (expt 2 (- n))))))))))

(defthm lemma-3-5
  (admissible-div-table-p (rho%%) (m%%) (n%%) (table%%))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-5-48
                        lemma-3-5-57
                        m%%-constraint
                        n%%-constraint
                        rho%%-constraint
                        (:instance lemma-3-5-59 (m (m%%)) (n (n%%)) (rho (rho%%))
                                                (h (lookup (i-witness (rho%%) (m%%) (n%%) (table%%))
                                                           (j-witness (rho%%) (m%%) (n%%) (table%%))
                                                           (table%%)))
                                                (i (i-witness (rho%%) (m%%) (n%%) (table%%)))
                                                (j (j-witness (rho%%) (m%%) (n%%) (table%%))))))))

;;**********************************************************************************

(encapsulate (((xtable%%) => *))

(local (defund xtable-entry (i j)
  (if (and (> (pi0 i (m%%))
              (- (+ (delta0 j (n%%))
                    (expt 2 (- (n%%)))
                    (expt 2 (- 3 (m%%))))))
           (<= (pi0 i (m%%))
               (- (expt 2 (- (* (k%%) (rho%%))))
                  (+ (delta0 j (n%%))
                     (expt 2 (- (n%%)))
                     (expt 2 (- 3 (m%%)))))))
      (- 1 (expt 2 (rho%%)))
    (lookup i j (table%%)))))

(local (defun xtable-row (i j)
  (declare (xargs :measure (nfix (- (expt 2 (n%%)) j))))
  (if (and (natp j)
           (< j (expt 2 (n%%))))
      (cons (xtable-entry i j)
            (xtable-row i (1+ j)))
    ())))

(local (defun xtable-rows (i)
  (declare (xargs :measure (nfix (- (expt 2 (m%%)) i))))
  (if (and (natp i)
           (< i (expt 2 (m%%))))
      (cons (xtable-row i 0)
            (xtable-rows (1+ i)))
    ())))

(local (defund xtable%% ()
  (xtable-rows 0)))

(local (defun xtable-induct (j k)
  (if (zp j)
      k
    (xtable-induct (1- j) (1+ k)))))

(local (defthmd xtable-1
  (implies (and (natp j)
                (natp k)
                (< (+ j k) (expt 2 (n%%))))
           (equal (nth j (xtable-row i k))
                  (xtable-entry i (+ j k))))
  :hints (("Goal" :induct (xtable-induct j k))
          ("Subgoal *1/2" :expand ((xtable-row i k)))
          ("Subgoal *1/1" :expand ((xtable-row i k))))))

(local (defthmd xtable-2
  (implies (and (natp i)
                (natp k)
                (< (+ i k) (expt 2 (m%%))))
           (equal (nth i (xtable-rows k))
                  (xtable-row (+ i k) 0)))
  :hints (("Goal" :induct (xtable-induct i k))
          ("Subgoal *1/1" :expand ((xtable-rows k))))))

(local (defthmd xtable-3
  (implies (and (natp j)
                (< j (expt 2 (n%%))))
           (equal (nth j (xtable-row i 0))
                  (xtable-entry i j)))
  :hints (("Goal" :use (:instance xtable-1 (k 0))))))

(local (defthmd xtable-4
  (implies (and (natp i)
                (< i (expt 2 (m%%))))
           (equal (nth i (xtable-rows 0))
                  (xtable-row i 0)))
  :hints (("Goal" :use (:instance xtable-2 (k 0))))))

(local (defthm xtable-5
  (integerp (xtable-entry i j))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable xtable-entry)))))

(local (defthmd xtable-6
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
           (equal (lookup i j (xtable%%))
                  (xtable-entry i j)))
  :hints (("Goal" :in-theory (enable lookup xtable%%)
                  :use (xtable-4 xtable-3)))))

(defthmd xtable-def
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
           (equal (lookup i j (xtable%%))
                  (if (and (> (pi0 i (m%%))
                           (- (+ (delta0 j (n%%))
                                 (expt 2 (- (n%%)))
                                 (expt 2 (- 3 (m%%))))))
                           (<= (pi0 i (m%%))
                               (- (expt 2 (- (* (k%%) (rho%%))))
                                  (+ (delta0 j (n%%))
                                     (expt 2 (- (n%%)))
                                     (expt 2 (- 3 (m%%)))))))
                      (- 1 (expt 2 (rho%%)))
                    (lookup i j (table%%)))))
  :hints (("Goal" :in-theory (enable xtable-entry)
                  :use (xtable-6))))

)

(local-defund i-srt-aux (i k rho m n table)
  (if (zp i)
      ()
    (if (check-row (1- i) (expt 2 n) k rho m n (nth (1- i) table))
        (i-srt-aux (1- i) k rho m n table)
      (1- i))))

(local-defund i-srt (k rho m n table)
  (i-srt-aux (expt 2 m) k rho m n table))

(local-defund j-srt-aux (i j k rho m n row)
  (if (zp j)
      ()
    (if (check-entry i (1- j) k rho m n (ifix (nth (1- j) row)))
        (j-srt-aux i (1- j) k rho m n row)
      (1- j))))

(local-defund j-srt (k rho m n table)
  (let ((i (i-srt k rho m n table)))
    (j-srt-aux i (expt 2 n) k rho m n (nth i table))))

(local-defthm xtable-7
  (implies (and (natp i)
                (not (check-rows i k rho m n table)))
           (let ((w (i-srt-aux i k rho m n table)))
             (and (natp w)
                  (< w i)
                  (not (check-row w (expt 2 n) k rho m n (nth w table))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable i-srt-aux check-rows))))

(local-defthm xtable-8
  (implies (and (natp m)
                (not (admissible-srt-table-p k rho m n table)))
           (let ((i (i-srt k rho m n table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (not (check-row i (expt 2 n) k rho m n (nth i table))))))
  :rule-classes ()
  :hints (("Goal" :use (:instance xtable-7 (i (expt 2 m)))
                  :in-theory (enable i-srt admissible-srt-table-p))))

(local-defthm xtable-9
  (implies (and (natp j)
                (not (check-row i j k rho m n row)))
           (let ((w (j-srt-aux i j k rho m n row)))
             (and (natp w)
                  (< w j)
                  (not (check-entry i w k rho m n (ifix (nth w row)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable j-srt-aux check-row))))

(local-defthm xtable-10
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (not (admissible-srt-table-p k rho m n table)))
           (let* ((i (i-srt k rho m n table))
                  (j (j-srt k rho m n table))
                  (h (lookup i j table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (not (check-entry i j k rho m n h)))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-8
                        (:instance xtable-9 (i (i-srt k rho m n table))
                                            (j (expt 2 n))
                                            (row (nth (i-srt k rho m n table) table))))
                  :in-theory (enable lookup j-srt))))

(local-defthm xtable-11
  (implies (and (not (zp m))
                (not (zp n))
                (not (zp rho))
                (not (zp k))
                (not (admissible-srt-table-p k rho m n table)))
           (let* ((i (i-srt k rho m n table))
                  (j (j-srt k rho m n table))
                  (h (lookup i j table)))
             (and (natp i)
                  (< i (expt 2 m))
                  (natp j)
                  (< j (expt 2 n))
                  (accessible-p i j k rho m n)
                  (not (and (integerp h)
                            (< (- (expt 2 rho)) h)
                            (< h (expt 2 rho))
                            (>= h (lower i j rho m n))
                            (check-lower-bound h i j (1+ k) rho m n))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-10)
                  :in-theory (enable check-entry))))

(local-defthm xtable-12
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (= h (lookup i j (xtable%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (= h (- 1 (expt 2 (rho%%)))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-def)
                  :in-theory (enable accessible-p))))

(local-defthm xtable-13
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (<= (pi0 i (m%%)) (- (expt 2 (- 3 (m%%))))))
  :rule-classes ()
  :hints (("Goal" :use (k%%-constraint rho%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-14
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (not (or (< i (expt 2 (1- (m%%))))
                   (= i (1- (expt 2 (m%%)))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-13 m%%-constraint)
                  :in-theory (enable pi0))))

(local-defthm xtable-15
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (< (lower i j (rho%%) (m%%) (n%%))
             (* (expt 2 (rho%%))
                (/ (+ (pi0 i (m%%)) (/ (expt 2 (- (m%%) 3))))
                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-14 rho%%-constraint m%%-constraint n%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))
                        (:instance cg-def (x (* (expt 2 (rho%%))
                                                (/ (+ (pi0 i (m%%)) (/ (expt 2 (- (m%%) 3))))
                                                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%)))))))))
                  :in-theory (enable lower))))

(local-defthm xtable-16
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (<= (* (expt 2 (rho%%))
                 (/ (+ (pi0 i (m%%)) (/ (expt 2 (- (m%%) 3))))
                    (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))
              (* (expt 2 (rho%%))
                 (/ (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))))
                    (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint m%%-constraint n%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))
                        (:instance *-weakly-monotonic (x (/ (expt 2 (rho%%)) (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))
                                                      (y (+ (pi0 i (m%%)) (/ (expt 2 (- (m%%) 3)))))
                                                      (y+ (- (expt 2 (- (* (k%%) (rho%%))))
                                                             (+ (delta0 j (n%%))
                                                                (expt 2 (- (n%%)))))))))))

(local-defthm xtable-17
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (< (lower i j (rho%%) (m%%) (n%%))
             (* (expt 2 (rho%%))
                (/ (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))))
                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (xtable-15 xtable-16 rho%%-constraint m%%-constraint n%%-constraint))))

(local-defthm xtable-18
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
          (= (* (expt 2 (rho%%))
                (/ (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))))
                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))
             (- (/ (expt 2 (* (- 1 (k%%)) (rho%%)))
                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%)))))
                (expt 2 (rho%%)))))
  :rule-classes ()
  :hints (("Goal" :use (k%%-constraint rho%%-constraint m%%-constraint n%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-19
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
          (< (expt 2 (* (- 1 (k%%)) (rho%%)))
             (+ (delta0 j (n%%)) (/ (expt 2 (n%%))))))
  :rule-classes ()
  :hints (("Goal" :use (k%%-constraint rho%%-constraint m%%-constraint n%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-20
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
          (< (/ (expt 2 (* (- 1 (k%%)) (rho%%)))
                (+ (delta0 j (n%%)) (/ (expt 2 (n%%)))))
             1))
  :rule-classes ()
  :hints (("Goal" :use (xtable-19 k%%-constraint rho%%-constraint m%%-constraint n%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-21
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (< (lower i j (rho%%) (m%%) (n%%))
             (- (/ (expt 2 (* (- 1 (k%%)) (rho%%)))
                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%)))))
                (expt 2 (rho%%)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (xtable-17 xtable-18 rho%%-constraint m%%-constraint n%%-constraint))))

(local-defthm xtable-22
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (< (- (/ (expt 2 (* (- 1 (k%%)) (rho%%)))
                   (+ (delta0 j (n%%)) (/ (expt 2 (n%%)))))
                (expt 2 (rho%%)))
             (- 1 (expt 2 (rho%%)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (xtable-20))))

(local-defthm xtable-23
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (<= (pi0 i (m%%))
                    (- (expt 2 (- (* (k%%) (rho%%))))
                       (+ (delta0 j (n%%))
                          (expt 2 (- (n%%)))
                          (expt 2 (- 3 (m%%)))))))
          (< (lower i j (rho%%) (m%%) (n%%))
             (- 1 (expt 2 (rho%%)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (xtable-21 xtable-22 rho%%-constraint m%%-constraint n%%-constraint))))

(local-defthm xtable-24
  (let* ((i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
         (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
    (implies (<= (pi0 i (m%%))
                 (- (expt 2 (- (* (k%%) (rho%%))))
                    (+ (delta0 j (n%%))
                       (expt 2 (- (n%%)))
                       (expt 2 (- 3 (m%%))))))
             (admissible-srt-table-p (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance xtable-12 (i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
                                             (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
                                             (h (lookup (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))
                                                        (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))
                                                        (xtable%%))))
                        (:instance xtable-23 (i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
                                             (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
                        (:instance xtable-11 (k (k%%)) (rho (rho%%)) (m (m%%)) (n (n%%)) (table (xtable%%))))
                  :in-theory (enable check-lower-bound))))

(local-defthm xtable-25
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (equal (lookup i j (xtable%%))
                 (lookup i j (table%%))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable xtable-def))))

(local-defthm xtable-26
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (check-sqrt-entry i j (1+ (k%%)) (rho%%) (m%%) (n%%) (lookup i j (xtable%%))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-25 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance check-sqrt-table-lemma (m (m%%)) (n (n%%)) (rho (rho%%)) (k (1+ (k%%))) (table (table%%)))))))

(local-defthm xtable-27
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (and (< (- (expt 2(rho%%))) h)
                 (< h (expt 2 (rho%%)))
                 (check-upper-bound h i j (1+ (k%%)) (rho%%) (m%%) (n%%))
                 (check-lower-bound h i j (1+ (k%%)) (rho%%) (m%%) (n%%)))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-26 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint)
                  :in-theory (enable check-sqrt-entry sqrt-accessible-p accessible-p))))

(local-defthm xtable-28
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (= h (1- (expt 2 (rho%%))))
                     (check-entry i j (k%%) (rho%%) (m%%) (n%%) (lookup i j (xtable%%))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-27 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint)
                  :in-theory (enable check-entry lower))))

(local-defthm xtable-29
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (>= (pi0 i (m%%)) (delta0 j (n%%))))
           (< i (expt 2 (1- (m%%)))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint m%%-constraint n%%-constraint
                        (:instance *-strongly-monotonic (x (expt 2 (- 2 (m%%)))) (y i) (y+ (expt 2 (m%%))))
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%))))
                  :in-theory (enable pi0))))

(local-defthm xtable-30
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (>= (pi0 i (m%%)) (delta0 j (n%%)))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (+ (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))
                            (* (1+ h) (1+ h) (expt 2 (- (* (+ 2 (k%%)) (rho%%))))))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-27 xtable-29 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint)
                  :in-theory (enable check-upper-bound))))

(local-defthm xtable-31
  (implies (and (integerp h)
                (rationalp x)
                (>= x 0)
                (<= (abs h) (expt 2 (rho%%))))
            (<= (* h h x)
               (* (expt 2 (* 2 (rho%%))) x)))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint k%%-constraint
                        (:instance converse-66 (x h) (y (expt 2 (rho%%))))
                        (:instance *-weakly-monotonic (y (* h h))
                                                      (y+ (expt 2 (rho%%))))))))

(local-defthm xtable-32
  (implies (and (integerp h)
                (<= (abs h) (expt 2 (rho%%))))
            (<= (* h h (expt 2 (- (* (+ 2 (k%%)) (rho%%)))))
               (expt 2 (- (* (k%%) (rho%%))))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint k%%-constraint
                        (:instance xtable-31 (x (expt 2 (- (* (+ 2 (k%%)) (rho%%))))))))))

(local-defthm xtable-33
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (<= (* (1+ h) (1+ h) (expt 2 (- (* (+ 2 (k%%)) (rho%%)))))
                (expt 2 (- (* (k%%) (rho%%)))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-27 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance xtable-32 (h (1+ (lookup i j (xtable%%)))))))))

(local-defthm xtable-34
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (<= (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))
                         (* (- 1 (expt 2 (- (rho%%)))) (delta0 j (n%%)))))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint m%%-constraint n%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))
                        (:instance *-weakly-monotonic (x (/ (delta0 j (n%%)) (expt 2 (rho%%))))
                                                      (y (1+ (lookup i j (xtable%%))))
                                                      (y+ (1- (expt 2 (rho%%)))))))))

(local-defthm xtable-35
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (>= (pi0 i (m%%)) (delta0 j (n%%)))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (+ (expt 2 (- (* (k%%) (rho%%))))
                            (* (- 1 (expt 2 (- (rho%%)))) (delta0 j (n%%))))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-30 xtable-33 xtable-34 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint)
                  :in-theory (theory 'minimal-theory))))

(local-defthm xtable-36
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (>= (pi0 i (m%%)) (delta0 j (n%%)))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (+ (delta0 j (n%%))
                            (* (expt 2 (- (rho%%)))
                               (- (expt 2 (* (- 1 (k%%)) (rho%%)))
                                  (delta0 j (n%%)))))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-35 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint))))

(local-defthm xtable-37
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
           (<= (expt 2 (* (- 1 (k%%)) (rho%%)))
               (delta0 j (n%%))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-38
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%))))
           (<= (* (expt 2 (- (rho%%)))
                  (- (expt 2 (* (- 1 (k%%)) (rho%%)))
                     (delta0 j (n%%))))
               0))
  :rule-classes ()
  :hints (("Goal" :use (xtable-37 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance *-weakly-monotonic (x (expt 2 (- (rho%%))))
                                                       (y (- (expt 2 (* (- 1 (k%%)) (rho%%))) (delta0 j (n%%))))
                                                       (y+ 0))
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-39
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (>= (pi0 i (m%%)) (delta0 j (n%%)))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (delta0 j (n%%))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (xtable-36 xtable-38 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint))))

(local-defthm xtable-40
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (< (pi0 i (m%%)) (delta0 j (n%%))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-39 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint))))

(local-defthm xtable-41
  (implies (and (integerp k)
                (> k (k%%)))
           (<= (expt 2 (* (- 1 k) (rho%%)))
               (expt 2 (- (* (k%%) (rho%%))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-40 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint)
                  :in-theory (enable accessible-p sqrt-accessible-p))))

(local-defthm xtable-42
  (implies (and (rationalp x1)
                (rationalp x1)
                (rationalp y)
                (rationalp z)
                (<= x1 x2)
                (< (+ x2 y) z))
           (< (+ x2 y) z))
  :rule-classes ())

(local-defthm xtable-43
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (integerp k)
                (> k (k%%))
                (< (+ (EXPT 2 (- (* (K%%) (RHO%%))))
                      (- (+ (DELTA0 J (N%%))
                            (EXPT 2 (- (N%%)))
                            (EXPT 2 (+ 3 (- (M%%)))))))
                   (PI0 I (M%%))))
           (< (+ (EXPT 2 (* (+ 1 (- K)) (RHO%%)))
                 (- (+ (DELTA0 J (N%%))
                       (/ (EXPT 2 (N%%)))
                       (/ (EXPT 2 (+ -3 (M%%)))))))
              (PI0 I (M%%))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (xtable-41 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance xtable-42 (x1 (EXPT 2 (* (+ 1 (- K)) (RHO%%))))
                                             (x2 (EXPT 2 (- (* (K%%) (RHO%%)))))
                                             (y (- (+ (DELTA0 J (N%%))
                                                      (EXPT 2 (- (N%%)))
                                                      (EXPT 2 (+ 3 (- (M%%)))))))
                                             (z (PI0 I (M%%))))
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))
          ("Subgoal 4" :in-theory (enable natp zp))
          ("Subgoal 3" :in-theory (enable natp zp))
          ("Subgoal 2" :in-theory (enable natp zp))
          ("Subgoal 1" :in-theory (enable natp zp))))

(local-defthm xtable-44
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (integerp k)
                (> k (k%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (sqrt-accessible-p i j k (rho%%) (m%%) (n%%)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable accessible-p sqrt-accessible-p)
                  :use (xtable-40 xtable-43 rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                        (:instance converse-39 (rho (rho%%)) (m (m%%)) (n (n%%)))))))

(local-defthm xtable-45
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (integerp k)
                (> k (k%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (check-upper-bound h i j k (rho%%) (m%%) (n%%)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable check-sqrt-entry)
                  :use (xtable-44
                        xtable-25
                        (:instance check-sqrt-table-lemma (rho (rho%%)) (m (m%%)) (n (n%%)) (table (table%%)))))))

(local-defthm xtable-46
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (integerp k)
                (> k (k%%))
                (or (< i (expt 2 (1- (m%%))))
                    (= i (1- (expt 2 (m%%)))))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (and (< h (1- (expt 2 (rho%%))))
                          (> (* k (rho%%))
                             (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%)))) (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                                           (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
                          (< h (lower i j (rho%%) (m%%) (n%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-upper-bound)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
                  :use (xtable-45
                        (:instance lemma-3-5-38 (h (lookup i j (xtable%%))))))))

(local-defun kwit (i j)
  (let ((h (lookup i j (xtable%%))))
    (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                     (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%))))
                  (/ (* (1+ h) (1+ h)) (expt 2 (rho%%)))))))

(local-defund kmax (i j)
  (1+ (max (k%%) (kwit i j))))

(local-defthm xtable-47
  (implies (and (natp a)
                (natp b))
           (let ((k (1+ (max a b))))
             (and (integerp k)
                  (> k a)
                  (> (* k (rho%%)) b))))
  :rule-classes ()
  :hints (("Goal" :use (rho%%-constraint
                        (:instance *-weakly-monotonic (x (1+ (max a b))) (y 1) (y+ (rho%%)))))))

(local-defthm xtable-48
  (and (integerp (kmax i j))
       (> (kmax i j) (k%%))
       (> (* (kmax i j) (rho%%)) (kwit i j)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable kmax)
                  :use ((:instance xtable-47 (a (k%%))
                                             (b (kwit i j)))))))

(local-defthm xtable-49
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (or (< i (expt 2 (1- (m%%))))
                    (= i (1- (expt 2 (m%%)))))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (and (< h (1- (expt 2 (rho%%))))
                          (< h (lower i j (rho%%) (m%%) (n%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (* (/ (1+ h) (expt 2 (rho%%))) (delta0 j (n%%)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :expand ((kwit i j))
                  :use (xtable-48
                        (:instance xtable-46 (k (kmax i j)))))))

(local-defthm xtable-50
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (or (< i (expt 2 (1- (m%%))))
                    (= i (1- (expt 2 (m%%)))))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (>= h (lower i j (rho%%) (m%%) (n%%))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-49 rho%%-constraint m%%-constraint n%%-constraint
                        (:instance lemma-3-5-47 (h (lookup i j (xtable%%))) (m (m%%)) (n (n%%)) (rho (rho%%)))))))

(local-defthm xtable-51
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (integerp k)
                (> k (k%%))
                (>= i (expt 2 (1- (m%%))))
                (not (= i (1- (expt 2 (m%%)))))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (and (< h (1- (expt 2 (rho%%))))
                          (> (* k (rho%%))
                             (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                                              (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                                           (/ (* (1+ h) (1+ h)) (expt 2 (rho%%))))))
                          (< h (lower i j (rho%%) (m%%) (n%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-upper-bound)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
                  :use (xtable-45
                        (:instance lemma-3-5-51 (h (lookup i j (xtable%%))))))))

(local-defun kwit2 (i j)
  (let ((h (lookup i j (xtable%%))))
    (k-witness (/ (- (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                     (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%))))))
                  (/ (* (1+ h) (1+ h)) (expt 2 (rho%%)))))))

(local-defund kmax2 (i j)
  (1+ (max (k%%) (kwit2 i j))))

(local-defthm xtable-52
  (and (integerp (kmax2 i j))
       (> (kmax2 i j) (k%%))
       (> (* (kmax2 i j) (rho%%)) (kwit2 i j)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable kmax2)
                  :use ((:instance xtable-47 (a (k%%))
                                             (b (kwit2 i j)))))))

(local-defthm xtable-53
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (>= i (expt 2 (1- (m%%))))
                (not (= i (1- (expt 2 (m%%)))))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (and (< h (1- (expt 2 (rho%%))))
                          (< h (lower i j (rho%%) (m%%) (n%%))))
                     (<= (+ (pi0 i (m%%)) (expt 2 (- 3 (m%%))))
                         (* (/ (1+ h) (expt 2 (rho%%))) (+ (delta0 j (n%%)) (expt 2 (- (n%%)))))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :expand ((kwit2 i j))
                  :use (xtable-52
                        (:instance xtable-51 (k (kmax2 i j)))))))

(local-defthm xtable-54
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (>= i (expt 2 (1- (m%%))))
                (not (= i (1- (expt 2 (m%%)))))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (>= h (lower i j (rho%%) (m%%) (n%%))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-53 rho%%-constraint m%%-constraint n%%-constraint
                        (:instance lemma-3-5-59 (h (lookup i j (xtable%%))) (m (m%%)) (n (n%%)) (rho (rho%%)))))))

(local-defthm xtable-55
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (let ((h (lookup i j (xtable%%))))
            (implies (< h (1- (expt 2 (rho%%))))
                     (>= h (lower i j (rho%%) (m%%) (n%%))))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-54 xtable-50))))

(local-defthm xtable-56
  (implies (and (natp i)
                (< i (expt 2 (m%%)))
                (natp j)
                (< j (expt 2 (n%%)))
                (accessible-p i j (k%%) (rho%%) (m%%) (n%%))
                (> (pi0 i (m%%))
                   (- (expt 2 (- (* (k%%) (rho%%))))
                      (+ (delta0 j (n%%))
                         (expt 2 (- (n%%)))
                         (expt 2 (- 3 (m%%)))))))
          (>= (lookup i j (xtable%%))
              (lower i j (rho%%) (m%%) (n%%))))
  :rule-classes ()
  :hints (("Goal" :use (xtable-55)
                  :in-theory (enable lower))))

(local-defthm xtable-57
  (let* ((i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
         (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
    (implies (> (pi0 i (m%%))
                (- (expt 2 (- (* (k%%) (rho%%))))
                   (+ (delta0 j (n%%))
                      (expt 2 (- (n%%)))
                      (expt 2 (- 3 (m%%))))))
             (admissible-srt-table-p (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (e/d (check-lower-bound)
                           (jared-disables-1
                            jared-disables-2
                            jared-disables-3
                            jared-disables-4))
           :use (rho%%-constraint m%%-constraint n%%-constraint k%%-constraint
                                  (:instance xtable-56 (i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
                                             (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
                                  (:instance xtable-23 (i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
                                             (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
                                  (:instance xtable-27 (i (i-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%)))
                                             (j (j-srt (k%%) (rho%%) (m%%) (n%%) (xtable%%))))
                                  (:instance xtable-11 (k (k%%)) (rho (rho%%)) (m (m%%)) (n (n%%)) (table (xtable%%)))))))

(defthm lemma-3-6-b
  (admissible-srt-table-p (k%%) (rho%%) (m%%) (n%%) (xtable%%))
  :rule-classes ()
  :hints (("Goal" :use (xtable-24 xtable-57))))

;;**********************************************************************************

(defund check-exists-entry (i j k rho m n)
  (or (not (accessible-p i j k rho m n))
      (<= (lower i j rho m n) (- 1 (expt 2 rho)))
      (check-lower-bound (lower i j rho m n) i j (1+ k) rho m n)))

(defund check-exists-row (i j k rho m n)
  (if (zp j)
      t
    (and (check-exists-entry i (1- j) k rho m n)
         (check-exists-row i (1- j) k rho m n))))

(defund check-exists-rows (i k rho m n)
  (if (zp i)
      t
    (and (check-exists-row (1- i) (expt 2 n) k rho m n)
         (check-exists-rows (1- i) k rho m n))))

(defund exists-srt-table-p (k rho m n)
  (check-exists-rows (expt 2 m) k rho m n))

(defthm exists-srt-table-p-2-2-6-2
  (exists-srt-table-p 2 2 6 2))

(defthm exists-srt-table-p-2-3-7-4
  (exists-srt-table-p 2 3 7 4))

(defthm exists-srt-table-p-2-3-8-3
  (exists-srt-table-p 2 3 8 3))

(defthm not-exists-srt-table-p-100-2-5-2
  (not (exists-srt-table-p 100 2 5 2)))

(defthm not-exists-srt-table-p-100-3-6-4
  (not (exists-srt-table-p 100 3 6 4)))

(local-defthm lemma-3-7-1
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (integerp (lower i j rho m n))
                (< (lower i j rho m n) (expt 2 rho))))
  :hints (("Goal" :in-theory (enable lower)))
  :rule-classes ())

(local-defthm lemma-3-7-2
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (and (integerp (srt-entry i j rho m n))
                (< (srt-entry i j rho m n) (expt 2 rho))
                (> (srt-entry i j rho m n) (- (expt 2 rho)))))
  :hints (("Goal" :in-theory (enable srt-entry)
                  :use lemma-3-7-1))
  :rule-classes ())

(local-defthm lemma-3-7-3
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (check-exists-entry i j k rho m n))
           (check-entry i j k rho m n (srt-entry i j rho m n)))
  :hints (("Goal" :in-theory (enable srt-entry check-exists-entry check-lower-bound check-entry)
                  :use (lemma-3-7-1 lemma-3-7-2))))

(local-defthm lemma-3-7-4
  (implies (and (natp k)
                (natp j)
                (natp n)
                (< (+ k j) (expt 2 n)))
           (equal (nth j (srt-row i k rho m n))
                  (srt-entry i (+ k j) rho m n)))
  :hints (("Goal" :induct (srt-row-induct j k))
          ("Subgoal *1/2" :expand ((SRT-ROW I K RHO M N)))
          ("Subgoal *1/1" :expand ((SRT-ROW I K RHO M N)))))

(local-defthm lemma-3-7-5
  (implies (and (natp k)
                (natp i)
                (natp m)
                (< (+ k i) (expt 2 m)))
           (equal (nth i (srt-rows k rho m n))
                  (srt-row (+ k i) 0 rho m n)))
  :hints (("Goal" :induct (srt-row-induct i k))
          ("Subgoal *1/2" :expand ((SRT-ROWS K RHO M N)))
          ("Subgoal *1/1" :expand ((SRT-ROWS K RHO M N)))))

(local-defthm lemma-3-7-6
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
           (equal (nth j (nth i (srt-table rho m n)))
                  (srt-entry i j rho m n)))
  :hints (("Goal" :in-theory (enable srt-table))))

(local-defthm integerp-srt-entry
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (<= j (expt 2 n)))
           (integerp (srt-entry i j rho m n)))
  :hints (("Goal" :in-theory (enable lower srt-entry))))

(local-defthm lemma-3-7-7
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (<= j (expt 2 n))
                (check-exists-row i j k rho m n))
           (check-row i j k rho m n (nth i (srt-table rho m n))))
  :hints (("Goal" :in-theory (enable check-exists-row check-row))))

(local-defthm lemma-3-7-8
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (<= i (expt 2 m))
                (check-exists-rows i k rho m n))
           (check-rows i k rho m n (srt-table rho m n)))
  :hints (("Goal" :in-theory (enable check-exists-rows check-rows))))

(defthm lemma-3-7-a
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (exists-srt-table-p k rho m n))
           (admissible-srt-table-p k rho m n (srt-table rho m n)))
  :hints (("Goal" :in-theory (enable exists-srt-table-p admissible-srt-table-p))))

(defun f (h i j k rho m n)
  (if (< i (expt 2 (1- m)))
      (* (/ (1- h) (expt 2 rho))
         (+ (delta0 j n) (expt 2 (- n)) (* (1- h) (expt 2 (- (* (1+ k) rho))))))
    (* (/ (1- h) (expt 2 rho))
       (+ (delta0 j n) (* (1- h) (expt 2 (- (* (1+ k) rho))))))))

(local-defthm lemma-3-7-10
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h))
           (>= (* (expt 2 rho)
                  (- (f (1+ h) i j k rho m n)
                     (f h i j k rho m n)))
               (+ (delta0 j n) (* (1- (* 2 h)) (expt 2 (- (* (1+ k) rho)))))))
  :rule-classes ()
  :hints (("Goal" :use converse-39)))

(local-defthm lemma-3-7-11
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h))
           (rationalp (f h i j k rho m n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use converse-39)))

(local-defthm lemma-3-7-12
  (implies (and (not (zp rho))
                (not (zp k))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (1- (* 2 h))
               (- 1 (expt 2 (1+ rho)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x 2)
                                                      (y (- 1 (expt 2 rho)))
                                                      (y+ h))))))

(local-defthm lemma-3-7-13
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (* (1- (* 2 h)) (expt 2 (- (* (1+ k) rho))))
               (* (- 1 (expt 2 (1+ rho))) (expt 2 (- (* (1+ k) rho))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-7-12
                        (:instance *-weakly-monotonic (x (expt 2 (* (1+ k) rho)))
                                                      (y (- 1 (expt 2 (1+ rho))))
                                                      (y+ (1- (* 2 h))))))))

(local-defthm lemma-3-7-14
  (implies (and (rationalp x1)
                (rationalp y1)
                (rationalp x2)
                (rationalp y2)
                (>= x1 x2)
                (>= y1 y2))
           (>= (+ x1 y1) (+ x2 y2)))
  :rule-classes ())

(local-defthm lemma-3-7-15
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (+ (delta0 j n) (* (1- (* 2 h)) (expt 2 (- (* (1+ k) rho)))))
               (+ 1 (* (- 1 (expt 2 (1+ rho))) (expt 2 (- (* (1+ k) rho)))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-7-13
                        (:instance lemma-3-7-14 (x1 (delta0 j n)) (x2 1)
                                                (y1 (* (1- (* 2 h)) (expt 2 (- (* (1+ k) rho)))))
                                                (y2 (* (- 1 (expt 2 (1+ rho))) (expt 2 (- (* (1+ k) rho))))))))))

(local-defthm lemma-3-7-16
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (+ 1 (* (- 1 (expt 2 (1+ rho))) (expt 2 (- (* (1+ k) rho)))))
               (- 1 (expt 2 (- 1 (* k rho))))))
  :rule-classes ()
  :hints (("Goal" :use (converse-39))))

(local-defthm lemma-3-7-17
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x y)
                (>= y z))
           (>= x z))
  :rule-classes ())


(local-defthm lemma-3-7-18
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (+ (delta0 j n) (* (1- (* 2 h)) (expt 2 (- (* (1+ k) rho)))))
               0))
  :rule-classes ()
  :hints (("Goal" :use (converse-39
                        lemma-3-7-15
                        lemma-3-7-16
                        (:instance lemma-3-7-17 (y (+ 1 (* (- 1 (expt 2 (1+ rho))) (expt 2 (- (* (1+ k) rho))))))
                                                (x (+ (delta0 j n) (* (1- (* 2 h)) (expt 2 (- (* (1+ k) rho))))))
                                                (z (- 1 (expt 2 (- 1 (* k rho))))))))))

(local-defthm lemma-3-7-19
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (* (expt 2 rho)
                  (- (f (1+ h) i j k rho m n)
                     (f h i j k rho m n)))
               0))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                 lemma-3-7-10
                 lemma-3-7-18))))

(local-defthm lemma-3-7-20
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho))))
           (>= (f (1+ h) i j k rho m n)
               (f h i j k rho m n)))
  :rule-classes ()
  :hints (("Goal"
           :in-theory (disable ;jared-disables-1
                               jared-disables-2
                               jared-disables-3
                               jared-disables-4)
           :use (converse-39
                 lemma-3-7-19))))

(in-theory (disable f))

(local-defthm lemma-3-7-21
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (integerp h)
                (>= h (- 1 (expt 2 rho)))
                (natp hp))
           (>= (f (+ h hp) i j k rho m n)
               (f h i j k rho m n)))
  :rule-classes ()
  :hints (("Goal" :induct (natp-induct hp))
          ("Subgoal *1/2" :use ((:instance lemma-3-7-20 (h (1- (+ h hp))))))))

(local-defthm lemma-3-7-22
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (check-entry i j k rho m n h)
                (not (= h (- 1 (expt 2 rho))))
                (accessible-p i j k rho m n))
           (and (>= (pi0 i m) (f h i j k rho m n))
                (>= h (lower i j rho m n))
                (< h (expt 2 rho))
                (< (- (expt 2 rho)) h)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable upper check-lower-bound f check-entry))))

(local-defthm lemma-3-7-23
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n)))
          (integerp (lower i j rho m n)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable lower))))

(local-defthm lemma-3-7-24
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (>= (lower i j rho m n) (- 1 (expt 2 rho)))
                (integerp h)
                (check-entry i j k rho m n h)
                (not (= h (- 1 (expt 2 rho))))
                (accessible-p i j k rho m n))
           (and (>= (pi0 i m) (f (lower i  j rho m n) i j k rho m n))
                (>= h (lower i j rho m n))
                (< h (expt 2 rho))
                (< (- (expt 2 rho)) h)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-3-7-22
                        (:instance lemma-3-7-21 (h (lower i j rho m n)) (hp (- h (lower i j rho m n))))))))

(local-defthm lemma-3-7-25
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (>= (lower i j rho m n) (- 1 (expt 2 rho)))
                (integerp h)
                (check-entry i j k rho m n h)
                (not (= h (- 1 (expt 2 rho))))
                (accessible-p i j k rho m n))
           (and (check-lower-bound (lower i j rho m n) i j (1+ k) rho m n)
                (>= h (lower i j rho m n))
                (< h (expt 2 rho))
                (< (- (expt 2 rho)) h)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable f check-lower-bound)
                  :use (lemma-3-7-24
                        (:instance lemma-3-7-21 (h (lower i j rho m n)) (hp (- h (lower i j rho m n))))))))

(local-defthm lemma-3-7-26
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (< j (expt 2 n))
                (check-entry i j k rho m n h)
                (integerp h))
           (check-exists-entry i j k rho m n))
  :hints (("Goal" :in-theory (enable check-exists-entry check-entry)
                  :use (lemma-3-7-25))))

(local-defthm lemma-3-7-27
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (< i (expt 2 m))
                (natp j)
                (<= j (expt 2 n))
                (check-row i j k rho m n row))
           (check-exists-row i j k rho m n))
  :hints (("Goal" :in-theory (enable check-exists-row check-row))))

(local-defthm lemma-3-7-28
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (natp i)
                (<= i (expt 2 m))
                (check-rows i k rho m n rows))
           (check-exists-rows i k rho m n))
  :hints (("Goal" :in-theory (enable check-exists-rows check-rows))))

(defthm lemma-3-7-b
  (implies (and (not (zp rho))
                (not (zp m))
                (not (zp n))
                (not (zp k))
                (admissible-srt-table-p k rho m n table))
           (exists-srt-table-p k rho m n))
  :hints (("Goal" :in-theory (enable exists-srt-table-p admissible-srt-table-p))))
