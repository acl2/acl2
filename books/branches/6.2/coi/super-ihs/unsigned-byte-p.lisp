#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(local (include-book "arithmetic"))
(include-book "ihs/ihs-lemmas" :dir :system)
(include-book "eric")

(in-theory (disable unsigned-byte-p))

;see FALSIFY-UNSIGNED-BYTE-P
;consider disabling for the user of this library
(defthm unsigned-byte-p-when-n-is-not-an-integerp
  (implies (not (integerp n))
           (equal (unsigned-byte-p n x)
                  nil))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-when-n-is-non-positive
  (implies (<= n 0)
           (equal (unsigned-byte-p n x)
                  (and (equal 0 n)
                       (equal 0 x) )))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;try disabling this?
(defthm unsigned-byte-p-forward-to-expt-bound
  (implies (unsigned-byte-p bits i)
           (< i (expt 2 bits)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     integer-range-p)))
  :rule-classes :forward-chaining)

;If we are trying to show (unsigned-byte-p n x) and we know that x is <= some k, then if we can show that k is <=
;(2^n)-1, we rewrite the unsigned-byte-p claim to a conjunction of seemingly easier facts.  One might object that
;this rule takes us from the nice world of bit vectors to the dirty world of arithmetic, but if we can establish
;the upper bound on x, I think we are already in the dirty arithmetic world, and I'd hate to see a proof of
;unsigned-byte-p fail when we alread have the upper bound, which seems like the hard part to me.

;bzo maybe the signed-byte-p rules are too agressive?  because we often know that x is >= 0...

(defthm unsigned-byte-p-rewrites-to-lower-bound-when-we-know-upper-bound-one
  (implies (and (<= x k) ;k is a free variable
                (<= k (+ -1 (expt 2 n)))
                )
           (equal (unsigned-byte-p n x)
                  (and (integerp x)
                       (<= 0 x)
                       (integerp n)
                       )
                  ))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P UNSIGNED-BYTE-P))))

(defthm unsigned-byte-p-rewrites-to-lower-bound-when-we-know-upper-bound-two
  (implies (and (< x k) ;k is a free variable
                (<= k (expt 2 n)) ;(<= k (+ -1 (expt 2 n)))
                )
           (equal (unsigned-byte-p n x)
                  (and (<= 0 x)
                       (integerp x)
                       (<= 0 n)
                       (integerp n))))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P UNSIGNED-BYTE-P))))

(defthmd usb-free-backchain
  (implies (and (<= x k) ;k is a free variable
                (<= k (1- (expt 2 n)))
                (integerp n)
                (integerp x)
                (<= 0 x)
                )
           (unsigned-byte-p n x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P
                                     UNSIGNED-BYTE-P))))

(defthmd usb-free-backchain1
  (implies (and (< x k)
                (<= k (1- (expt 2 n)))
                (integerp n)
                (integerp x)
                (<= 0 x)
                )
           (unsigned-byte-p n x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P
                                     UNSIGNED-BYTE-P))))

(defthm unsigned-byte-p-of-1
  (equal (unsigned-byte-p n 1)
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     integer-range-p))))

;bzo add syntaxp hyps like the one for this rule to other rules?
(defthm unsigned-byte-p-of-x-minus-1
  (implies (and (syntaxp (not (quotep x))) ;prevents bad behavior when acl2 unifies (+ -1 x) with a constant
                (unsigned-byte-p n x)
                )
           (equal (unsigned-byte-p n (+ -1 x))
                  (not (equal 0 x)))))

(defthm unsigned-byte-p-of-expt
  (equal (unsigned-byte-p n (expt 2 m))
         (and (< (ifix m) n)
              (<= 0 (ifix m))
              (integerp n)))
  :otf-flg t
  :hints (("Goal" :cases ((integerp m))
           :in-theory (enable unsigned-byte-p))))

;generalize to non-powers-of-2
(defthm unsigned-byte-p-of-expt-const-version
  (implies (and (syntaxp (quotep k))
                (acl2::power2p k))
           (equal (unsigned-byte-p n k)
                  (and (< (expo k) n)
                       (<= 0 (expo k))
                       (integerp n))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-of-expt)
           :use (:instance unsigned-byte-p-of-expt (m (expo k))))))

(defthm unsigned-byte-p-when-adding-big-power-of-2
  (equal (unsigned-byte-p n (+ (expt 2 n) y))
         (and (integerp n)
              (<= 0 n)
              (if (acl2-numberp y)
                  (or (equal y (- (expt 2 n)))
                      (and (unsigned-byte-p n (- y))
                           (not (equal 0 y))))
                nil)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-when-adding-big-power-of-2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n)))
           (equal (unsigned-byte-p n (+ k y))
                  (and (integerp n)
                       (<= 0 n)
                       (if (acl2-numberp y)
                           (or (equal y (- (expt 2 n)))
                               (and (unsigned-byte-p n (- y))
                                    (not (equal 0 y))))
                         nil))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p--of-minus
  (equal (unsigned-byte-p n (- y))
         (and (integerp n)
              (<= 0 n)
              (if (acl2-numberp y)
                  (and (<= y 0)
                       (and (signed-byte-p (+ 1 n) y)
                            (not (equal y (- (expt 2 n))))))
                t)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p signed-byte-p))))

;this might be expensive?
(defthm equal-bit-1 
  (implies (unsigned-byte-p 1 x) 
           (equal (equal x 1) 
                  (not (equal x 0)))))

(defthm unsigned-byte-p-+-easy
  (implies (and; (integerp n)
        ;        (< 0 n)
                (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y))
           (unsigned-byte-p n (+ x y)))
  :hints (("goal" :in-theory (enable unsigned-byte-p EXPONENTS-ADD-UNRESTRICTED))))

;it's maybe a bit odd that this is about the size parameter (which will probably usually be a constant in code proofs)
(defthmd unsigned-byte-p-fc-to-size-is-natural
  (implies (unsigned-byte-p n x)
           (and (integerp n)
                (<= 0 n)))
  :rule-classes ((:forward-chaining :trigger-terms ((unsigned-byte-p n x))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;could allow the sizes of x and y to differ and then use the larger
(defthm unsigned-byte-p-+-easy-fc
  (implies (and (unsigned-byte-p n x) ;n is a free variable
                ;(integerp n)
                ;(<= 0 n)
                (unsigned-byte-p n y))
           (unsigned-byte-p (+ 1 n) (+ x y)))
  :hints (("goal" :in-theory (enable  unsigned-byte-p-fc-to-size-is-natural)
           :use ((:instance unsigned-byte-p-+-easy (n (1+ n))))))
  :rule-classes ((:forward-chaining :trigger-terms ((+ x y)))))



