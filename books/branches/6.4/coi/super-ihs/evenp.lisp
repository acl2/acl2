#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;We include arithmetic facts only locally to keep this book from enforcing an choice of arithmetic theories on its user.
(local (include-book "arithmetic"))
; (Matt K., 10/2013: Changed rel8 to rel9.)
(local (include-book "rtl/rel9/arithmetic/even-odd" :dir :system)) ;bzo combine this included book with the present book?
(local (include-book "rtl/rel9/arithmetic/integerp" :dir :system))

(in-theory (disable evenp))

;; (defthm evenp-fc
;;   (implies (evenp x)
;;            (integerp (* 1/2 x)))
;;   :rule-classes :forward-chaining)

;; (defthm evenp-rw
;;   (implies (integerp (* 1/2 x))
;;            (evenp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst 2)))

;better than the version in the RTL library
(defthmd even-int-implies-int2
  (implies (integerp (* 1/2 x))
           (equal (integerp x)
                  (acl2-numberp x)
                  ))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (disable integerp-prod)
           :use (:instance integerp-prod (x (* 1/2 x)) (y 2)))))

(defthm evenp-when-not-integerp
  (implies (not (integerp x))
           (equal (evenp x)
                  (not (acl2-numberp x))))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm evenp-forward-to-integerp
  (implies (and (evenp x)
                (acl2-numberp x))
           (integerp x))
  :rule-classes :forward-chaining)

(encapsulate
 ()

 (local
  (defthm integerp-*-means-l1
    (implies (and (integerp x)
                  (integerp y))
             (integerp (* x y)))))
          

 (defthm integerp-*-means
   (implies (and (integerp (* r x))
                 (equal (numerator r) 1)
                 (rationalp x)
                 (rationalp r)
                 )
            (integerp x))
   :hints (("goal" 
            :use ((:instance integerp-*-means-l1 
                             (x (* x r)) 
                             (y (denominator r))))))
   :rule-classes :forward-chaining))

(encapsulate
 ()

 (local
  (defthm evenp-+-2
    (implies (or (equal x 2)
                 (equal x -2))
             (equal (evenp (+ x n))
                    (evenp n)))
    :hints (("goal"
             :in-theory (enable evenp)))))

 (local
  (defun ind1 (n)
    (cond ((zip n) nil)
          ((not (evenp n)) (ind1 (if (< n 0) (+ n 1) (- n 1))))
          (t (ind1 (if (< n 0) (+ n 1) (- n 2)))))))
 

 (local
  (defthm evenp-+1-lemma
    (implies (and (not (equal (fix n) 0))
                  (not (integerp (* 1/2 n)))
                  (<= 0 n)
                  (integerp (+ -1/2 (* 1/2 n))))
             (integerp (+ 1/2 (* 1/2 n))))
    :hints (("goal"
             :in-theory (e/d (evenp) (evenp-+-2))
             :use ((:instance evenp-+-2 
                              (n (1+ n))
                              (x -2)))))))

 (local
  (defthm evenp-+1
    (implies (integerp n)
             (equal (evenp (+ 1 n))
                    (not (evenp n))))
    :hints (("goal"
             :in-theory (enable evenp)
             :induct (ind1 n)))))

 (local
  (defthm evenp-+-1
    (implies (and (syntaxp (quotep x))
                  (or (equal x 1)
                      (equal x -1))
                  (integerp n))
             (equal (evenp (+ x n))
                    (not (evenp n))))
    :hints (("goal"
             :in-theory (disable evenp-+1)
             :use (evenp-+1
                   (:instance evenp-+1 (n (1- n))))))))

 (local
  (defthm evenp-+-3
    (implies (and (syntaxp (quotep x))
                  (or (equal x 3)
                      (equal x -3))
                  (integerp n))
             (equal (evenp (+ x n))
                    (not (evenp n))))
    :hints (("goal"
             :in-theory (disable evenp-+-2)
             :use ((:instance evenp-+-2 (n (+ 1 n))
                              (x 2))
                   (:instance evenp-+-2 (n (+ -1 n))
                              (x -2)))))))

 (local
  (defthm evenp-+-4
    (implies (or (equal x 4)
                 (equal x -4))
             (equal (evenp (+ x n))
                    (evenp n)))
    :hints (("goal"
             :use ((:instance evenp-+-2 
                              (n (+ 2 n))
                              (x 2))
                   (:instance evenp-+-2 
                              (n (+ -2 n))
                              (x -2)))))))

 (local
  (defun absdec (x n)
    (if (< x 0) (+ x n) (- x n))))

 (local
  (defun ind2 (x y)
    (cond ((or (zip x) (zip y)) nil)
          ((and (evenp x) (evenp y))
           (ind2 (absdec x 2) (absdec y 2)))
          ((evenp x)
           (ind2 (absdec x 2) (absdec y 1)))
          ((evenp y)
           (ind2 (absdec x 1) (absdec y 2)))
          (t
           (ind2 (absdec x 1) (absdec y 1))))))

 (local (defthmd evenp-+-helper
   (implies (and (integerp a)
                 (integerp b))
            (equal (evenp (+ a b))
                   (equal (evenp a)
                          (evenp b))))
   :hints (("goal"
            :induct (ind2 a b)))))


;This might be expensive?  If so, consider disabling it, but make a version that only fires when a is a quoted constant and leave that version enabled.
 (defthm evenp-+
   (implies (integerp a)
            (equal (evenp (+ a b))
                   (if (integerp b)
                       (equal (evenp a) (evenp b))
                     (if (acl2-numberp b)
                         nil
                       (evenp a)
                       ))))
   :hints (("goal" :use (:instance evenp-+-helper))))

 (defthm evenp-+-alt
   (implies (integerp b)
            (equal (evenp (+ a b))
                   (if (integerp a)
                       (equal (evenp a) (evenp b))
                     (if (acl2-numberp a)
                         nil
                       (evenp b)
                       ))))
   :hints (("goal" :in-theory (disable evenp-+)
            :use (:instance evenp-+ (a b) (b a)))))

 )



;improve?
(defthm evenp-
  (implies (integerp a)
           (equal (evenp (- a))
                  (evenp a)))
  :hints (("goal" :in-theory (enable evenp))))

(encapsulate
 ()

 (local
  (defun ind3 (a b)
    (cond ((zip a) (cons a b))
          ((< a 0) (ind3 (1+ a) b))
          (t (ind3 (1- a) b)))))

;If you disable this, consider making a cheap version which only fires when a is a constant.
 (defthm evenp-*
   (implies (and (integerp a)
                 (integerp b))
            (equal (evenp (* a b))
                   (or (evenp a)
                       (evenp b))))
   :hints (("goal"
            :in-theory (enable zp)
            :induct (ind3 a b)))))

;move hyps to conclusion?
(defthm evenp-expt
  (implies (and (<= 0 y)
                (integerp y)
                (integerp x) ; usually x will be 2
                )
           (equal (evenp (expt x y))
                  (and (not (equal y 0))
                       (evenp x))))
  :hints (("goal" :in-theory (enable expt))))

;special case when the base of exponentiation is 2
;
(defthm evenp-of-expt2-better
  (equal (evenp (expt 2 y))
         (and (integerp y)
              (< 0 y)))
  :hints (("Goal" :in-theory (e/d (evenp) ()))))



;;
;; ODDP
;; 

(in-theory (disable oddp))

;redundant?
;more like this?
(defthm oddp-forward-to-not-evenp
  (implies (oddp x)
           (not (evenp x)))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

(defthm evenp-forward-to-not-oddp
  (implies (evenp x)
           (not (oddp x)))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

(defthm not-oddp-forward-to-evenp
  (implies (not (oddp x))
           (evenp x))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

(defthm not-evenp-forward-to-oddp
  (implies (not (evenp x))
           (oddp x))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

;induction shouldn't be needed here if we improve evenp-expt-2?
(defthm oddp-of-expt
  (equal (oddp (expt 2 j))
         (or (not (integerp j))
             (<= j 0)))
  :hints (("Goal" :in-theory (enable oddp 
                                     expt ;improve evenp rule and drop
                                     EXPONENTS-ADD-UNRESTRICTED))))

;consider adding (disabled!) versions of these without the backchain-limits?
(defthmd even-odd-different-1 
  (implies (and (evenp a)
                (not (evenp b)))
           (not (equal a b)))
  :rule-classes ((:rewrite :backchain-limit-lst 5)))

;bzo do we need both of these rules?
;consider adding (disabled!) versions of these without the backchain-limits?
(defthmd even-odd-different-2 
  (implies (and (not (evenp a))
                (evenp b))
           (not (equal a b)))
  :rule-classes ((:rewrite :backchain-limit-lst 5)))




(defthm oddp-+
  (implies (and (integerp a) (integerp b))
           (equal (oddp (+ a b))
                  (not (equal (oddp a) (oddp b)))))
  :hints (("Goal" :in-theory (enable oddp))))

;improve?
(defthm oddp-minus
  (implies (integerp x)
           (equal (oddp (- x))
                  (oddp x)))
  :hints (("Goal" :in-theory (enable oddp))))

(defthm oddp-of-*
  (implies (and (integerp a) 
                (integerp b)
                )
           (equal (oddp (* a b))
                  (and (oddp a) (oddp b))))
  :hints (("Goal" :in-theory (enable oddp))))



;clean this up!

(defthm *ark*-|+1-*2-is-different-from-*2|
  (implies (and (integerp a) (integerp b))
           (not (equal (1+ (* 2 a)) (* 2 b))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))

;generalize to say expt is not equal to something odd?
(defthm *ark*-equal-1+-*2
  (implies
   (and (integerp a) (integerp b)
         (<= 0 a))
   (equal (equal (expt 2 a) (1+ (* 2 b)))
          (and (zp a) (zip b))))
  :hints (("goal" :in-theory (enable expt))))
 
(defthm *ark*-equal-1+-+-*2-*2
  (implies (and (integerp a) (integerp b) (integerp c)
                (<= 0 a))
           (equal (equal (expt 2 a) (+ 1 (* 2 b) (* 2 c)))
                  (and (zp a) (zip (+ b c)))))
  :hints (("goal" :use (:instance *ark*-equal-1+-*2 (b (+ b c))))))


;dividing through by 2 should get this...
(defthmd *ark*-+3-*2-is-different-from-*2
        (implies (and (integerp a) (integerp b))
                 (not (equal (+ 3 (* 2 a)) (* 2 b))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))

(defthm *ark*-equal-+3-*2
  (implies
   (and (integerp a) (integerp b)
        (<= 0 a))
   (equal
    (equal (expt 2 a) (+ 3 (* 2 b)))
    (and (zp a) (equal b -1))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))

;why induction here?
(defthm *ark*-equal-+3-+-*2-*2
  (implies (and (integerp a) (integerp b) (integerp c)
                (<= 0 a))
           (equal (equal (expt 2 a) (+ 3 (* 2 b) (* 2 c)))
                  (and (zp a) (equal (+ b c) -1))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))


(defthm equal-i+-*2
  (implies (and (integerp a) 
                (integerp b) 
                (integerp i)
                (<= 0 a)
                (not (evenp i)))
           (equal (equal (expt 2 a) (+ i (* 2 b)))
                  (and (zp a) (equal b (- (* 1/2 (+ -1 i)))))))
  :hints (("Goal" :in-theory (enable even-odd-different-2 even-odd-different-1))))
  
(defthm equal-i+-+-*2-*2
  (implies (and (integerp a) 
                (integerp b) 
                (integerp c)
                (integerp i)
                (<= 0 a)
                (not (evenp i)))
           (equal (equal (expt 2 a) (+ i (* 2 b) (* 2 c)))
                  (and (zp a) (equal (+ b c) (- (* 1/2 (+ -1 i)))))))
    :hints (("Goal" :in-theory (enable even-odd-different-2 even-odd-different-1))))


;; (defthm +i-*2-is-different-from-*2
;;   (implies (and (integerp a) 
;;                 (integerp b) 
;;                 (integerp i) 
;;                 (not (evenp i)))
;;            (not (equal (+ i (* 2 a)) (* 2 b)))))
;;   :hints (("goal"
;;            :use ((:instance evenp-+
;;                             (a i)
;;                             (b (* 2 a)))))))

(defthm mod-by-2-equals-1--rewrite-to-oddp
  (implies (integerp i)
           (equal (equal (mod i 2) 1)
                  (oddp i)))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm evenp-collapse
  (equal (integerp (* 1/2 x))
         (evenp x))
  :hints (("Goal" :in-theory (enable evenp))))

(theory-invariant (incompatible (:rewrite evenp-collapse) (:definition evenp)))



;; (thm
;;  (implies (and (evenp x)
;;                (acl2-numberp x))
;;           (integerp x)))

(defthm evenp-collect-1
  (equal (integerp (+ (* 1/2 x) (* 1/2 y)))
         (evenp (+ x y)))
  :hints (("Goal" :in-theory (e/d (evenp) (evenp-collapse)))))

(defthm odd-equal-expt-cheap
  (implies (and (not (evenp x))
                (integerp x)
                (integerp n)
                )
           (equal (equal x (expt 2 n))
                  (and (equal x 1)
                       (equal n 0))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  )
