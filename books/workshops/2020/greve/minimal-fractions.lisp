;;
;; Copyright (C) 2020, David Greve
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2.
;;
(in-package "ACL2")

;; We say x is represented by the fraction N/D when x * D = N % Q.
;; This definition admits many possible fractional representations.
;; We say that N/D is a minimal representation of x if no smaller
;; denominator results in a numerator with a magnitude less than N.
;; This book introduces a function for computing such fractional
;; representations and proves that it generates minimal fractions.  We
;; also prove that every x has a minimal fractional representation in
;; which the magnitude of N and D are less than or equal to (sqrt Q).

;; Throughout this book we use the following notation:
;;
;; z : universally quantified variable
;; k : negative coefficient (denominator)
;; n : negative numerator
;; m : positive coefficient (denominator)
;; p : positive numerator
;; x : original value = n/k = p/m
;; q : modulus

;; Our generalized universally quantified minimal fractions invariant
;; can be represented logically as:
;; 
;; (implies
;;  (and
;;   (equal n (nmod (* k x) q))
;;   (equal p (pmod (* m x) q)))
;;  (forall (z)
;;    (and
;;     (implies
;;      (< (- (nmod (* z x) q)) (- p n))
;;      (<= k z))
;;     (implies
;;      (and
;;       (not (equal (pmod z q) 0))
;;       (< (pmod (* z x) q) (- p n)))
;;      (<= m z)))))
;;
;; We also prove that our algorithm preserves the following invariant:
;;
;; (implies
;;   (and
;;     (equal n (nmod (* k x) q))
;;     (equal p (pmod (* m x) q)))
;;   (equal (- (* k p) (* m n)) q))
;;
;; We use this invariant to prove that every number has a minimal
;; fractional representation in which the coefficients are less than
;; the square root of the modulus (unless the resulting numerator is
;; exactly the square root of the modulus)

;; (defthm lt-sqrt-minimum-fraction
;;   (implies
;;    (and
;;     (integerp x)
;;     (non-trivial-modulus q))
;;    (mv-let (n d) (minimum-fraction x q)
;;      (or (and (equal (* n n) q)
;;               (lt-sqrt d q))
;;          (and (lt-sqrt n q)
;;               (lt-sqrt d q)))))

;; The function (print-all-minimal-fractions x q) prints all of the
;; minimal fractions for x mod q.

;; ACL2 !>(print-all-minimal-fractions 7 17)
;; -17/0 7/1
;; -10/1 7/1
;; -3/2 7/1
;; -3/2 4/3
;; -3/2 1/5
;; -2/7 1/5
;; -1/12 1/5
;; -1/12 0/17
;; T
;;
;; The function (print-all-minimum-fractions q) prints the
;; minimum fractional representaition of all of the numbers
;; in the range (1 .. q-1)
;;
;; ACL2 !>(print-all-minimum-fractions 17)
;; 1 : 1/1
;; 2 : 2/1
;; 3 : 3/1
;; 4 : 4/1
;; 5 : -2/3
;; 6 : 1/3
;; 7 : -3/2
;; 8 : -1/2
;; 9 : 1/2
;; 10 : 3/2
;; 11 : -1/3
;; 12 : 2/3
;; 13 : -4/1
;; 14 : -3/1
;; 15 : -2/1
;; 16 : -1/1
;; T

(include-book "coi/quantification/quantified-congruence" :dir :system)
(include-book "coi/util/skip-rewrite" :dir :system)
(include-book "nary")

(defthm natp-nfix
  (implies
   (natp x)
   (equal (nfix x) x)))

(defun nfix-equiv (x y)
  (equal (nfix x) (nfix y)))

(defequiv nfix-equiv)

(defthm nfix-equiv-nfix
  (nfix-equiv (nfix x) x))

(defcong nfix-equiv equal (nfix x) 1)

(in-theory (disable nfix-equiv))

(defun ifix-equiv (x y)
  (equal (ifix x) (ifix y)))

(defequiv ifix-equiv)

(defthm ifix-equiv-ifix
  (ifix-equiv (ifix x) x))

(defcong ifix-equiv equal (ifix x) 1)

(defun pfix (x)
  (declare (type t x))
  (if (posp x) x 1))

(defthm posp-pfix-identity
  (implies
   (posp x)
   (equal (pfix x) x)))

(defthm posp-pfix
  (posp (pfix x))
  :rule-classes ((:forward-chaining :trigger-terms ((pfix x)))))

(defthm posp-implies
  (implies
   (posp x)
   (and (natp x)
        (integerp x)
        (< 0 x)))
  :rule-classes (:forward-chaining))

(defun pfix-equiv (x y)
  (equal (pfix x) (pfix y)))

(defequiv pfix-equiv)

(defthm pfix-equiv-pfix
  (pfix-equiv (pfix x) x))

(defcong pfix-equiv equal (pfix x) 1)

(defun negp (x)
  (declare (type t x))
  (and (integerp x)
       (< x 0)))

(defun neg-fix (x)
  (if (negp x) x -1))

(defun neg-equiv (x y)
  (equal (neg-fix x)
         (neg-fix y)))

(defthm negp-neg-fix
  (implies
   (negp x)
   (equal (neg-fix x) x)))

(defequiv neg-equiv)

(defthm negp-implies
  (implies
   (negp x)
   (and (integerp x)
        (< x 0)))
  :rule-classes (:forward-chaining))

(defun non-trivial-modulus (q)
  (declare (type t q))
  (and (integerp q)
       (< 2 q))) 

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (def::un pmod (x q)
    (declare (xargs :signature ((t t) natp)))
    (mod (ifix x) (pfix q)))
  
  (defthm mod-pmod
    (implies
     (and
      (integerp x)
      (posp q))
     (equal (mod (pmod x q) q)
            (mod x q))))

  (defthm pmod-zero
    (equal (pmod 0 q) 0))
  
  (defthm pmod-bound
    (implies
     (posp q)
     (< (pmod x q) q))
    :rule-classes (:linear))
  
  (def::un nmod (x q)
    (declare (xargs :signature ((t t) negp)))
    (- (mod (ifix x) (pfix q)) (pfix q)))

  (defthm nmod-reduction
    (equal (nmod a q)
           (- (pmod a q) (pfix q)))
    :hints (("Goal" :in-theory (enable nmod pmod))))

  (defthm mod-ctx-pmod-reduction
    (implies
     (and (natp x) (posp q))
     (equal (mod-ctx (pmod x q) q)
            (mod-ctx x q))))

  (defthmd pmod-congruence
    (implies
     (and
      (integerp q)
      (integerp x)
      (nary::bind-context
       (equal z (mod-ctx x q))))
     (equal (pmod x q)
            (pmod z q)))
    :hints (("Goal" :in-theory (enable mod-ctx))))
    
  (defthm pmod-negation
    (implies
     (and (integerp x) (posp q))
     (equal (pmod (- x) q)
            (if (equal (pmod x q) 0) 0
              (- (nmod x q))))))

  (defthm pmod-sum
    (implies
     (and
      (integerp a)
      (integerp b)
      (posp q))
     (equal (pmod (+ a b) q)
            (if (< (+ (pmod a q) (pmod b q)) q)
                (+ (pmod a q) (pmod b q))
              (- (+ (pmod a q) (pmod b q)) q)))))

  (defthm force-pmod-rewriting
    (implies
     (and
      (syntaxp (symbolp z))
      (in-conclusion-check (equal (pmod z q) k) :top t)
      (integerp z)
      (posp q))
     (equal (equal (pmod z q) k)
            (hide (rewrite-equiv (equal (mod-ctx z q) k)))))
    :hints (("Goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:in-theory (enable pmod mod-ctx)))))
          
  (in-theory (disable pmod nmod))
  
  (in-theory (enable pmod-congruence))
  
  )

(defun minimal-fractions-pair-p (z k n m p x q)
  ;; z : universally quantified variable
  ;; k : negative coefficient (denominator)
  ;; n : negative numerator
  ;; m : positive coefficient (denominator)
  ;; p : positive numerator
  ;; x : original value
  ;; q : modulus
  (let ((z (pfix z))
        (k (nfix k))
        (n (neg-fix n))
        (m (nfix m))
        (p (nfix p))
        (x (nfix x))
        (q (pfix q)))
    (and
     (implies
      (< (- (nmod (* z x) q)) (- p n))
      (<= k z))
     (implies
      (and
       (not (equal (pmod z q) 0))
       (< (pmod (* z x) q) (- p n)))
      (<= m z)))))

(defun smallest-coefficient-pair-p (z k m x q)
  ;; z : universally quantified variable
  ;; k : negative coefficient
  ;; m : positive coefficient
  ;; x : original value
  ;; q : modulus
  (let ((z (pfix z))
        (k (nfix k))
        (m (nfix m))
        (x (nfix x))
        (q (pfix q)))
    (minimal-fractions-pair-p z k (nmod (* k x) q) m (pmod (* m x) q) x q)))

(encapsulate
    ()

  (local (in-theory (disable nfix-equiv ifix-equiv pfix-equiv)))
  (local (in-theory (disable ifix nfix pfix abs)))
  
  (defcong pfix-equiv equal (smallest-coefficient-pair-p z k m x q) 1)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 2)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 3)
  (defcong nfix-equiv equal (smallest-coefficient-pair-p z k m x q) 4)
  (defcong pfix-equiv equal (smallest-coefficient-pair-p z k m x q) 5)

)

(defun-sk smallest-coefficient-pair (k m x q)
  (forall (z) (smallest-coefficient-pair-p (pfix z) k m x q))
  :strengthen t)

(encapsulate
    ()

  (local (in-theory (disable nth smallest-coefficient-pair-p)))

  (defun smallest-coefficient-pair-equiv (k1 m1 x1 q1 k2 m2 x2 q2)
    (and (nfix-equiv k1 k2)
         (nfix-equiv m1 m2)
         (nfix-equiv x1 x2)
         (pfix-equiv q1 q2)))

  (quant::congruence smallest-coefficient-pair (k m x q)
    (forall (z) (smallest-coefficient-pair-p (pfix z) k m x q))
    :hyps smallest-coefficient-pair-equiv)

  )

(in-theory (disable smallest-coefficient-pair))

(defthmd smallest-coefficient-pair-implication
  (implies
   (smallest-coefficient-pair     k m x q)
   (smallest-coefficient-pair-p z k m x q))
  :hints (("Goal" :use smallest-coefficient-pair-necc)))

(in-theory (disable smallest-coefficient-pair-p))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()
     
     (local
      (defun delta (n m)
        (abs (- (ifix n) (ifix m)))))
     
     (defthmd smallest-coefficient-pair-invariant-1-helper
       (implies
        (and
         (natp k)
         (natp m)
         (natp x)
         (non-trivial-modulus q)
         (smallest-coefficient-pair k m x q)
         (posp a)
         (<= (- (nmod (* k x) q)) (pmod (* m x) q))
         )
        (smallest-coefficient-pair-p a k (+ k m) x q))
       :hints (("Goal" :do-not-induct t
                :do-not '(generalize eliminate-destructors)
                :use ((:instance smallest-coefficient-pair-implication
                                 (z a))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a m)))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a k)))))
               (and stable-under-simplificationp
                    '(:in-theory (enable smallest-coefficient-pair-p)))
               ))
     
     (defthmd smallest-coefficient-pair-invariant-2-helper
       (implies
        (and
         (natp k)
         (natp m)
         (natp x)
         (non-trivial-modulus q)
         (smallest-coefficient-pair k m x q)
         (posp a)
         (< (pmod (* m x) q) (- (nmod (* k x) q)))
         )
        (smallest-coefficient-pair-p a (+ k m) m x q))
       :hints (("Goal" :do-not-induct t
                :do-not '(generalize eliminate-destructors)
                :use ((:instance smallest-coefficient-pair-implication
                                 (z a))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a m)))
                      (:instance smallest-coefficient-pair-implication
                                 (z (delta a k)))))
               (and stable-under-simplificationp
                    '(:in-theory (enable smallest-coefficient-pair-p)))
               ))
     
     ))

  (defthm smallest-coefficient-pair-invariant-1
    (implies
     (and
      (natp k)
      (natp m)
      (natp x)
      (non-trivial-modulus q)
      (smallest-coefficient-pair k m x q)
      (<= (- (nmod (* k x) q)) (pmod (* m x) q)))
     (smallest-coefficient-pair k (+ k m) x q))
    :hints (("Goal" :in-theory (disable pfix)
             :expand ((smallest-coefficient-pair k (+ k m) x q)))
            (and stable-under-simplificationp
                 '(:use (:instance smallest-coefficient-pair-invariant-1-helper
                                   (a (pfix (SMALLEST-COEFFICIENT-PAIR-WITNESS K (+ K M) X Q))))))))
  
  (defthm smallest-coefficient-pair-invariant-2
    (implies
     (and
      (natp k)
      (natp m)
      (natp x)
      (non-trivial-modulus q)
      (smallest-coefficient-pair k m x q)
      (< (pmod (* m x) q) (- (nmod (* k x) q)))
      )
     (smallest-coefficient-pair (+ k m) m x q))
    :hints (("Goal" :in-theory (disable pfix)
             :expand ((smallest-coefficient-pair (+ k m) m x q)))
            (and stable-under-simplificationp
                 '(:use (:instance smallest-coefficient-pair-invariant-2-helper
                                   (a (pfix (SMALLEST-COEFFICIENT-PAIR-WITNESS (+ K M) M X Q))))))))
  )

(defthmd smallest-coefficient-pair-implies-minimal-fractions-pair-p
  (implies
   (and
    (posp z)
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (smallest-coefficient-pair k m x q))
   (minimal-fractions-pair-p z k (nmod (* k x) q) m (pmod (* m x) q) x q))
  :hints (("Goal" :use smallest-coefficient-pair-implication
           :in-theory (enable smallest-coefficient-pair-p))))

(in-theory (disable minimal-fractions-pair-p))

(def::un step-minimal-fractions-pair (k n m p)
  (declare (xargs :signature ((natp negp natp natp) natp negp natp natp)))
  (if (< p (- n)) (mv (+ k m) (+ n p) m p)
    (mv k n (+ k m) (+ n p))))

(in-theory (disable mv-nth mv-nth-to-val))

(defthm smallest-coefficient-pair-step-minimal-fractions-pair
  (implies
   (and
    (smallest-coefficient-pair k m x q)
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (equal n (nmod (* k x) q))
    (equal p (pmod (* m x) q)))
   (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
     (and (smallest-coefficient-pair k m x q)
          (equal n (nmod (* k x) q))
          (equal p (pmod (* m x) q)))))
  :hints (("Subgoal 1" :use (smallest-coefficient-pair-invariant-1))
          ("Subgoal 2" :use (smallest-coefficient-pair-invariant-2))))

(encapsulate
    ()

  (local
   (defthm smallest-coefficient-pair-p-init-helper
     (implies
      (and
       (posp z)
       (natp x)
       (non-trivial-modulus q))
      (and (smallest-coefficient-pair-p z 0 1 x q)
           (smallest-coefficient-pair-p z 1 0 x q)))
     :hints (("Goal" :in-theory (enable MINIMAL-FRACTIONS-PAIR-P
                                        smallest-coefficient-pair-p)))))

  (defthm smallest-coefficient-pair-init
    (implies
     (and
      (natp x)
      (non-trivial-modulus q))
     (and (smallest-coefficient-pair 0 1 x q)
          (smallest-coefficient-pair 1 0 x q)))
    :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair)
                                    (PFIX-EQUIV-IMPLIES-EQUAL-SMALLEST-COEFFICIENT-PAIR-P-1)))))
  
  )
  
(defthm magnitude-invariant
  (implies
   (and
    (equal (* k p) (+ c (* m n)))
    (natp k)
    (negp n)
    (natp m)
    (natp p))
   (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
     (equal (* k p) (+ c (* m n))))))

(encapsulate
    ()

  (defun lt-sqrt (x q)
    (declare (type integer x q))
    (< (* x x) q))
     
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()

     (defun num-equal (x y)
       (equal x y))
     
     (defun prod (x y)
       (* x y))
     
     (defthmd magnitude-invariant-helper
       (implies
        (and
         (natp k)
         (negp n)
         (natp m)
         (natp p)
         (num-equal (- (prod k p) (prod m n)) c))
        (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
                (num-equal (- (prod k p) (prod m n)) c))))
     
     (defthm negative-product
       (equal (- (prod x y))
              (prod x (- y))))
     
     (defthm posp-prod
       (implies
        (and
         (posp x)
         (posp y))
        (posp (prod x y))))
     
     (defthmd lte-square-lte
       (implies
        (and
         (natp a)
         (natp b)
         (<= (* a a) (* b b)))
        (<= a b))
       :hints (("Goal" :nonlinearp t)))
     
     (defthmd lte-property
       (implies
        (and
         (natp a)
         (natp b)
         (natp c)
         (<= a b)
         (<= a c))
        (<= (* a a) (* b c)))
       :hints (("Goal" :nonlinearp t)))
     
     (defthm product-of-nlt-sqrt
       (implies
        (and
         (natp x)
         (natp y)
         (natp c)
         (not (lt-sqrt x c))
         (not (lt-sqrt y c)))
        (<= c (prod x y)))
       :hints (("Goal" :use ((:instance lte-property
                                        (a c)
                                        (b (* x x))
                                        (c (* y y))
                                        )
                             (:instance lte-square-lte
                                        (a c)
                                        (b (* x y)))
                             ))))

     (defthm not-num-equal-1
       (implies
        (and
         (posp x)
         (posp y)
         (<= c x))
        (not (num-equal (+ x y) c))))
     
     (defthm not-num-equal-2
       (implies
        (and
         (posp x)
         (posp y)
         (<= c y))
        (not (num-equal (+ x y) c))))
     
     (defthm negative-lt-sqrt
       (implies
        (< n 0)
        (equal (lt-sqrt n c)
               (lt-sqrt (- n) c))))
     
     (in-theory (disable prod num-equal lt-sqrt))
     
     (defthm one-fraction-lt-sqrt-helper-1
       (implies
        (and
         (posp k)
         (negp n)
         (posp m)
         (posp p)
         (natp c)
         (not (equal p (- n)))
         (num-equal (- (prod k p) (prod m n)) c)
         (lt-sqrt k c)
         (lt-sqrt m c)
         (not (lt-sqrt (+ k m) c))
         (not (lt-sqrt p c))
         (not (lt-sqrt n c)))
        nil)
       :rule-classes nil
       :hints (("Goal" :use magnitude-invariant-helper)))

     (defthm one-fraction-lt-sqrt-helper-2
       (implies
        (and
         (posp k)
         (negp n)
         (posp m)
         (posp p)
         (natp c)
         (not (equal p (- n)))
         (num-equal (- (prod k p) (prod m n)) c)
         (lt-sqrt k c)
         (lt-sqrt m c)
         (not (lt-sqrt (+ k m) c)))
        (or (lt-sqrt p c)
            (lt-sqrt n c)))
       :rule-classes nil
       :hints (("Goal" :use one-fraction-lt-sqrt-helper-1)))

     ))

  (defthm one-fraction-lt-sqrt-neq
    (implies
     (and
      (posp k)
      (negp n)
      (posp m)
      (posp p)
      (natp c)
      (not (equal p (- n)))
      (equal (- (* k p) (* m n)) c)
      (lt-sqrt k c)
      (lt-sqrt m c)
      (not (lt-sqrt (+ k m) c)))
     (or (lt-sqrt p c)
         (lt-sqrt n c)))
    :rule-classes nil
    :hints (("Goal" :in-theory '(num-equal prod)
             :use one-fraction-lt-sqrt-helper-2)))

  (defthm equal-p--n
    (implies
     (and
      (posp z)
      (posp p)
      (natp c)
      (equal (* z p) c)
      (not (lt-sqrt z c)))
     (or (and (equal (* p p) c)
              (equal p z))
         (lt-sqrt p c)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable lt-sqrt))))

  (defthm lt-sqrt-negative
    (equal (lt-sqrt (- x) y)
           (lt-sqrt x y))
    :hints (("Goal" :in-theory (enable lt-sqrt))))

  (local (in-theory (disable NEGATIVE-LT-SQRT)))

  (defthm one-fraction-lt-sqrt-alt
    (implies
     (and
      (posp k)
      (negp n)
      (posp m)
      (posp p)
      (natp c)
      (equal (- (* k p) (* m n)) c)
      (lt-sqrt k c)
      (lt-sqrt m c)
      (not (lt-sqrt (+ k m) c)))
     (or (and (equal (* p p) c)
              (equal (* n n) c)
              (equal p (+ k m))
              (equal (- n) (+ k m)))
         (lt-sqrt p c)
         (lt-sqrt n c)))
    :otf-flg t
    :rule-classes nil
    :hints (("Goal" :do-not-induct t
             :use ((:instance one-fraction-lt-sqrt-neq
                              (c (- (* k p) (* m n))))
                   (:instance equal-p--n
                              (z (+ k m)))
                   (:instance equal-p--n
                              (p (- n))
                              (z (+ k m)))))))

  (defthm lt-sqrt-0
    (equal (lt-sqrt 0 n)
           (< 0 n))
    :hints (("Goal" :in-theory (enable lt-sqrt))))

  (defthm one-fraction-lt-sqrt-nat
    (implies
     (and
      (natp k)
      (negp n)
      (natp m)
      (natp p)
      (natp q)
      (equal (- (* k p) (* m n)) q)
      (lt-sqrt k q)
      (lt-sqrt m q)
      (not (lt-sqrt (+ k m) q)))
     (or (and (equal (* p p) q)
              (equal (* n n) q)
              (equal p (+ k m))
              (equal (- n) (+ k m)))
         (lt-sqrt p q)
         (lt-sqrt n q)))
    :otf-flg t
    :rule-classes nil
    :hints (("Goal" :use (:instance one-fraction-lt-sqrt-alt
                                    (c q)))))

  (defthm one-fraction-lt-sqrt
    (implies
     (and
      (natp k)
      (negp n)
      (natp m)
      (natp p)
      (natp q)
      (equal (- (* k p) (* m n)) q)
      (lt-sqrt k q)
      (lt-sqrt m q)
      (not (lt-sqrt (+ k m) q)))
     (or (and (equal (* p p) q)
              (equal (* n n) q)
              (lt-sqrt k q)
              (lt-sqrt m q))
         (lt-sqrt p q)
         (lt-sqrt n q)))
    :otf-flg t
    :rule-classes nil
    :hints (("Goal" :use (:instance one-fraction-lt-sqrt-nat))))
               
  )

;; k n m p
;; (equal (- (* k p) (* m n)) q)
;; 1 -v 0 Q
;; (equal (- (* 1 Q) (* 0 -v)) q)
;; 0 -Q 1 v
;; (equal (- (* 0 v) (* 1 -Q)) q)

(defun-sk minimal-fractions-pair (k n m p x q)
  (forall (z) (minimal-fractions-pair-p (pfix z) k n m p x q)))

(defthm smallest-coefficient-pair-implies-minimal-fractions-pair
  (implies
   (and
    (posp z)
    (natp k)
    (natp m)
    (natp x)
    (posp q)
    (equal n (nmod (* k x) q))
    (equal p (pmod (* m x) q))
    (smallest-coefficient-pair k m x q))
   (minimal-fractions-pair k n m p x q))
  :hints (("Goal" :in-theory (e/d (smallest-coefficient-pair-implies-minimal-fractions-pair-p)
                                  (nmod-reduction)))))
  
(defun minimal-fractions-pair-listp (list x q)
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (case-match entry
        ((k n m p)
         (and (minimal-fractions-pair k n m p x q)
              (minimal-fractions-pair-listp (cdr list) x q)))
        (& nil)))))

(defun fractions-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (case-match entry
        ((k n m p)
         (and (natp k)
              (negp n)
              (natp m)
              (natp p)
              (fractions-listp (cdr list))))
        (& nil)))))

(def::un minimal-fractions-list-rec (k n m p)
  (declare (xargs :signature ((natp negp natp natp) fractions-listp)
                  :measure (+ (nfix (- (ifix n))) (nfix p))))
  (if (not (and (< (ifix n) 0) (< 0 (nfix p)))) (list (list k n m p))
    (cons (list k n m p)
          (mv-let (k n m p) (step-minimal-fractions-pair k n m p)
            (minimal-fractions-list-rec k n m p)))))

(in-theory (disable nmod-reduction step-minimal-fractions-pair ))

(defthm minimal-fractions-pair-listp-minimal-fractions-list-rec
  (implies
   (and
    (natp k)
    (natp m)
    (natp x)
    (non-trivial-modulus q)
    (smallest-coefficient-pair k m x q)
    (equal n (nmod (* k x) q))
    (equal p (pmod (* m x) q)))
   (minimal-fractions-pair-listp (minimal-fractions-list-rec k n m p) x q))
  :hints (("Goal" :induct (minimal-fractions-list-rec k n m p))
          (and stable-under-simplificationp
               '(:expand (:free (p n) (MINIMAL-FRACTIONS-LIST-REC K N M P))))))

(def::un minimal-fractions-list (x q)
  (declare (xargs :signature ((integerp posp) fractions-listp)))
  (let ((x (pmod x q)))
    (if (equal x 0) nil
      (let ((k 0)
            (n (- q))
            (m 1)
            (p x))
        (minimal-fractions-list-rec k n m p)))))

(defthm nmod-zero
  (equal (nmod 0 q) (- (pfix q)))
  :hints (("Goal" :in-theory (enable nmod))))

(defthm timez-zero
  (equal (* 0 x) 0))

(defthm minimal-fractions-pair-listp-minimal-fractions-list
  (implies
   (and
    (natp x)
    (non-trivial-modulus q)
    )
   (minimal-fractions-pair-listp (minimal-fractions-list x q) x q)))

(in-theory (disable minimal-fractions-list))

(defun print-minimal-fractions-pair-list (list)
  (declare (xargs :guard (fractions-listp list)))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (case-match entry
        ((k n m p)
         (prog2$
          (cw "~p1/~p0 ~p3/~p2~%" k n m p)
          (print-minimal-fractions-pair-list (cdr list))))
        (t nil)))))

(def::und print-all-minimal-fractions (x q)
  (declare (xargs :guard (and (integerp x) (posp q))))
  (let ((list (minimal-fractions-list x q)))
    (print-minimal-fractions-pair-list list)))

(in-theory (disable lt-sqrt))

(def::un minimum-fraction-rec (k n m p q)
  (declare (xargs :signature ((natp negp natp natp posp) integerp natp)
                  :hints (("Goal" :in-theory (enable step-minimal-fractions-pair)))
                  :guard (and (lt-sqrt k q) (lt-sqrt m q))
                  :measure (+ (nfix (- (ifix n))) (nfix p))))
  (if (not (and (< (ifix n) 0) (< 0 (nfix p)))) (mv p m)
    (mv-let (k1 n1 m1 p1) (step-minimal-fractions-pair k n m p)
      (if (and (lt-sqrt k1 q) (lt-sqrt m1 q))
          (minimum-fraction-rec k1 n1 m1 p1 q)
        (if (equal (* n n) q) (mv n k)
          (if (equal (* p p) q) (mv p m)
            (if (and (lt-sqrt n q) (lt-sqrt p q))
                (let ((f1 (max k (- n)))
                      (f2 (max m p)))
                  (if (< f1 f2) (mv n k)
                    (if (< f2 f1) (mv p m)
                      (if (< k m) (mv n k)
                        (mv p m)))))
              (if (lt-sqrt n q)
                  (mv n k)
                (mv p m)))))))))

(defthm lt-sqrt-minimum-fraction-rec
  (implies
   (and
    (natp k)
    (negp n)
    (natp m)
    (natp p)
    (posp q)
    (equal (* k p) (+ q (* m n)))
    (lt-sqrt k q)
    (lt-sqrt m q))
   (mv-let (n d) (minimum-fraction-rec k n m p q)
     (or (and (equal (* n n) q)
              (lt-sqrt d q))
         (and (lt-sqrt n q)
              (lt-sqrt d q)))))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal" :induct (minimum-fraction-rec k n m p q))
          (and stable-under-simplificationp
               '(:in-theory (enable STEP-MINIMAL-FRACTIONS-PAIR)))
          (and stable-under-simplificationp
               '(:use one-fraction-lt-sqrt))
          ))

(defthm lt-sqrt-1
  (implies
   (and
    (integerp q)
    (< 2 q))
   (lt-sqrt 1 q))
  :hints (("Goal" :in-theory (enable lt-sqrt))))

(def::un minimum-fraction (x q)
  (declare (xargs :signature ((integerp posp) integerp natp)))
  (let ((x (pmod x q)))
    (if (lt-sqrt x q) (mv x 1)
      (if (<= q 2) (mv x 1)
        (let ((k 0)
              (n (- q))
              (m 1)
              (p x))
          (minimum-fraction-rec k n m p q))))))

(defthm lt-sqrt-minimum-fraction
  (implies
   (and
    (integerp x)
    (non-trivial-modulus q))
   (mv-let (n d) (minimum-fraction x q)
     (or (and (equal (* n n) q)
              (lt-sqrt d q))
         (and (lt-sqrt n q)
              (lt-sqrt d q)))))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :use (:instance lt-sqrt-minimum-fraction-rec
                           (k 0)
                           (n (- q))
                           (m 1)
                           (p (pmod x q))))))

(in-theory (disable minimum-fraction))

(defun minimum-fraction-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (case-match entry
        ((n d) (and (integerp n)
                    (natp d)
                    (minimum-fraction-listp (cdr list))))
        (& nil)))))

(def::un minimum-fraction-list-rec (x q)
  (declare (xargs :signature ((natp posp) minimum-fraction-listp)
                  :measure (nfix (- (nfix q) (nfix x)))))
  (let ((q (nfix q))
        (x (nfix x)))
    (if (<= q x) nil
      (mv-let (n d) (minimum-fraction x q)
        (cons (list n d)
              (minimum-fraction-list-rec (1+ x) q))))))

(def::und minimum-fraction-list (q)
  (declare (xargs :signature ((posp) minimum-fraction-listp)))
  (minimum-fraction-list-rec 1 q))

(defun print-minimum-fraction-list (i list)
  (declare (xargs :guard (and (natp i) (minimum-fraction-listp list))))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (case-match entry
        ((n d)
         (prog2$
          (cw "~p0 : ~p1/~p2~%" i n d)
          (print-minimum-fraction-list (1+ i) (cdr list))))
        (t nil)))))

(defun print-all-minimum-fractions (q)
  (declare (xargs :guard (posp q)))
  (let ((list (minimum-fraction-list q)))
    (print-minimum-fraction-list 1 list)))
