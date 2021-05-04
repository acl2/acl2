; Number Theory Library
; Tonelli-Shanks Square Root
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors:
;   Alessandro Coglio (coglio@kestrel.edu),
;   Eric Smith (eric.smith@kestrel.edu),
;   Jagadish Bapanapally (jagadishb285@gmail.com)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
(local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
(include-book "kestrel/arithmetic-light/mod-expt-fast" :dir :system)
(include-book "kestrel/number-theory/quadratic-residue" :dir :system)
(local (include-book "projects/quadratic-reciprocity/eisenstein" :dir :system))
(local (include-book "kestrel/number-theory/mod-expt-fast" :dir :system))

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;rtl::primep


(in-theory (disable acl2::mod-expt-fast))

(local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

(defxdoc tonelli-shanks-modular-sqrt-algorithm
  :parents (acl2::number-theory)
  :short "Tonelli-Shanks Modular Square Root Algorithm."
  :long "<b> <h3> Overview </h3> </b>
<p> Below is an implementation of the Tonelli-Shanks modular square root algorithm. The function tonelli-shanks-sqrt-aux returns a square root for a natural number n in the prime field p if a square root exists for n in the field. The function returns 0 if n is equal to 0 or if n does not have a square root.</p>

<p> Refer to tonelli-shanks-proof.lisp for the proof of the correctness of the function. See subtopics for the supportive functions and interface functions to tonelli-shanks-sqrt-aux.</p>
<h3> Definitions and Theorems </h3>
@(def q*2^s)
@(thm q2s-is-correct)
@(thm posp-q*2^s-n-is-even)
@(def least-repeated-square-aux)
@(def least-repeated-square)
@(def repeated-square)
@(thm repeated-square-equiv)
@(def t-s-aux)
@(def tonelli-shanks-sqrt-aux)")
(xdoc::order-subtopics tonelli-shanks-modular-sqrt-algorithm
                       (tonelli-shanks-either-sqrt tonelli-shanks-lesser-sqrt tonelli-shanks-sqrt tonelli-shanks-greater-sqrt tonelli-shanks-even-sqrt tonelli-shanks-odd-sqrt tonelli-shanks-supportive-functions))

(defxdoc tonelli-shanks-supportive-functions
  :parents (tonelli-shanks-modular-sqrt-algorithm)
  :short "Supportive Functions"
  :long "Supportive functions for the Tonelli-Shanks modular square root algorithm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; --------------------------------
;; Square root
;; Tonelli-Shanks algorithm.
;; See:
;;   https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm
;; Another reference, not just about "extension fields" but with
;; good explanations of the various modular square root options for various fields:
;;   "Square root computation over even extension fields"
;;   https://eprint.iacr.org/2012/685.pdf

;; ----------------
;; p - 1 = q.2^s

;; Step 1 of
;; https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm

;; Factors n into the s powers of 2 and the rest q.
;; If n is a power of 2, q will be 1.
;; Otherwise q will be the product of the odd prime factors.
;;
(define q*2^s ((n natp))
  :returns (mv (q natp) (s natp))
  :verify-guards nil
  :parents (tonelli-shanks-supportive-functions)
  (if (or (not (natp n)) (= n 0))
      (mv 0 0)
    (if (oddp n)
        (mv n 0)
      (mv-let (inner-q inner-s)
        (q*2^s (/ n 2))
        (mv inner-q (+ inner-s 1)))))
  ///
  (verify-guards q*2^s))

(defthm q2s-q-is-odd
  (implies (and (natp n) (< 0 n))
           (oddp (mv-nth 0 (q*2^s n))))
  :hints (("goal" :in-theory (e/d (q*2^s oddp) ()))))

;; Show that q2s is correct:

(defthm q*2^s-type-0
  (natp (mv-nth 0 (q*2^s n)))
  :rule-classes :type-prescription)

(defthm q*2^s-type-1
  (natp (mv-nth 1 (q*2^s n)))
  :rule-classes :type-prescription)

(defthm q2s-is-correct
  (implies (natp n)
           (equal (* (mv-nth 0 (q*2^s n))
                     (expt 2 (mv-nth 1 (q*2^s n))))
                  n))
  :hints (("goal" :in-theory (enable q*2^s acl2::expt-of-+))))

;; If n is even, then, (mv-nth 1 (q*2^s n)) is a positive integer
(defthm posp-q*2^s-n-is-even
  (implies (and (> n 1)
                (natp n)
                (evenp n))
           (posp (mv-nth 1 (q*2^s n))))
  :hints (("goal"
           :use ((:instance q2s-is-correct (n n))
                 (:instance q2s-q-is-odd (n n)))
           )))

;; ----------------
;; least repeated square to unity
;; inner loop for main T-S loop

;; (least-repeated-square tt m p)
;; calculates the least i, 0<i<m, such that tt^(2^i) = 1 mod p
;; p will be (primes::bn-254-group-prime)
;; Return value of 0 means there is no integer, i that is >= 1 and < m for which (mod tt^2^i p) = 1

(defun least-repeated-square-aux (i tt^2^i m p)
  (declare (xargs :guard (and (posp i) (natp tt^2^i) (natp m) (natp p) (< 2 p))))
  (declare (xargs :measure (nfix (- m i))))
  (if (not (and (posp i) (natp m) (< i m)))
      0
    (let ((next-square (mod (* tt^2^i tt^2^i) p)))
      (if (= next-square 1)
          i
        (least-repeated-square-aux (+ i 1) next-square m p)))))

(defthm least-repeated-square-aux-less-than-m
  (implies (< 0 m)
           (< (least-repeated-square-aux i tt m p) m)))

;; This variant is needed for verifying guards on t-s-aux
(defthm least-repeated-square-aux-less-than-m--variant
  (implies (and (natp m) (< 0 m) (natp (least-repeated-square-aux i tt m p)))
           (<= 0 (+ -1 m (- (least-repeated-square-aux i tt m p))))))

(defun least-repeated-square (tt m p)
  (declare (xargs :guard (and (natp tt) (natp m) (natp p) (< 2 p))))
  (if (= (mod tt p) 1)
      0
    (least-repeated-square-aux 1 tt m p)))

(defthm least-repeated-square-less-than-m
  (implies (< 0 m)
           (< (least-repeated-square tt m p) m)))

(defthm least-repeated-square-is-natp
  (natp (least-repeated-square tt m p)))

;; ----------------
;; repeated square

;; Squares base n times,
;; i.e., computes base^(2^n)
;; for (natp n) and (natp base) and odd prime p.
(define repeated-square ((base natp) (n natp) (p natp))
  :returns (retval natp)
  :measure (nfix n)
  :parents (tonelli-shanks-supportive-functions)
  (declare (xargs :guard (and (natp base) (natp n) (natp p) (< 2 p))))
  (if (or (not (natp base)) (not (natp n)) (not (natp p)) (< p 3))
      0
    (if (zp n)
        base
      (repeated-square (mod (* base base) p) (- n 1) p))))

(encapsulate
  ()

  (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
  (local (include-book "arithmetic/equalities" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm repeated-square-equiv
    (implies (and (posp x)
                  (natp c)
                  (natp p)
                  (< 2 p))
             (equal (repeated-square c x p)
                    (acl2::mod-expt-fast c (expt 2 x) p)))
    :hints (("goal"
             :use ((:instance acl2::mod-of-expt-of-mod (i (expt 2 (+ -1 x)))
                              (x (* c c))
                              (y p))
                   (:instance acl2::exponents-add-for-nonneg-exponents
                              (r c)
                              (i (expt 2 (+ -1 x)))
                              (j (expt 2 (+ -1 x))))
                   (:instance acl2::exponents-add-unrestricted (r c)
                              (i (expt 2 (+ -1 x))) (j (expt 2 (+ -1 x)))))
             :in-theory (enable acl2::mod-expt-fast repeated-square)
             ))))

;; ----------------
;; main t-s loop
;; step 4 of
;; https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm

(defun t-s-aux (m c tt r p)
  (declare (xargs :measure (nfix m)
                  :guard-debug t
                  :guard (and (posp m) (natp c) (natp tt)
                              (natp r)
                              (rtl::primep p) (< 2 p))
                  :hints (("goal"
                           :use (:instance least-repeated-square-aux (i 1) (tt^2^i tt) (m m) (p p))
                           :in-theory (e/d (least-repeated-square least-repeated-square-aux) ())))))
  (let ((m2 (least-repeated-square tt m p)))
    (if (zp m2)
        r
      (let ((b (repeated-square c (- (- m m2) 1) p)))
        (let ((c2 (mod (* b b) p))
              (tt2 (mod (* tt b b) p))
              (r2 (mod (* r b) p)))
          (t-s-aux m2 c2 tt2 r2 p))))))

(verify-guards t-s-aux)

(defthm integerp-t-s-aux
  (implies  (and (natp m)
                 (natp c)
                 (natp tt)
                 (natp r)
                 (natp p)
                 (< 2 p))
            (natp (t-s-aux m c tt r p)))
  )

(defthm integerp-of-mod-expt-fast-1
  (implies (and (integerp a)
                (natp i)
                (integerp n))
           (integerp (acl2::mod-expt-fast a i n)))
  :hints (("goal" :in-theory (enable acl2::mod-expt-fast))))

(defthm mod-expt-fast-natp
  (implies (and (integerp n)
                (< 1 n)
                (natp a)
                (natp i))
           (natp (acl2::mod-expt-fast a i n)))
  :hints (("goal"
           :in-theory (e/d (acl2::mod-expt-fast) ())
           ))
  )

(defthm natp-lemma1
  (implies (and (natp n)
                (oddp q)
                (natp q)
                (rtl::primep p)
                (< n p)
                (> p 2))
           (natp (acl2::mod-expt-fast n(+ 1/2 (* 1/2 q)) p)))
  :hints (("goal"
           :in-theory (enable acl2::not-evenp-when-oddp)
           ))
  )

;; ----------------
;; Tonelli-Shanks modular square root algorithm

;; The argument z must be a "quadratic nonresidue", which means a number
;; that has no square root in the prime field.

;; The argument n must be an integer greater than or equal to 0.

;; The argument p must be a prime greater than 2.

;; The function returns the square root of n in the prime field p if n has a square root.
;; Otherwise returns 0.

(defun tonelli-shanks-sqrt-aux (n p z)
  (declare (xargs :guard (and (natp n) (natp p) (natp z) (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
                  :guard-hints (("goal"
                                 :use ((:instance posp-q*2^s-n-is-even (n (- p 1))))
                                 :in-theory (e/d (acl2::integerp-of-*-of-1/2-becomes-evenp
                                                  acl2::not-evenp-when-oddp
                                                  acl2::mod-expt-fast
                                                  rtl::oddp-odd-prime)
                                                 (oddp))))))
  (if (has-square-root? n p)
      (if (= n 0)
          0
        (mv-let (q s)
          (q*2^s (- p 1))
          (let (
                (m s)
                (c (acl2::mod-expt-fast z q p))
                (tt (acl2::mod-expt-fast n q p))
                (r (acl2::mod-expt-fast n (/ (+ q 1) 2) p)))
            (t-s-aux m c tt r p))))
    0))

(defthm natp-tonelli-shanks-sqrt-aux
  (implies  (and (natp n)
                 (natp p)
                 (natp z)
                 (rtl::primep p)
                 (< n p)
                 (has-square-root? n p)
                 (not (has-square-root? z p))
                 (< 2 p))
            (natp (tonelli-shanks-sqrt-aux n p z)))
  :hints (("goal"
           :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
           )))

;; ----------------
;; Interface functions to the Tonelli-shanks modular square root algorithm.

;; The argument z must be a "quadratic nonresidue", which means a number
;; that has no square root in the prime field.

;; The argument n must be an integer greater than or equal to 0.

;; The argument p must be a prime greater than 2.

(define tonelli-shanks-lesser-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-shanks algorithm. Finds least square root if a square root exists."
  :long "Finds the lesser square root of the two square roots of n modulo p if it exists, otherwise returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard :hints (("goal"
                                           :use (:instance natp-tonelli-shanks-sqrt-aux (n n) (p p) (z z))
                                           :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                           )))
  :parents (tonelli-shanks-modular-sqrt-algorithm)
  (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
    (if (> sqrt (/ p 2))
        (mod (- sqrt) p)
      sqrt))
  :guard-hints (("goal" :use ((:instance natp-tonelli-shanks-sqrt-aux (n n) (p p) (z z)))
                 :in-theory (e/d (tonelli-shanks-sqrt-aux extra-info acl2::mod-expt-fast natp rtl::oddp-odd-prime) (has-square-root?)))))

(define tonelli-shanks-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :short "Tonelli-shanks algorithm. Finds the least square root."
  :long "Finds the lesser square root of the two square roots of n modulo p if a square root exists. otherwise returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard)
  :parents (tonelli-shanks-modular-sqrt-algorithm)
  (tonelli-shanks-lesser-sqrt n p z))

(define tonelli-shanks-either-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-shanks algorithm. Finds a square root if a square root exists."
  :long "Finds a square root of n modulo p if it exists, else returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard)
  :parents (tonelli-shanks-modular-sqrt-algorithm)
  (tonelli-shanks-sqrt-aux n p z))

(define tonelli-shanks-greater-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
  :guard-debug t
  :short "Tonelli-shanks algorithm. Finds the greater square root of the two if square root exists."
  :long "Finds the greater square root of the two square roots of n modulo p if square root exists, otherwise returns 0. p must be an odd prime. z is a quadratic nonresidue in p."
  :returns (sqrt natp :hyp :guard :hints (("goal"
                                           :use (:instance natp-tonelli-shanks-sqrt-aux (n n) (p p) (z z))
                                           :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                           )))
  :parents (tonelli-shanks-modular-sqrt-algorithm)
  (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
    (if (> sqrt (/ p 2))
        sqrt
      (mod (- sqrt) p)))
  :guard-hints (("goal" :use (:instance natp-tonelli-shanks-sqrt-aux (n n) (p p) (z z))
                 :in-theory (e/d (tonelli-shanks-sqrt-aux) ()))))

;; Show that, if n is a positve integer and has a square root in the prime
;; field p then, the square roots are positive integers and less than the prime
;; number p (required for verifying return types of tonelli-shanks-even-sqrt
;; and tonelli-shanks-odd-sqrt):

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
   (local (include-book "kestrel/number-theory/mod-expt-fast" :dir :system))
   (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))
   
   (defthmd hyps-t-s-aux
     (implies (and (natp n)
                   (natp p)
                   (natp z)
                   (not (has-square-root? z p))
                   (< 2 p)
                   (< z p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (< 0 n)
                   (equal (mv-nth 0 (q*2^s (- p 1))) q)
                   (equal (acl2::mod-expt-fast z q p) c)
                   (equal (acl2::mod-expt-fast n (/ (+ q 1) 2) p) r))
              (and (posp c)
                   (posp r)
                   (< c p)
                   (< r p)))
     :hints (("goal"
              :use ((:instance acl2::<-of-0-and-mod-expt-fast-when-primep (n p) (i q) (a z))
                    (:instance acl2::<-of-0-and-mod-expt-fast-when-primep (n p) (i (/ (+ q 1) 2)) (a n)))
              :in-theory (e/d (acl2::mod-expt-fast) ())
              )))))

(local
 (encapsulate
   ()
   
   (local
    (defthm lemma1
      (implies (and (posp m)
                    (natp m2)
                    (< m2 m))
               (<= (+ m2 1) m))))

   (defthm <0<t-s-aux<p
     (implies (and (posp n)
                   (has-square-root? n p)
                   (posp m)
                   (posp c)
                   (< c p)
                   (natp tt)
                   (posp r)
                   (< r p)
                   (natp p)
                   (< n p)
                   (rtl::primep p)
                   (< 2 p)
                   (< 0 (least-repeated-square tt m p)))
              (let ((b (repeated-square c (- (- m (least-repeated-square tt m p)) 1) p)))
                (let ((c2 (mod (* b b) p))
                      (tt2 (mod (* tt b b) p))
                      (r2 (mod (* r b) p)))
                  (declare (ignore tt2))
                  (and (posp r2)
                       (< r2 p)
                       (posp c2)
                       (< c2 p)
                       ))))
     :hints (("goal"
              :use ((:instance acl2::<-of-0-and-mod-expt-fast-when-primep (n p)
                               (i (+ -1 m (- (least-repeated-square tt m p))))
                               (a c))
                    (:instance lemma1 (m m) (m2 (least-repeated-square tt m p)))
                    (:instance least-repeated-square-less-than-m (m m) (tt tt) (p p))
                    (:instance least-repeated-square-is-natp (tt tt) (m m) (p p))
                    (:instance repeated-square-equiv (c c) (x (+ -1 m (- (least-repeated-square tt m p))))
                               (p p)))
              :in-theory (e/d (acl2::mod-expt-fast repeated-square) (least-repeated-square hyps-t-s-aux))
              )))))

(defthmd t-s-aux-posp<p
  (implies  (and (posp n)
                 (has-square-root? n p)
                 (posp m)
                 (posp c)
                 (< c p)
                 (natp tt)
                 (posp r)
                 (< r p)
                 (natp p)
                 (< n p)
                 (rtl::primep p)
                 (< 2 p))
            (and (posp (t-s-aux m c tt r p))
                 (< (t-s-aux m c tt r p) p)))
  :hints (("goal"
           :in-theory (e/d (t-s-aux) (least-repeated-square repeated-square))
           :induct (t-s-aux m c tt r p)
           )))

(defthmd tonelli-shanks-sqrt-aux-is-posp<p
  (implies (and (posp n)
                (natp z)
                (> p 2)
                (has-square-root? n p)
                (< n p)
                (< z p)
                (rtl::primep p)
                (not (has-square-root? z p))
                (equal (tonelli-shanks-sqrt-aux n p z) y))
           (and (posp y)
                (< y p)))
  :hints (("goal"
           :in-theory (e/d (tonelli-shanks-sqrt-aux has-square-root?) ())
           :use ((:instance hyps-t-s-aux
                            (n n)
                            (p p)
                            (z z)
                            (q (mv-nth 0 (q*2^s (- p 1))))
                            (c (acl2::mod-expt-fast z (mv-nth 0 (q*2^s (- p 1))) p))
                            (r (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (q*2^s (- p 1))) 1) 2) p)))
                 (:instance t-s-aux-posp<p
                            (n n)
                            (p p)
                            (m (mv-nth 1 (q*2^s (- p 1))))
                            (c (acl2::mod-expt-fast z (mv-nth 0 (q*2^s (- p 1))) p))
                            (tt (acl2::mod-expt-fast n (mv-nth 0 (q*2^s (- p 1))) p))
                            (r (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (q*2^s (- p 1))) 1) 2) p))
                            )
                 ))))

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  
  (define tonelli-shanks-even-sqrt ((n natp) (p natp) (z natp))
    :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
    :guard-debug t
    :short "Tonelli-shanks algorithm. Finds even square root if a square root exists."
    :long "Finds the even square root of the two square roots of n modulo p if a square root exists, otherwise returns 0. z is a quadratic nonresidue in p."
    :returns (sqrt natp :hyp :guard :hints (("goal" :use ((:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z) (y (tonelli-shanks-sqrt-aux n p z))))                                                    
                                             :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                             )))
    :parents (tonelli-shanks-modular-sqrt-algorithm)
    (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
      (if (evenp sqrt)
          sqrt
        (mod (- sqrt) p)))
    :guard-hints (("goal" :use ((:instance natp-tonelli-shanks-sqrt-aux
                                           (n n) (p p) (z z))
                                (:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
                                (:instance natp-tonelli-shanks-sqrt-aux
                                           (n 0) (p p) (z z)))
                   :in-theory (e/d (tonelli-shanks-sqrt-aux acl2::not-evenp-when-oddp) ())))
    ///
    (acl2::more-returns
     (sqrt evenp :hyp :guard :hints (("goal"
                                      :use ((:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z) (y (tonelli-shanks-sqrt-aux n p z))))                                                    
                                      :in-theory (e/d (tonelli-shanks-sqrt-aux) ())
                                      ))))))

(defun natp-zero-or-oddp (x)
  (and (natp x)
       (or (oddp x)
           (equal x 0))))

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  
  (define tonelli-shanks-odd-sqrt ((n natp) (p natp) (z natp))
    :guard (and (> p 2) (< z p) (rtl::primep p) (< n p) (not (has-square-root? z p)))
    :guard-debug t
    :short "Tonelli-shanks algorithm. Finds odd square root if a square root exists."
    :long "Finds the odd square root of the two square roots of n modulo prime p if a square root exists, otherwise returns 0. z is a quadratic nonresidue in p."
    :returns (sqrt natp-zero-or-oddp :hyp :guard :hints (("goal" :use ((:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z) (y (tonelli-shanks-sqrt-aux n p z))))                                                    
                                                          :in-theory (e/d (tonelli-shanks-sqrt-aux oddp acl2::not-evenp-when-oddp) ())
                                                          )))
    :parents (tonelli-shanks-modular-sqrt-algorithm)
    (let ((sqrt (tonelli-shanks-sqrt-aux n p z)))
      (if (oddp sqrt)
          sqrt
        (mod (- sqrt) p)))
    :guard-hints (("goal" :use ((:instance natp-tonelli-shanks-sqrt-aux
                                           (n n) (p p) (z z))
                                (:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
                                (:instance natp-tonelli-shanks-sqrt-aux
                                           (n 0) (p p) (z z)))
                   :in-theory (e/d (tonelli-shanks-sqrt-aux acl2::not-evenp-when-oddp oddp) ())))))
