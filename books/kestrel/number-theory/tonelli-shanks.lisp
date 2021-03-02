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
(include-book "kestrel/number-theory/quadratic-residue" :dir :system)
(local (include-book "projects/quadratic-reciprocity/eisenstein" :dir :system))

(include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;rtl::primep


(in-theory (disable acl2::mod-expt-fast))

(local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

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
;; p - 1 = Q.2^S

;; Step 1 of
;; https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm

;; Factors n into the S powers of 2 and the rest Q.
;; If n is a power of 2, Q will be 1.
;; Otherwise Q will be the product of the odd prime factors.
;;
(define Q*2^S ((n natp))
  :returns (mv (q natp) (s natp))
  :verify-guards nil
  (if (or (not (natp n)) (= n 0))
      (mv 0 0)
    (if (oddp n)
	(mv n 0)
      (mv-let (inner-q inner-s)
          (Q*2^S (/ n 2))
        (mv inner-q (+ inner-s 1)))))
  ///
  (verify-guards Q*2^S))

(defthm q2s-q-is-odd
  (implies (and (natp n) (< 0 n))
           (oddp (mv-nth 0 (Q*2^S n))))
  :hints (("Goal" :in-theory (e/d (Q*2^S oddp) ()))))

;; Show that q2s is correct

(defthm Q*2^S-type-1
  (natp (mv-nth 1 (Q*2^S n)))
  :rule-classes :type-prescription)

(defthm q2s-is-correct
  (implies (natp n)
           (equal (* (mv-nth 0 (q*2^s n))
                     (expt 2 (mv-nth 1 (q*2^s n))))
                  n))
  :hints (("Goal" :in-theory (enable q*2^s acl2::expt-of-+))))


;; ----------------
;; least repeated square to unity
;; inner loop for main T-S loop

;; (least-repeated-square tt M p)
;; calculates the least i, 0<i<M, such that tt^(2^i) = 1 mod p
;; p will be (primes::bn-254-group-prime)
;; Return value of 0 means something went wrong (handled in the caller).

(defun least-repeated-square-aux (i tt^2^i M p)
  (declare (xargs :guard (and (natp i) (natp tt^2^i) (natp M) (natp p)
                              (< 2 p))))
  (declare (xargs :measure (nfix (- M i))))
  (if (not (and (natp i) (natp M) (< 0 i) (< i M)
                (natp tt^2^i) (natp p) (< 2 p)))
      0
    (let ((next-square (mod (* tt^2^i tt^2^i) p)))
      (if (= next-square 1)
          i
        (least-repeated-square-aux (+ i 1) next-square M p)))))

(defthm least-repeated-square-aux-less-than-M
  (implies (< 0 M)
           (< (least-repeated-square-aux i tt M p) M)))

;; This variant is needed for verifying guards on T-S-aux
(defthm least-repeated-square-aux-less-than-M--variant
  (implies (and (natp M) (< 0 M) (natp (least-repeated-square-aux i tt M p)))
           (<= 0 (+ -1 M (- (least-repeated-square-aux i tt M p))))))

(defun least-repeated-square (tt M p)
  (declare (xargs :guard (and (natp tt) (natp M) (natp p) (< 2 p))))
  (if (or (not (natp tt)) (not (natp M))
          (not (natp p)) (< p 3))
      0
    (if (<= tt 1) ; this should be a guard
        0
      (least-repeated-square-aux 1 tt M p))))

(defthm least-repeated-square-less-than-M
  (implies (< 0 M)
           (< (least-repeated-square tt M p) M)))

;; ----------------
;; repeated square (can this be combined with the previous?)

;; Squares base n times,
;; i.e., computes base^(2^n)
;; for (natp n) and (natp base) and odd prime p.
(define repeated-square ((base natp) (n natp) (p natp))
  :returns (retval natp)
  :measure (nfix n)
  (declare (xargs :guard (and (natp base) (natp n) (natp p) (< 2 p))))
  (if (or (not (natp base)) (not (natp n)) (not (natp p)) (< p 3))
      0
    (if (zp n)
        base
      (repeated-square (mod (* base base) p) (- n 1) p))))

;; ----------------
;; main T-S loop
;; step 4 of
;; https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm#The_algorithm
;; Return value of 0 means something went wrong (handled in the caller).

(defun T-S-aux (M c tt R p)
  (declare (xargs :measure (nfix M)))
  (if (or (not (posp M)) (not (natp c)) (not (natp tt)) (not (natp R))
          (not (natp p)) (< p 3))
      0 ; error indicator (real root of 0 is caught at the top and computation
        ; never gets here)
    (if (= tt 1)
        ;; Normalize by returning the smaller root.
        (if (> R (/ p 2))
            (mod (- R) p)
          R)
      (let ((i (least-repeated-square tt M p)))
        (let ((b (repeated-square c (- (- M i) 1) p)))
          (let ((M2 i)
                (c2 (mod (* b b) p))
                (tt2 (mod (* tt b b) p))
                (R2 (mod (* R b) p)))
            (T-S-aux M2 c2 tt2 R2 p)))))))

(verify-guards T-S-aux)

;; ----------------
;; Tonelli-Shanks modular square root algorithm,
;; with a refinement to always return the lesser of the two square roots.

;; The argument z must be a "quadratic nonresidue", which means a number
;; that has no square root in the prime field.

;; If this returns 0, it means either n is 0
;; or there is no square root.
;; (If there were an error, it could also return 0,
;; so we should clarify that and prove
;; that can't happen)

;; Future work: prove correctness
(define tonelli-shanks-sqrt ((n natp) (p natp) (z natp))
  :guard (and (> p 2) (< z p) (rtl::primep p) (not (has-square-root? z p)))
  :short "Tonelli-Shanks modular square root."
  :long "Finds the square root of n modulo p.  p must be an odd prime.
         z is a quadratic nonresidue in p."
  :returns (sqrt natp)
  :parents (acl2::number-theory)
    (mv-let (Q S)
        (Q*2^S (- p 1))
      (let ((M S) ; could replace S by M, but this matches
            (c (acl2::mod-expt-fast z Q p))
            (tt (acl2::mod-expt-fast n Q p))
            (R (acl2::mod-expt-fast n (/ (+ Q 1) 2) p)))
        (T-S-aux M c tt R p)))
  :guard-hints (("Goal"
                 :in-theory (e/d (acl2::integerp-of-*-of-1/2-becomes-evenp
                                  acl2::not-evenp-when-oddp
				  rtl::oddp-odd-prime)
                                 (oddp)))))
