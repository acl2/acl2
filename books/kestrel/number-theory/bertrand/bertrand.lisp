; Bertrand's Postulate: For every n >= 1, there is a prime p with n < p <= 2n.
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book proves Bertrand's Postulate (theorem 98 on the "Formalizing 100
;; Theorems" list).  The main theorem is BERTRAND-POSTULATE, near the end of
;; this book.  The only definition needed to understand its statement, besides
;; EXISTS-PRIME-BETWEEN-N-AND-2N below, is DM::PRIMEP, from
;; projects/numbers/euclid.lisp.  At the end of the book, we also prove
;; BERTRAND-POSTULATE-STRICT, a variant with a strict upper bound.
;;
;; We follow Erdos's proof, as presented in "Proofs from THE BOOK" (Aigner and
;; Ziegler) and as formalized in Lean's Mathlib (NumberTheory/Bertrand.lean)
;; and other systems:
;;
;; - For large n (here, n >= 1024), suppose there is no prime in (n, 2n].
;;   Consider the central binomial coefficient C = (2n choose n).  Then:
;;   - 4^n <= 2n * C.
;;   - Each prime power p^e exactly dividing C satisfies p^e <= 2n.
;;   - Primes p with p^2 > 2n appear in C at most once.
;;   - Primes p with 2n/3 < p <= n do not divide C.
;;   - So C <= (2n)^c * primorial(2n/3) <= (2n)^c * 4^(2n/3), where c is the
;;     number of primes p with p^2 <= 2n, and (c+1)^2 <= 2n.
;;   - These bounds contradict each other (see main-inequality.lisp).
;;   Unlike most formalizations, we use no real numbers or logarithms, only
;;   integer arithmetic.
;;
;; - For n < 1024, we check the claim by computation.
;;
;; Supporting books:
;; - legendre.lisp: Legendre's formula for the prime factorization of m!, and
;;   the resulting factorization of binomial coefficients.
;; - primorial.lisp: The product of the primes <= m is at most 4^m.
;; - central-binomial.lisp: Bounds on the central binomial coefficient.
;; - main-inequality.lisp: The final inequality for large n.

(include-book "projects/numbers/euclid" :dir :system) ; for dm::primep
(local (include-book "central-binomial"))
(local (include-book "main-inequality"))
(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; There exists a prime p with n < p <= 2n.
(defun-sk exists-prime-between-n-and-2n (n)
  (exists (p)
    (and (dm::primep p)
         (< n p)
         (<= p (* 2 n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Small n: check by computation

;; Find the least prime p with lo < p <= hi, or return nil if there is none.
(local
 (defun find-prime-between (lo hi)
   (declare (xargs :measure (nfix (- hi lo))))
   (if (and (integerp lo)
            (integerp hi)
            (< lo hi))
       (if (dm::primep (+ 1 lo))
           (+ 1 lo)
         (find-prime-between (+ 1 lo) hi))
     nil)))

(local
 (defthm find-prime-between-correct
   (implies (find-prime-between lo hi)
            (and (dm::primep (find-prime-between lo hi))
                 (< lo (find-prime-between lo hi))
                 (<= (find-prime-between lo hi) hi)))))

;; Check that there is a prime in (k, 2k] for every k with 1 <= k <= n.
(local
 (defun check-bertrand (n)
   (if (zp n)
       t
     (and (find-prime-between n (* 2 n))
          (check-bertrand (+ -1 n))))))

(local
 (defthm check-bertrand-correct
   (implies (and (check-bertrand m)
                 (posp n)
                 (<= n m)
                 (integerp m))
            (find-prime-between n (* 2 n)))))

;; Proved by evaluation:
(local
 (defthm check-bertrand-1023
   (check-bertrand 1023)))

(local
 (defthm bertrand-postulate-small
   (implies (and (posp n)
                 (< n 1024))
            (exists-prime-between-n-and-2n n))
   :hints (("Goal" :use ((:instance check-bertrand-correct (m 1023))
                         (:instance exists-prime-between-n-and-2n-suff
                                    (p (find-prime-between n (* 2 n)))))
            :in-theory (disable check-bertrand-correct
                                exists-prime-between-n-and-2n-suff
                                find-prime-between
                                (:e check-bertrand))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Large n: Erdos's argument

(local
 (defthm no-primes-between-when-not-exists-prime-between-n-and-2n
   (implies (and (not (exists-prime-between-n-and-2n n))
                 (<= hi (* 2 n))
                 (integerp n)
                 (integerp hi))
            (no-primes-between n hi))
   :hints (("Goal" :induct (no-primes-between n hi)
            :in-theory (enable no-primes-between))
           (and stable-under-simplificationp
                '(:use (:instance exists-prime-between-n-and-2n-suff
                                  (p hi)))))))

;; The chain of inequalities, in abstract form.
(local
 (defthm bertrand-chain
   (implies (and (<= p4n (* x cb))      ; 4^n <= 2n * C
                 (<= cb (* e pr))       ; C <= (2n)^c * primorial(2n/3)
                 (<= pr p4m)            ; primorial(2n/3) <= 4^(2n/3)
                 (< (* x e p4m) p4n)    ; the main inequality
                 (<= 0 x)
                 (<= 0 e)
                 (rationalp p4n)
                 (rationalp x)
                 (rationalp cb)
                 (rationalp e)
                 (rationalp pr)
                 (rationalp p4m))
            nil)
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

;; Abbreviations, to keep the arithmetic library from rewriting these terms:

(local
 (defund central-binomial-coefficient (n)
   (/ (dm::fact (* 2 n))
      (* (dm::fact n) (dm::fact n)))))

(local
 (defund small-count (n)
   (small-prime-count (* 2 n) (* 2 n))))

(local
 (defund small-factor (n)
   (expt (* 2 n) (small-count n))))

(local
 (defund two-thirds (n)
   (floor (* 2 n) 3)))

(local
 (defthm bertrand-fact-1
   (implies (posp n)
            (<= (power-of-4 n)
                (* 2 n (central-binomial-coefficient n))))
   :rule-classes nil
   :hints (("Goal" :use central-binomial-lower-bound
            :in-theory (e/d (central-binomial-coefficient)
                            (central-binomial-lower-bound
                             (:definition dm::fact)))))))

(local
 (defthm bertrand-fact-2
   (implies (and (no-primes-between n (* 2 n))
                 (<= 3 n)
                 (integerp n))
            (<= (central-binomial-coefficient n)
                (* (small-factor n) (primorial (two-thirds n)))))
   :rule-classes nil
   :hints (("Goal" :use central-binomial-upper-bound
            :in-theory (e/d (central-binomial-coefficient
                             small-factor
                             small-count
                             two-thirds)
                            (central-binomial-upper-bound
                             (:definition dm::fact)))))))

(local
 (defthm bertrand-fact-3
   (implies (natp n)
            (<= (primorial (two-thirds n))
                (power-of-4 (two-thirds n))))
   :rule-classes nil
   :hints (("Goal" :use (:instance primorial-bound (m (floor (* 2 n) 3)))
            :in-theory (e/d (two-thirds) (primorial-bound))))))

(local
 (defthm natp-of-small-count
   (natp (small-count n))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable small-count)))))

(local
 (defthm natp-of-small-factor
   (implies (natp n)
            (natp (small-factor n)))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable small-factor)))))

(local
 (defthm small-count-squared-bound
   (implies (posp n)
            (<= (* (+ 1 (small-count n)) (+ 1 (small-count n)))
                (* 2 n)))
   :rule-classes nil
   :hints (("Goal" :use (:instance small-prime-count-squared-bound
                                   (x (* 2 n))
                                   (k (* 2 n)))
            :in-theory (e/d (small-count)
                            (small-prime-count-squared-bound))))))

(local
 (defthm expt-of-small-count-plus-1
   (implies (posp n)
            (equal (expt (* 2 n) (+ 1 (small-count n)))
                   (* (* 2 n) (small-factor n))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable small-factor)))))

(local
 (defthm bertrand-fact-4
   (implies (and (<= 1024 n)
                 (integerp n))
            (< (* (* (* 2 n) (small-factor n))
                  (power-of-4 (two-thirds n)))
               (power-of-4 n)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance main-inequality
                                    (u (+ 1 (small-count n))))
                         (:instance small-count-squared-bound)
                         (:instance expt-of-small-count-plus-1))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(two-thirds
                                         posp
                                         natp
                                         (:type-prescription small-count)))))))

(local
 (defthm bertrand-postulate-large
   (implies (and (no-primes-between n (* 2 n))
                 (<= 1024 n)
                 (integerp n))
            nil)
   :rule-classes nil
   :hints (("Goal" :use ((:instance bertrand-fact-1)
                         (:instance bertrand-fact-2)
                         (:instance bertrand-fact-3)
                         (:instance bertrand-fact-4)
                         (:instance bertrand-chain
                                    (p4n (power-of-4 n))
                                    (x (* 2 n))
                                    (cb (central-binomial-coefficient n))
                                    (e (small-factor n))
                                    (pr (primorial (two-thirds n)))
                                    (p4m (power-of-4 (two-thirds n)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bertrand's Postulate: For every positive integer n, there is a prime p with
;; n < p <= 2n.
(defthm bertrand-postulate
  (implies (posp n)
           (exists-prime-between-n-and-2n n))
  :hints
  (("Goal"
    :use ((:instance bertrand-postulate-small)
          (:instance bertrand-postulate-large)
          (:instance no-primes-between-when-not-exists-prime-between-n-and-2n
                     (hi (* 2 n))))
    :in-theory
    (disable exists-prime-between-n-and-2n
             bertrand-postulate-small
             no-primes-between-when-not-exists-prime-between-n-and-2n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A variant with a strict upper bound, as Bertrand's Postulate is stated in
;; some other formalizations (e.g., Isabelle and Rocq).  It requires n >= 2,
;; since no integer lies strictly between 1 and 2.  For n >= 2, it is
;; equivalent to the theorem above, because 2n is not prime.

;; There exists a prime p with n < p < 2n.
(defun-sk exists-prime-strictly-between-n-and-2n (n)
  (exists (p)
    (and (dm::primep p)
         (< n p)
         (< p (* 2 n)))))

(local
 (defthm not-primep-of-*-2
   (implies (and (integerp n)
                 (<= 2 n))
            (not (dm::primep (* 2 n))))
   :hints (("Goal" :use (:instance dm::primep-no-divisor
                                   (p (* 2 n))
                                   (d 2))
            :in-theory (enable dm::divides)))))

;; Bertrand's Postulate, strict version: For every integer n >= 2, there is a
;; prime p with n < p < 2n.
(defthm bertrand-postulate-strict
  (implies (and (integerp n)
                (<= 2 n))
           (exists-prime-strictly-between-n-and-2n n))
  :hints (("Goal" :use ((:instance bertrand-postulate)
                        (:instance
                         exists-prime-strictly-between-n-and-2n-suff
                         (p (exists-prime-between-n-and-2n-witness n)))
                        (:instance not-primep-of-*-2))
           :in-theory (disable bertrand-postulate
                               exists-prime-strictly-between-n-and-2n-suff
                               not-primep-of-*-2))))
