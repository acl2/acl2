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

; Port lior0 theorems to lior.  The original definition of lior (in rel4) was
; that of lior0 in the current release.  So the port is to keep all the lemmas
; about lior0 and then use equality of lior0 with lior to port them to lior.

(in-package "RTL")

(include-book "lior0")
(local (include-book "top1"))

(defun binary-lior (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)
                  :verify-guards nil))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (or (equal (bitn x 0) 1)
                      (equal (bitn y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lior (mod x 2) (mod y 2) 1))))
       :exec ; (lior0 x y n)
       (logior (bits x (1- n) 0)
               (bits y (1- n) 0))))

(defmacro lior (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior x y n) -- the base case
         `(binary-lior ,@x))
        (t
         `(binary-lior ,(car x)
                       (lior ,@(cdr x))
                       ,(car (last x))))))


(encapsulate
 ()

 (local
  (defun p0 (x y n)
    (equal (lior x y n)
           (lior0 x y n))))

 (local
  (defthm p0-holds-inductive-step
    (implies (and (not (zp n))
                  (not (equal n 1))
                  (p0 (fl (* x 1/2))
                      (fl (* y 1/2))
                      (+ -1 n))
                  (p0 (mod x 2) (mod y 2) 1))
             (p0 x y n))
    :hints (("Goal" :use (lior0-def binary-lior)))))

 (local
  (defthm p0-holds-base-1
    (p0 x y 1)
    :hints (("Goal" :in-theory (enable bitn)
             :expand ((binary-lior0 x y 1))))))

 (local
  (defthm p0-holds-base-0
    (implies (zp n)
             (p0 x y n))
    :hints (("Goal" :expand ((binary-lior0 x y n))))))

 (local
  (defthm p0-holds
    (p0 x y n)
    :hints (("Goal" :induct (lior x y n)
             :in-theory (disable p0)))
    :rule-classes nil))

 (defthmd lior-is-lior0
   (equal (lior x y n)
          (lior0 x y n))
   :hints (("Goal" :use p0-holds))))

(local (in-theory (e/d (lior-is-lior0))))

(add-macro-alias lior binary-lior)

(defthm lior-nonnegative-integer-type
  (and (integerp (lior x y n))
       (<= 0 (lior x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lior) is no better than lior-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lior)))

;drop this if we plan to keep natp enabled?
(defthm lior-natp
  (natp (lior x y n)))

(defthm lior-with-n-not-a-natp
  (implies (not (natp n))
           (equal (lior x y n)
                  0)))

(defthmd lior-bvecp-simple
  (bvecp (lior x y n) n))

(defthm lior-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lior x y n) k)))


;;
;; Rules to normalize lior terms (recall that LIOR is a macro for BINARY-LIOR):
;;

;; allow sizes to differ on these?

(defthm lior-associative
  (equal (lior (lior x y n) z n)
         (lior x (lior y z n) n)))

(defthm lior-commutative
  (equal (lior y x n)
         (lior x y n)))

(defthm lior-commutative-2
  (equal (lior y (lior x z n) n)
         (lior x (lior y z n) n)))

(defthm lior-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (lior x (lior y z n) n)
                  (lior (lior x y n) z n))))

(defthm lior-0
  (implies (case-split (bvecp y n))
           (equal (lior 0 y n)
                  y)))

;nicer than the analogous rule for logior?
(defthm lior-1
  (implies (case-split (bvecp y 1))
           (equal (lior 1 y 1)
                  1)))

(defthm lior-self
  (implies (and (case-split (bvecp x n))
                (case-split (integerp n)))
           (equal (lior x x n)
                  x)))

(defthmd bits-lior-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lior x y n) i j)
                  (lior (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j))))))

(defthmd bits-lior-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lior x y n) i j)
                  (lior (bits x i j)
                        (bits y i j)
                        (+ n (- j))))))

;notice the call to MIN in the conclusion
(defthm bits-lior
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (lior x y n) i j)
                  (lior (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-lior-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior x y n) m)
                  (lior (bitn x m)
                        (bitn y m)
                        1))))

(defthmd bitn-lior-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior x y n) m)
                  0)))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-lior
  (implies (and (case-split (<= 0 k))
                (case-split (integerp n))
                )
           (equal (bitn (lior x y n) k)
                  (if (< k n)
                      (lior (bitn x k)
                            (bitn y k)
                            1)
                    0))))

;or could wrap bits around conclusion?
(defthm lior-equal-0
  (implies (and (case-split (bvecp x n))
                (case-split (bvecp y n))
                (case-split (integerp n))
                )
           (equal (equal 0 (lior x y n))
                  (and (equal x 0)
                       (equal y 0)))))

(defthm lior-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (lior x y 1))
                  (and (equal x 0)
                       (equal y 0)))))

(defthm lior-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (lior x y 1))
                  (or (equal x 1)
                      (equal y 1)))))

(defthm lior-ones
  (implies (and (case-split (bvecp x n))
                (case-split (natp n)) ;gen
                )
           (equal (lior (1- (expt 2 n)) x n)
                  (1- (expt 2 n))))
  :hints (("Goal" :use lior0-ones))
  :rule-classes ())

;lior-with-all-ones will rewrite (lior x n) [note there's only one value being ANDed], because (lior x n)
;expands to (BINARY-LIOR X (ALL-ONES N) N) - now moot???
(defthm lior-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (lior (all-ones n) x n)
                  (all-ones n))))

(defthm lior-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
		(case-split (natp n))
                (case-split (bvecp x n)))
           (equal (lior k x n)
                  (1- (expt 2 n))))
  :hints (("Goal" :use lior-ones)))

(defthm lior-def-original
  (implies (and (< 0 n)
                (integerp n))
           (equal (lior x y n)
                  (+ (* 2 (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lior (mod x 2) (mod y 2) 1))))
  :hints (("Goal" :use lior0-def))
  :rule-classes ())

(defthm lior-mod-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (mod (lior x y n) 2)
                  (lior (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use lior0-mod-2)))

(defthm lior-fl-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (fl (/ (lior x y n) 2))
                  (lior (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use lior0-fl-2)))

(in-theory (disable lior-mod-2 lior-fl-2))

;BOZO rename
(defthm lior-x-y-0
  (equal (lior x y 0) 0))

(defthm lior-reduce
  (implies (and (bvecp x n)
                (bvecp y n)
                (< n m)
                (natp n) ;gen?
                (natp m)
                )
           (equal (lior x y m) (lior x y n))))

;whoa! this is a *lower* bound !
;make alt version?
(defthm lior-bnd
  (implies (case-split (bvecp x n))
           (<= x (lior x y n)))
  :rule-classes (:rewrite :linear))

;get rid of the bvecp hyps (do that for many lemmas like this one)
(defthm lior-with-shifted-arg
  (implies (and (bvecp y m)
                (bvecp x (- n m))
                (<= m n)
                (natp m)
                (integerp n)
                )
           (= (lior (* (expt 2 m) x) y n)
              (+ (* (expt 2 m) x) y)))
  :rule-classes ()
  :hints (("Goal" :use lior0-with-shifted-arg)))

(defthm lior-shift-original
  (implies (and (bvecp x (- n m))
                (bvecp y (- n m))
                (integerp n) ;(not (zp n))
                (natp m)
                (<= m n)
                )
           (= (lior (* (expt 2 m) x)
                    (* (expt 2 m) y)
                    n)
              (* (expt 2 m) (lior x y (- n m)))))
  :rule-classes ()
  :hints (("Goal" :use lior0-shift)))

(defthm lior-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (= (lior x (expt 2 k) n)
              (+ (bits x (1- n) 0)
                 (* (expt 2 k) (- 1 (bitn x k))))))
  :rule-classes ()
  :hints (("Goal" :use lior0-expt)))

;interesting.  not the same as lior-bvecp (here, m can be smaller than n)
;rename !!
(defthm lior-bvecp-2
  (implies (and (bvecp x m)
                (bvecp y m)
                )
           (bvecp (lior x y n) m)))

(defthm lior-upper-bound
  (< (lior x y n) (expt 2 n))
  :rule-classes (:rewrite :linear))

(defthm lior-upper-bound-tight
  (implies (<= 0 n)
           (<= (lior x y n) (1- (expt 2 n))))
  :rule-classes (:rewrite :linear))

(defthm lior-fl-1
  (equal (lior (fl x) y n)
         (lior x y n)))

(defthm lior-fl-2-eric
  (equal (lior x (fl y) n)
         (lior x y n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Added in move to rel5 (should perhaps be in a -proofs file):
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Start proof of fl-lior (copied from proof of fl-land).

(local
 (defun fl-lior-induction (k n)
   (if (zp k)
       n
     (fl-lior-induction (1- k) (1+ n)))))


(local
 (defthmd fl-lior-induction-step-1
   (implies (not (zp k))
            (equal (lior (fl (* x (/ (expt 2 k))))
                         (fl (* y (/ (expt 2 k))))
                         n)
                   (lior (fl (/ (fl (* x (/ (expt 2 (1- k))))) 2))
                         (fl (/ (fl (* y (/ (expt 2 (1- k))))) 2))
                         n)))
   :hints (("Goal" :in-theory (disable lior-fl-1
                                       lior-fl-2-eric
                                       lior-is-lior0
                                       fl/int-rewrite)
            :expand ((expt 2 k))
            :use ((:instance fl/int-rewrite
                             (x (* x (/ (expt 2 (1- k)))))
                             (n 2))
                  (:instance fl/int-rewrite
                             (x (* y (/ (expt 2 (1- k)))))
                             (n 2)))))))

(local
 (defthmd fl-lior-induction-step-2
   (equal (lior (fl (/ (fl (* x (/ (expt 2 (1- k))))) 2))
                (fl (/ (fl (* y (/ (expt 2 (1- k))))) 2))
                n)
          (fl (/ (lior (fl (* x (/ (expt 2 (1- k)))))
                       (fl (* y (/ (expt 2 (1- k)))))
                       (1+ n))
                 2)))
   :hints (("Goal" :in-theory (disable lior-fl-1
                                       lior-fl-2-eric
                                       lior-is-lior0
                                       fl/int-rewrite)
            :expand ((lior (fl (* x (/ (expt 2 (1- k)))))
                           (fl (* y (/ (expt 2 (1- k)))))
                           (1+ n)))))))

(local
 (defthmd fl-lior-induction-step-3
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (lior x y (+ k n))))
                        (lior (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (/ (lior (fl (* x (/ (expt 2 (1- k)))))
                                (fl (* y (/ (expt 2 (1- k)))))
                                (1+ n))
                          2))
                   (fl (/ (fl (* (/ (expt 2 (+ -1 k)))
                                 (lior x y (+ k n))))
                          2))))))

(local
 (defthmd fl-lior-induction-step-4
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (lior x y (+ k n))))
                        (lior (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (/ (fl (* (/ (expt 2 (+ -1 k)))
                                 (lior x y (+ k n))))
                          2))
                   (fl (* (/ (expt 2 k))
                          (lior x y (+ k n))))))
   :hints (("Goal" :expand ((expt 2 k))))))

(local
 (defthm fl-lior-induction-step
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (lior x y (+ k n))))
                        (lior (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (* (/ (expt 2 k))
                          (lior x y (+ k n))))
                   (lior (fl (* x (/ (expt 2 k))))
                         (fl (* y (/ (expt 2 k))))
                         n)))
   :hints (("Goal" :use (fl-lior-induction-step-1
                         fl-lior-induction-step-2
                         fl-lior-induction-step-3
                         fl-lior-induction-step-4)))))

(defthmd fl-lior
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (lior x y (+ n k)) (expt 2 k)))
                  (lior (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :induct (fl-lior-induction k n)
           :in-theory (disable lior-is-lior0 lior-fl-1 lior-fl-2-eric))))

(defthmd lior-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (lior x y n)
                  (+ (* 2 (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lior (bitn x 0) (bitn y 0) 1))))
  :hints (("Goal" :in-theory (enable bitn-rec-0)
           :use lior-def-original)))

(local
 (defun lior-shift-induction (n k)
   (if (zp k)
       (+ k n)
     (lior-shift-induction (1- n) (1- k)))))

(defthm lior-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (lior (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (lior x y (- n k)))))
  :hints (("Goal" :induct (lior-shift-induction n k)
           :expand ((expt 2 k))
           :in-theory (e/d (bitn-negative-bit-of-integer)
                           (lior-is-lior0))))
  :rule-classes ())

; See land.lisp for analogous lemma and a hand proof of it.
(defthmd mod-lior
  (implies (and (integerp n)
                (<= k n))
           (equal (mod (lior x y n) (expt 2 k))
                  (lior x y k)))
  :hints (("Goal"
           :use
           ((:instance bits-lior (x x) (y y) (n k) (i (1- k)) (j 0))
            (:instance mod-bits (x (lior x y n)) (i (1- n)) (j k))))))

(defthmd lior-bits-1
  (equal (lior (bits x (1- n) 0)
               y
               n)
         (lior x y n))
  :hints (("Goal" :use lior0-bits-1)))

(defthmd lior-bits-2
  (equal (lior x
               (bits y (1- n) 0)
               n)
         (lior x y n))
  :hints (("Goal" :use lior0-bits-2)))

(defthm lior-base
  (equal (lior x y 1)
         (if (or (equal (bitn x 0) 1)
                 (equal (bitn y 0) 1))
             1
           0))
  :hints (("Goal" :use lior0-base))
  :rule-classes nil)
