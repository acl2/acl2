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

; Port lxor0 theorems to lxor.  The original definition of lxor (in rel4) was
; that of lxor0 in the current release.  So the port is to keep all the lemmas
; about lxor0 and then use equality of lxor0 with lxor to port them to lxor.

(in-package "ACL2")

(include-book "lxor0")
(local (include-book "top1")) ; for lxor0-bits-1 and lxor0-bits-2

(defun binary-lxor (x y n)
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
              (if (iff (equal (bitn x 0) 1)
                       (equal (bitn y 0) 1))
                  0
                1))
             (t (+ (* 2 (binary-lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lxor (mod x 2) (mod y 2) 1))))
       :exec ; (lxor0 x y n)
       (logxor (bits x (1- n) 0)
               (bits y (1- n) 0))))

(defmacro lxor (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lxor x y n) -- the base case
         `(binary-lxor ,@x))
        (t
         `(binary-lxor ,(car x)
                       (lxor ,@(cdr x))
                       ,(car (last x))))))

; We attempt to derive all lxor results from corresponding lxor0 results.

(encapsulate
 ()

 (local
  (defun p0 (x y n)
    (equal (lxor x y n)
           (lxor0 x y n))))

 (local
  (defthm p0-holds-inductive-step
    (implies (and (not (zp n))
                  (not (equal n 1))
                  (p0 (fl (* x 1/2))
                      (fl (* y 1/2))
                      (+ -1 n))
                  (p0 (mod x 2) (mod y 2) 1))
             (p0 x y n))
    :hints (("Goal" :use (lxor0-def binary-lxor)))))

 (local
  (defthm p0-holds-base-1
    (p0 x y 1)
    :hints (("Goal" :in-theory (enable bitn)
             :expand ((binary-lxor0 x y 1))))))

 (local
  (defthm p0-holds-base-0
    (implies (zp n)
             (p0 x y n))
    :hints (("Goal" :expand ((binary-lxor0 x y n))))))

 (local
  (defthm p0-holds
    (p0 x y n)
    :hints (("Goal" :induct (lxor x y n)
             :in-theory (disable p0)))
    :rule-classes nil))

 (defthmd lxor-is-lxor0
   (equal (lxor x y n)
          (lxor0 x y n))
   :hints (("Goal" :use p0-holds))))

(local (in-theory (e/d (lxor-is-lxor0) (binary-lxor))))

;Allows things like (in-theory (disable lxor)) to refer to binary-lxor.
(add-macro-alias lxor binary-lxor)

(defthm lxor-nonnegative-integer-type
  (and (integerp (lxor x y n))
       (<= 0 (lxor x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lxor) is no better than lxor-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lxor)))

;drop this if we plan to keep natp enabled?
(defthm lxor-natp
  (natp (lxor x y n)))

(defthm lxor-with-n-not-a-natp
  (implies (not (natp n))
           (equal (lxor x y n)
                  0)))

(defthmd lxor-bvecp-simple
  (bvecp (lxor x y n) n))

(defthm lxor-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lxor x y n) k)))


;;
;; Rules to normalize lxor terms (recall that LXOR is a macro for BINARY-LXOR):
;;

;; allow sizes to differ on these?

(defthm lxor-associative
  (equal (lxor (lxor x y n) z n)
         (lxor x (lxor y z n) n)))

(defthm lxor-commutative
  (equal (lxor y x n)
         (lxor x y n)))

(defthm lxor-commutative-2
  (equal (lxor y (lxor x z n) n)
         (lxor x (lxor y z n) n)))

(defthm lxor-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (lxor x (lxor y z n) n)
                  (lxor (lxor x y n) z n))))

(defthm lxor-0
  (implies (case-split (bvecp y n))
           (equal (lxor 0 y n)
                  y)))

;nicer than the analogous rule for logand?
(defthm lxor-1
  (implies (case-split (bvecp y 1))
           (equal (lxor 1 y 1)
                  (lnot y 1))))

(defthm lxor-self
  (implies (case-split (bvecp x n))
           (equal (lxor x x n)
                  0)))


(defthmd bits-lxor-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lxor x y n) i j)
                  (lxor (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j))))))

(defthmd bits-lxor-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lxor x y n) i j)
                  (lxor (bits x i j)
                        (bits y i j)
                        (+ n (- j))))))

;notice the call to MIN in the conclusion
(defthm bits-lxor
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (lxor x y n) i j)
                  (lxor (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-lxor-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor x y n) m)
                  (lxor (bitn x m)
                        (bitn y m)
                        1))))
(defthmd bitn-lxor-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor x y n) m)
                  0)))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-lxor
  (implies (and (case-split (<= 0 k))
                (case-split (integerp n))
                )
           (equal (bitn (lxor x y n) k)
                  (if (< k n)
                      (lxor (bitn x k)
                            (bitn y k)
                            1)
                    0))))


(defthm lxor-ones
  (implies (case-split (bvecp x n))
           (equal (lxor (1- (expt 2 n)) x n)
                  (lnot x n)))
  :rule-classes ()
  :hints (("Goal" :use lxor0-ones)))

;lxor-with-all-ones will rewrite (lxor x n) [note there's only one value being ANDed], because (lxor x n)
;expands to (BINARY-LXOR X (ALL-ONES N) N) - now moot???
(defthm lxor-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (lxor (all-ones n) x n)
                  (lnot x n))))

(defthm lxor-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
                (case-split (bvecp x n)))
           (equal (lxor k x n)
                  (lnot x n)))
  :hints (("Goal" :use lxor0-ones-rewrite)))

(defthm lxor-def-original
  (implies (and (< 0 n)
                (integerp n))
           (equal (lxor x y n)
                  (+ (* 2 (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lxor (mod x 2) (mod y 2) 1))))
  :rule-classes ()
  :hints (("Goal" :use lxor0-def)))

(defthm lxor-mod-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (mod (lxor x y n) 2)
                  (lxor (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use lxor0-mod-2)))

(defthm lxor-fl-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (fl (/ (lxor x y n) 2))
                  (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use lxor0-fl-2)))

(in-theory (disable lxor-mod-2 lxor-fl-2))

(defthm bitn-lxor-0
  (implies (and (integerp x)
                (integerp y)
                (not (zp n))
                )
           (= (bitn (lxor x y n) 0)
              (bitn (+ x y) 0)))
  :rule-classes ()
  :hints (("Goal" :use bitn-lxor0-0)))

;BOZO rename
(defthm lxor-x-y-0
  (equal (lxor x y 0) 0))


;N is a free variable
(defthm lxor-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (< n m)
		  (case-split (integerp m))
		  )
	     (equal (lxor x y m)
                    (lxor x y n))))

(defthm lxor-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (lxor x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear))

(defthm lxor-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (lxor x y n) (1- (expt 2 n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Added in move to rel5 (should perhaps be in a -proofs file):
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm lxor-bvecp-2
  (implies (and (bvecp x m)
                (bvecp y m))
           (bvecp (lxor x y n) m))
  :hints (("Goal" :use ((:instance lxor-reduce
                                   (n m)
                                   (m n))))))

; Start proof of fl-lxor (copied from proof of fl-land with very small changes).

(local
 (defun fl-lxor-induction (k n)
   (if (zp k)
       n
     (fl-lxor-induction (1- k) (1+ n)))))


(local
 (defthmd fl-lxor-induction-step-1
   (implies (not (zp k))
            (equal (lxor (fl (* x (/ (expt 2 k))))
                         (fl (* y (/ (expt 2 k))))
                         n)
                   (lxor (fl (/ (fl (* x (/ (expt 2 (1- k))))) 2))
                         (fl (/ (fl (* y (/ (expt 2 (1- k))))) 2))
                         n)))
   :hints (("Goal" :in-theory (disable lxor-is-lxor0
                                       fl/int-rewrite)
            :expand ((expt 2 k))
            :use ((:instance fl/int-rewrite
                             (x (* x (/ (expt 2 (1- k)))))
                             (n 2))
                  (:instance fl/int-rewrite
                             (x (* y (/ (expt 2 (1- k)))))
                             (n 2)))))))

(local
 (defthmd fl-lxor-induction-step-2
   (equal (lxor (fl (/ (fl (* x (/ (expt 2 (1- k))))) 2))
                (fl (/ (fl (* y (/ (expt 2 (1- k))))) 2))
                n)
          (fl (/ (lxor (fl (* x (/ (expt 2 (1- k)))))
                       (fl (* y (/ (expt 2 (1- k)))))
                       (1+ n))
                 2)))
   :hints (("Goal" :in-theory (disable lxor-is-lxor0
                                       fl/int-rewrite)
            :expand ((lxor (fl (* x (/ (expt 2 (1- k)))))
                           (fl (* y (/ (expt 2 (1- k)))))
                           (1+ n)))))))

(local
 (defthmd fl-lxor-induction-step-3
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (lxor x y (+ k n))))
                        (lxor (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (/ (lxor (fl (* x (/ (expt 2 (1- k)))))
                                (fl (* y (/ (expt 2 (1- k)))))
                                (1+ n))
                          2))
                   (fl (/ (fl (* (/ (expt 2 (+ -1 k)))
                                 (lxor x y (+ k n))))
                          2))))))

(local
 (defthmd fl-lxor-induction-step-4
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (lxor x y (+ k n))))
                        (lxor (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (/ (fl (* (/ (expt 2 (+ -1 k)))
                                 (lxor x y (+ k n))))
                          2))
                   (fl (* (/ (expt 2 k))
                          (lxor x y (+ k n))))))
   :hints (("Goal" :expand ((expt 2 k))))))

(local
 (defthm fl-lxor-induction-step
   (implies (and (not (zp k))
                 (equal (fl (* (/ (expt 2 (+ -1 k)))
                               (lxor x y (+ k n))))
                        (lxor (fl (* x (/ (expt 2 (+ -1 k)))))
                              (fl (* y (/ (expt 2 (+ -1 k)))))
                              (+ 1 n)))
                 (natp x)
                 (natp y)
                 (natp n))
            (equal (fl (* (/ (expt 2 k))
                          (lxor x y (+ k n))))
                   (lxor (fl (* x (/ (expt 2 k))))
                         (fl (* y (/ (expt 2 k))))
                         n)))
   :hints (("Goal" :use (fl-lxor-induction-step-1
                         fl-lxor-induction-step-2
                         fl-lxor-induction-step-3
                         fl-lxor-induction-step-4)))))

(defthmd fl-lxor
  (implies (and (natp x)
                (natp y)
                (natp n)
                (natp k))
           (equal (fl (/ (lxor x y (+ n k)) (expt 2 k)))
                  (lxor (fl (/ x (expt 2 k))) (fl (/ y (expt 2 k))) n)))
  :hints (("Goal" :induct (fl-lxor-induction k n)
           :in-theory (disable lxor-is-lxor0))))

(defthm lxor-fl-1
  (equal (lxor (fl x) y n)
         (lxor x y n))
  :hints (("Goal" :in-theory (enable lxor lxor0))))

(defthm lxor-fl-2-eric
  (equal (lxor x (fl y) n)
         (lxor x y n))
  :hints (("Goal" :in-theory (enable lxor lxor0))))

(defthmd lxor-def
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (> n 0))
           (equal (lxor x y n)
                  (+ (* 2 (lxor (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (lxor (bitn x 0) (bitn y 0) 1))))
  :hints (("Goal" :in-theory (enable bitn-rec-0)
           :use lxor-def-original)))

(local
 (defun lxor-shift-induction (n k)
   (if (zp k)
       (+ k n)
     (lxor-shift-induction (1- n) (1- k)))))

(defthm lxor-shift
  (implies (and (integerp x)
                (integerp y)
                (natp k))
           (= (lxor (* (expt 2 k) x)
                    (* (expt 2 k) y)
                    n)
              (* (expt 2 k) (lxor x y (- n k)))))
  :hints (("Goal" :induct (lxor-shift-induction n k)
           :expand ((expt 2 k)
                    (lxor (* 2 x (expt 2 (+ -1 k)))
                          (* 2 y (expt 2 (+ -1 k)))
                          n))
           :in-theory (e/d (bitn-negative-bit-of-integer)
                           (lxor-is-lxor0))))
  :rule-classes ())

; See land.lisp for analogous lemma and a hand proof of it.
(defthmd mod-lxor
  (implies (and (integerp n)
                (integerp k)
                (<= k n))
           (equal (mod (lxor x y n) (expt 2 k))
                  (lxor x y k)))
  :hints (("Goal"
           :use
           ((:instance bits-lxor (x x) (y y) (n k) (i (1- k)) (j 0))
            (:instance mod-bits (x (lxor x y n)) (i (1- n)) (j k))))))

(defthmd lxor-bits-1
  (equal (lxor (bits x (1- n) 0)
               y
               n)
         (lxor x y n))
  :hints (("Goal" :use lxor0-bits-1)))

(defthmd lxor-bits-2
  (equal (lxor x
               (bits y (1- n) 0)
               n)
         (lxor x y n))
  :hints (("Goal" :use lxor0-bits-2)))

(defthm lxor-base
  (equal (lxor x y 1)
         (if (iff (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             0
           1))
  :hints (("Goal" :use lxor0-base))
  :rule-classes nil)
