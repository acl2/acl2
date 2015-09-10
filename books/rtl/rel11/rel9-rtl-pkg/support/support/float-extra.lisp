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

; This book was originally certified (in a different directory, not support/)
; starting with:

; (include-book "rtl/rel4/lib/top" :dir :system)

; Then that form was replaced by the forms below starting with (include-book
; "sticky"), up through the form (local (in-theory (theory 'lib-top1))).  See
; the comments at the top of fadd-extra.lisp for further explanation of how to
; extend the library.

; But first, we need the following before including rtl books -- otherwise we
; get a conflict of the rtl books with the arithmetic library.

(local
 (encapsulate
  ()

  (local (include-book "arithmetic/inequalities" :dir :system))
  (set-enforce-redundancy t)

  (defmacro acl2::fc (x) x)

  (defthm acl2::expt-is-increasing-for-base>1
    (implies (and (< 1 r)
                  (< i j)
                  (acl2::fc (real/rationalp r))
                  (acl2::fc (integerp i))
                  (acl2::fc (integerp j)))
             (< (expt r i) (expt r j)))
    :rule-classes (:rewrite :linear))

  (in-theory (disable (:rewrite acl2::expt-is-increasing-for-base>1)))))

(include-book "sticky") ; needed for some definitions
(include-book "util")   ; needed for definition of local-defthm

; Now put ourselves in what amounts to the environment of ../lib/top, as
; explained above.
(local (include-book "top1"))
(local (in-theory (theory 'lib-top1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; fp- definition and lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; "Transcription" by Matt Kaufmann into ACL2 of hand proofs supplied by David
; Russinoff (shown below). August 2005.

(defun fp- (x n)
  (if (= x (expt 2 (expo x)))
      (- x (expt 2 (- (expo x) n)))
    (- x (expt 2 (- (1+ (expo x)) n)))))

; Lemma 1.  If x>0, x n-exact, and y = fp-(x,n), then y is n-exact and fp+(y,n)
; = x.

; Proof.  Let e = expo(x).

; Case 1 [fp--lemma-1-1]: x = 2^e.

; y = x - 2^(e-n) by definition of fp-.

; 2^e > y = x - 2^(e-n) >= 2^e - 2^(e-1) = 2^(e-1);
; so [fp--lemma-1-1-1] expo(y) = e-1 by expo-unique.

; By exactp2, y is n-exact if y*2^(n-1-expo(y)) is an integer.  But we have:
; y*2^(n-1-expo(y)) = y*2^(n-e) = (x-2^(e-n))*2^(n-e) = (2^e-2^(e-n))*2^(n-e) =
; 2^n-1, which is an integer.

; fp+(y,n) = y + 2^(expo(y)+1-n) = y + 2^(e-n) = x.

; Case 2 [fp--lemma-1-2]: x != 2^e.

; [fp--lemma-1-2-1-1-1] By fp+2, x >= fp+(2^e,n) = 2^e + 2^(e+1-n) by expo-2**n.

; By definition of fp-, y = x - 2^(e+1-n) >= 2^e by the step just above.

; So [fp--lemma-1-2-1-1] 2^e <= y; and, y < x <= 2^(e+1) by expo-upper-bound.
; Therefore by expo-unique, expo(y) = e.

; By exactp2, y is n-exact if y*2^(n-1-expo(y)) is an integer.  But we have:
; y*2^(n-1-expo(y)) = y*2^(n-1-e) = (x-2^(e+1-n))*2^(n-1-e) =
; x*2^(n-1-e) - 1, whicn is an integer by exactp2 because x is n-exact.

; Finally, fp+(y,n) = y + 2^(expo(y)+1-n) = y + 2^(e+1-n) = x.

(local-defthm expt-hack
    (implies (and (integerp n)
                  (> n 0))
             (<= (expt 2 (* -1 n)) 1/2))
    :hints (("Goal" :use ((:instance acl2::expt-is-increasing-for-base>1
                                     (r 2)
                                     (i (* -1 n))
                                     (j -1)))))
    :rule-classes :linear)

; We deliberately export useful type-prescription rule fp--non-negative.
(encapsulate
 ()

 (set-non-linearp t)

; Expt-hack is used in the proof of the following.

 (defthm fp--non-negative
   (implies (and (rationalp x)
                 (integerp n)
                 (> n 0)
                 (> x 0))
            (and (rationalp (fp- x n))
                 (< 0 (fp- x n))))
   :hints (("Goal" :in-theory (e/d (expt-split fp-) (a15))
            :use expo-lower-bound))
   :rule-classes :type-prescription))

(local
 (encapsulate
  ()

  (set-non-linearp t)

  (local-defthm fp--lemma-1-1-1-1-1
    (implies (and (integerp n)
                  (< 0 n)
                  (equal x (expt 2 (expo x))))
             (<= (+ (expt 2 (+ -1 (expo x)))
                    (expt 2 (+ (expo x) (* -1 n))))
                 x))
    :hints (("Goal" :in-theory (e/d (expt-split fp-) (a15)))))

  (defthm fp--lemma-1-1-1-1
    (implies (and (rationalp x)
                  (> x 0)
                  (integerp n)
                  (> n 0)
                  (exactp x n)
                  (equal y (fp- x n))
                  (equal e (expo x))
                  (equal x (expt 2 e)))
             (>= y (expt 2 (- e 1))))
    :rule-classes nil)))

(local-defthm fp--lemma-1-1-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp- x n))
                (equal e (expo x))
                (equal x (expt 2 e)))
           (equal (expo y) (- e 1)))
  :hints (("Goal" :use (fp--lemma-1-1-1-1
                        (:instance expo-unique
                                   (x y)
                                   (n (- e 1))))))
  :rule-classes nil)

(local-defthm fp--lemma-1-1-2-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp- x n))
                (equal e (expo x))
                (equal x (expt 2 e)))
           (equal (* y (expt 2 (- (- n 1) (expo y))))
                  (1- (expt 2 n))))
   :hints (("Goal" :use fp--lemma-1-1-1))
  :rule-classes nil)

(local-defthm fp--lemma-1-1-2
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp- x n))
                (equal e (expo x))
                (equal x (expt 2 e)))
           (exactp y n))
  :hints (("Goal" :use (fp--lemma-1-1-2-1
                        (:instance exactp2 (x y) (n n)))))
  :rule-classes nil)

(local-defthm fp--lemma-1-1-3
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp- x n))
                (equal e (expo x))
                (equal x (expt 2 e)))
           (equal (fp+ y n) x))
  :hints (("Goal" :use fp--lemma-1-1-1))
  :rule-classes nil)

(local-defthm fp--lemma-1-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp- x n))
                (equal e (expo x))
                (equal x (expt 2 e)))
           (and (exactp y n)
                (equal (fp+ y n) x)))
  :hints (("Goal" :use (fp--lemma-1-1-2
                        fp--lemma-1-1-3)))
  :rule-classes nil)

(local
 (encapsulate
  ()

  (local-defthm fp--lemma-1-2-1-1-1
    (implies (and (rationalp x)
                  (> x 0)
                  (integerp n)
                  (> n 0)
                  (exactp x n)
                  (equal e (expo x))
                  (not (equal x (expt 2 e))))
             (>= x (+ (expt 2 e)
                      (expt 2 (+ 1 e (- n))))))
    :hints (("Goal" :use ((:instance fp+2
                                     (n n)
                                     (y x)
                                     (x (expt 2 e)))
                          (:instance expo-lower-bound
                                     (x x)))
             :in-theory (enable exactp-2**n)))
    :rule-classes nil)

  (defthm fp--lemma-1-2-1-1
    (implies (and (rationalp x)
                  (> x 0)
                  (integerp n)
                  (> n 0)
                  (exactp x n)
                  (equal y (fp- x n))
                  (equal e (expo x))
                  (not (equal x (expt 2 e))))
             (equal (expo y) e))
    :hints (("Goal" :use (fp--lemma-1-2-1-1-1
                          (:instance expo-upper-bound (x x))
                          (:instance expo-unique (x y) (n e)))))
    :rule-classes nil)))

(local-defthm fp--lemma-1-2-1-2
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp- x n))
                 (equal e (expo x))
                 (not (equal x (expt 2 e))))
            (equal (* y (expt 2 (- (1- n) e)))
                   (1- (* x (expt 2 (- (- n 1) e))))))
   :rule-classes nil)

(local-defthm fp--lemma-1-2-1
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp- x n))
                 (equal e (expo x))
                 (not (equal x (expt 2 e))))
            (exactp y n))
   :hints (("Goal" :use (fp--lemma-1-2-1-1
                         fp--lemma-1-2-1-2
                         (:instance exactp2 (x x) (n n))
                         (:instance exactp2 (x y) (n n)))))
   :rule-classes nil)

(local-defthm fp--lemma-1-2-2
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp- x n))
                 (equal e (expo x))
                 (not (equal x (expt 2 e))))
            (equal (fp+ y n) x))
   :hints (("Goal" :use (fp--lemma-1-2-1-1)))
   :rule-classes nil)

(local-defthm fp--lemma-1-2
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp- x n))
                 (equal e (expo x))
                 (not (equal x (expt 2 e))))
            (and (exactp y n)
                 (equal (fp+ y n) x)))
   :hints (("Goal" :use (fp--lemma-1-2-1 fp--lemma-1-2-2)))
   :rule-classes nil)

(local-defthm fp--lemma-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp- x n)))
           (and (exactp y n)
                (equal (fp+ y n) x)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fp--lemma-1-1 (e (expo x)))
                        (:instance fp--lemma-1-2 (e (expo x)))))))

(local-defthm fp-2-lemma
  (implies (and (integerp n)
                (> n 0))
           (not (equal (fp- (fp+ 0 n) n) 0)))
  :hints (("Goal" :use ((:instance expt-weak-monotone
                                   (n (+ 1 (* -2 n)))
                                   (m (+ 1 (* -1 n))))
                        (:instance expt-weak-monotone
                                   (m (+ 1 (* -2 n)))
                                   (n (+ 1 (* -1 n)))))))

  :rule-classes ())

(defthm fp-2
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0)
                (> x y)
                (integerp n)
                (> n 0)
                (exactp x n)
                (exactp y n))
           (<= y (fp- x n)))
  :hints (("Goal" :use ((:instance fp+2
                                   (x (fp- x n))
                                   (y y))
                        (:instance fp--lemma-1
                                   (x x)
                                   (y (fp- x n)))
                        fp-2-lemma)
           :in-theory (disable fp- fp+)))
  :rule-classes ())

(defthm fp-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (exactp (fp- x n) n))
  :hints (("Goal" :use ((:instance fp--lemma-1
                                   (x x)
                                   (y (fp- x n))))))
  :rule-classes ())

(defthm fp+-
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp+ (fp- x n) n)
                  x))
  :hints (("Goal" :use ((:instance fp--lemma-1
                                   (y (fp- x n)))))))

; Lemma 2.  If x>0, x is n-exact, and y = fp+(x,n), then fp-(y,n) = x.

; Proof.  Let e = expo(x).  Then y = x + 2^(e+1-n).

; Case 1 [fp--lemma-2-1]: y < 2^(e+1).

; Then [fp--lemma-2-1-1] expo(y) = e by expo-unique.

; Since y != 2^e, fp-(y,n) = y - 2^(e+1-n) = x.

; Case 2 [fp--lemma-2-2]: y >= 2^(e+1).

; By fp+2, since 2^(e+1) is n-exact by exactp-2**n, then 2^(e+1) >= y
; [fp--lemma-2-2-1].  So y = 2^(e+1), and the result follows by definition of fp-.

(local-defthm fp--lemma-2-1-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp+ x n))
                (equal e (expo x))
                (< y (expt 2 (1+ e))))
           (equal (expo y) e))
  :hints (("Goal" :use ((:instance expo-lower-bound (x x))
                        (:instance expo-unique (x y) (n e)))))
  :rule-classes nil)

(local-defthm fp--lemma-2-1
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp+ x n))
                 (equal e (expo x))
                 (< y (expt 2 (1+ e))))
            (equal (fp- y n) x))
   :hints (("Goal" :use (fp--lemma-2-1-1 expo-lower-bound)))
   :rule-classes nil)

(local-defthm fp--lemma-2-2-1
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp+ x n))
                 (equal e (expo x))
                 (>= y (expt 2 (1+ e))))
            (>= (expt 2 (1+ e)) y))
   :hints (("Goal" :use ((:instance fp+2 (x x) (y (expt 2 (1+ e))))
                         expo-upper-bound)
            :in-theory (enable exactp-2**n)))
   :rule-classes nil)

(local-defthm fp--lemma-2-2
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (exactp x n)
                 (equal y (fp+ x n))
                 (equal e (expo x))
                 (>= y (expt 2 (1+ e))))
            (equal (fp- y n) x))
   :hints (("Goal" :use (fp--lemma-2-2-1)))
   :rule-classes nil)

(local-defthm fp--lemma-2
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (equal y (fp+ x n)))
           (equal (fp- y n) x))
  :hints (("Goal" :use ((:instance fp--lemma-2-1 (e (expo x)))
                        (:instance fp--lemma-2-2 (e (expo x))))))
  :rule-classes nil)

(defthm fp-+
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp- (fp+ x n) n)
                  x))
  :hints (("Goal" :use ((:instance fp--lemma-2
                                   (y (fp+ x n)))))))

; Start proof of expo-prod.

(local-defthm expo-prod-1
  (implies (and (rationalp x)
                (not (= x 0))
                (rationalp y)
                (not (= y 0)))
           (equal (* x y)
                  (* (sgn x)
                     (sgn y)
                     (sig x)
                     (sig y)
                     (expt 2 (+ (expo x) (expo y))))))
  :hints (("Goal" :use ((:instance fp-rep (x x))
                        (:instance fp-rep (x y)))
           :in-theory (e/d (expt-split) (a15))))
  :rule-classes nil)

(local-defthm expo-prod-2
  (implies (and (rationalp x)
                (not (= x 0))
                (rationalp y)
                (not (= y 0))
                (< (* (sig x) (sig y)) 2))
           (equal (expo (* x y))
                  (+ (expo x) (expo y))))
  :hints (("Goal" :use (expo-prod-1
                        (:instance fp-rep-unique
                                   (x (* x y))
                                   (m (* (sig x) (sig y)))
                                   (e (+ (expo x) (expo y))))
                        (:instance sig-lower-bound
                                   (x x))
                        (:instance sig-lower-bound
                                   (x y)))
           :in-theory (enable sgn)))
  :rule-classes nil)

(local-defthm expo-prod-3-1
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal x 0))
                (not (equal y 0))
                (not (< (* (sig x) (sig y)) 2)))
           (and (< (* 1/2 (sig x) (sig y))
                   2)
                (>= (* 1/2 (sig x) (sig y))
                    1)))
  :hints (("Goal" :use ((:instance sig-upper-bound
                                   (x x))
                        (:instance sig-upper-bound
                                   (x y))
                        (:instance sig-lower-bound
                                   (x x))
                        (:instance sig-lower-bound
                                   (x y)))))
  :rule-classes nil)

(local
 (encapsulate
  ()

  (local-defthm hack
    (implies (and (syntaxp (quotep k))
                  (integerp k))
             (equal (expt 2 (+ k (expo x) (expo y)))
                    (* (expt 2 k)
                       (expt 2 (+ (expo x) (expo y))))))
    :hints (("Goal" :in-theory (e/d (expt-split) (a15)))))

  (defthm expo-prod-3
    (implies (and (rationalp x)
                  (not (= x 0))
                  (rationalp y)
                  (not (= y 0))
                  (not (< (* (sig x) (sig y)) 2)))
             (equal (expo (* x y))
                    (+ 1 (expo x) (expo y))))
    :hints (("Goal" :use (expo-prod-1
                          expo-prod-3-1
                          (:instance fp-rep-unique
                                     (x (* x y))
                                     (m (* 1/2 (sig x) (sig y)))
                                     (e (+ 1 (expo x) (expo y)))))
             :in-theory (e/d (sgn) (expt a15))))
    :rule-classes nil)))

(defthmd expo-prod
  (implies (and (rationalp x)
                (not (= x 0))
                (rationalp y)
                (not (= y 0)))
           (equal (expo (* x y))
                  (if (< (* (sig x) (sig y)) 2)
                      (+ (expo x) (expo y))
                    (+ 1 (expo x) (expo y)))))
  :hints (("Goal" :use (expo-prod-2 expo-prod-3))))

(defthmd sig-prod
  (implies (and (rationalp x)
                (not (= x 0))
                (rationalp y)
                (not (= y 0)))
           (equal (sig (* x y))
                  (if (< (* (sig x) (sig y)) 2)
                      (* (sig x) (sig y))
                    (* 1/2 (sig x) (sig y)))))
  :hints (("Goal" :in-theory (e/d (expt-split sig expo-prod) (a15)))))

; This is essentially just fp+1-2, but it happens to be convenient just to tack
; it on here.
(defthm fp+expo
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n)
                (not (= (expo (fp+ x n)) (expo x))))
           (equal (fp+ x n) (expt 2 (1+ (expo x)))))
  :hints (("Goal" :use fp+1-2))
  :rule-classes ())
