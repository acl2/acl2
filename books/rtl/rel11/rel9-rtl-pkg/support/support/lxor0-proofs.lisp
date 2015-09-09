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

#|

This book is about LXOR0, a nice version of LOGXOR.  LXOR0 takes an extra size parameter, N, and always returns
a bit vector of length N.

todo: ;add analogs of the thms in land0.lisp past bitn-land0

|#

;add macro alias

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund all-ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n)
      0 ;degenerate case
    (1- (expt 2 n))))

(local (include-book "all-ones"))
(local (include-book "merge"))
(local (include-book "bvecp"))
(local (include-book "logand"))
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "../../arithmetic/top"))


(defund binary-lxor0 (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logxor (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro lxor0 (&rest x)
  (declare (xargs :guard (consp x)))
  (cond ((endp (cdddr x)) ;(lxor0 x y n) -- the base case
         `(binary-lxor0 ,@x))
        (t
         `(binary-lxor0 ,(car x)
                       (lxor0 ,@(cdr x))
                       ,(car (last x))))))


;Allows things like (in-theory (disable lxor0)) to refer to binary-lxor0.
(add-macro-alias lxor0 binary-lxor0)


(defthm lxor0-nonnegative-integer-type
  (and (integerp (lxor0 x y n))
       (<= 0 (lxor0 x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lxor0) is no better than lxor0-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lxor0)))

;drop this if we plan to keep natp enabled?
(defthm lxor0-natp
  (natp (lxor0 x y n)))

(defthm lxor0-with-n-not-a-natp
  (implies (not (natp n))
           (equal (lxor0 x y n)
                  0))
  :hints (("Goal" :cases ((acl2-numberp n))
           :in-theory (enable lxor0)))
  )

(defthmd lxor0-bvecp-simple
  (bvecp (lxor0 x y n) n)
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable lxor0))))

(defthm lxor0-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lxor0 x y n) k))
  :hints (("Goal" :in-theory (disable lxor0-bvecp-simple)
           :use lxor0-bvecp-simple)))


;;
;; Rules to normalize lxor0 terms (recall that LXOR0 is a macro for BINARY-LXOR0):
;;

;; allow sizes to differ on these?

(defthm lxor0-associative
  (equal (lxor0 (lxor0 x y n) z n)
         (lxor0 x (lxor0 y z n) n))
  :hints (("Goal" :cases ((natp n))
           :in-theory (enable lxor0 bits-tail))))

(defthm lxor0-commutative
  (equal (lxor0 y x n)
         (lxor0 x y n))
  :hints (("Goal" :in-theory (enable lxor0))))

(defthm lxor0-commutative-2
  (equal (lxor0 y (lxor0 x z n) n)
         (lxor0 x (lxor0 y z n) n))
  :hints (("Goal"  :cases ((natp n))
           :in-theory (enable lxor0 bits-tail))))

(defthm lxor0-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (lxor0 x (lxor0 y z n) n)
                  (lxor0 (lxor0 x y n) z n))))

(defthm lxor0-0
  (implies (case-split (bvecp y n))
           (equal (lxor0 0 y n)
                  y))
  :hints (("Goal" :in-theory (enable lxor0 bits-tail))))

;nicer than the analogous rule for logand?
(defthm lxor0-1
  (implies (case-split (bvecp y 1))
           (equal (lxor0 1 y 1)
                  (lnot y 1)))
  :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))

(defthm lxor0-self
  (implies (case-split (bvecp x n))
           (equal (lxor0 x x n)
                  0))
  :hints (("Goal" :in-theory (enable lxor0 bits-tail))))


(defthmd bits-lxor0-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lxor0 x y n) i j)
                  (lxor0 (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable lxor0 bits-logand))))


(defthmd bits-lxor0-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lxor0 x y n) i j)
                  (lxor0 (bits x i j)
                        (bits y i j)
                        (+ n (- j)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable lxor0 bits-logand))))

;notice the call to MIN in the conclusion
(defthm bits-lxor0
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (lxor0 x y n) i j)
                  (lxor0 (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j)))))
  :hints (("Goal" :in-theory (enable bits-lxor0-1 bits-lxor0-2))))

(defthmd bitn-lxor0-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor0 x y n) m)
                  (lxor0 (bitn x m)
                        (bitn y m)
                        1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '(BITS-N-N-REWRITE)))))
(defthmd bitn-lxor0-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor0 x y n) m)
                  0))
  :hints (("Goal" :in-theory (enable BVECP-BITN-0))))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-lxor0
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lxor0 x y n) m)
                  (if (< m n)
                      (lxor0 (bitn x m)
                            (bitn y m)
                            1)
                    0)))
  :hints (("Goal" :in-theory (enable bitn-lxor0-1 bitn-lxor0-2))))


(defthm lxor0-ones
  (implies (case-split (bvecp x n))
           (equal (lxor0 (1- (expt 2 n)) x n)
                  (lnot x n)))
  :rule-classes ()
  :hints
  (("subgoal 1" :use logxor-ones)
   ("goal" :cases ((natp n))
    :in-theory (enable lxor0 bits-tail)
    )))

;lxor0-with-all-ones will rewrite (lxor0 x n) [note there's only one value being ANDed], because (lxor0 x n)
;expands to (BINARY-LXOR0 X (ALL-ONES N) N) - now moot???
(defthm lxor0-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (lxor0 (all-ones n) x n)
                  (lnot x n)))
  :hints
  (("goal" :use lxor0-ones
    :in-theory (enable all-ones))))

(defthm lxor0-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
                (case-split (bvecp x n)))
           (equal (lxor0 k x n)
                  (lnot x n)))
  :hints (("Goal" :use lxor0-ones)))

(local (in-theory (disable mod-by-2-rewrite-to-even mod-mult-of-n mod-equal-0)))

(encapsulate
 ()

 (local
  (defthm lxor0-def-integerp
    (implies (and (integerp x)
                  (integerp y)
                  (> n 0)
                  (integerp n))
             (equal (lxor0 x y n)
                    (+ (* 2 (lxor0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (lxor0 (mod x 2) (mod y 2) 1))))
    :rule-classes ()
    :hints (("Goal" :in-theory (e/d (lxor0 bits-fl-by-2) ())
             :use ((:instance logxor-def (i (bits x (1- n) 0)) (j (bits y (1- n) 0)))
                   (:instance mod012 (m x))
                   (:instance mod012 (m y)))))))

; Now we want to eliminate the (integerp x) and (integerp y) hypotheses from
; lxor0-def-integerp.  First suppose x is not rational.

 (local
  (defthm lxor0-is-0-if-not-rational-1
    (implies (not (rationalp x))
             (equal (lxor0 x y n)
                    (lxor0 0 y n)))
    :hints (("Goal" :expand ((lxor0 x y n)
                             (lxor0 0 y n))))))

 (local
  (defthm lxor0-is-0-if-not-rational-2
    (implies (not (rationalp y))
             (equal (lxor0 x y n)
                    (lxor0 x 0 n)))
    :hints (("Goal" :expand ((lxor0 x y n)
                             (lxor0 0 x n))))))

 (local
  (defthm fl-1/2-is-0-if-not-rational
    (implies (not (rationalp x))
             (equal (fl (* 1/2 x)) 0))
    :hints (("Goal" :cases ((acl2-numberp x))))))

 (local
  (defthm mod-2-if-not-rational
    (implies (not (rationalp x))
             (equal (mod x 2)
                    (fix x)))
    :hints (("Goal" :expand ((mod x 2))))))

 (local
  (defthm lxor0-fl-1
    (equal (lxor0 (fl x) y n)
           (lxor0 x y n))
    :hints (("Goal" :expand ((lxor0 y (fl x) n)
                             (lxor0 x y n))))))

 (local
  (defthm lxor0-fl-2
    (equal (lxor0 y (fl x) n)
           (lxor0 y x n))
    :hints (("Goal" :expand ((lxor0 y (fl x) n)
                             (lxor0 x y n))))))

 (local
  (defthm lxor0-def-rational-hack
    (implies (and (rationalp x)
                  (rationalp y)
                  (>= n 0)
                  (integerp n))
             (equal (lxor0 (* 1/2 (fl x)) (* 1/2 (fl y)) n)
                    (lxor0 (* 1/2 x) (* 1/2 y) n)))
    :hints (("Goal" :expand ((lxor0 (* 1/2 (fl x)) (* 1/2 (fl y)) n)
                             (lxor0 (* 1/2 x) (* 1/2 y) n))))))

 (local
  (defthm lxor0-def-rational
    (implies (and (rationalp x)
                  (rationalp y)
                  (> n 0)
                  (integerp n))
             (equal (lxor0 x y n)
                    (+ (* 2 (lxor0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (lxor0 (mod x 2) (mod y 2) 1))))
    :rule-classes ()
    :hints (("Goal"
             :use ((:instance lxor0-def-integerp (x (fl x)) (y (fl y))))
             :in-theory (e/d (mod-fl-eric) (fl-mod))))))

 (local
  (defthm lxor0-def-not-rational-1
    (implies (and (not (rationalp x))
                  (rationalp y)
                  (> n 0)
                  (integerp n))
             (equal (lxor0 x y n)
                    (+ (* 2 (lxor0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (lxor0 (mod x 2) (mod y 2) 1))))
    :hints (("Goal" :use ((:instance lxor0-def-rational
                                     (x 0)))))
    :rule-classes nil))

 (local
  (defthm lxor0-def-not-rational-2
    (implies (and (rationalp x)
                  (not (rationalp y))
                  (> n 0)
                  (integerp n))
             (equal (lxor0 x y n)
                    (+ (* 2 (lxor0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                       (lxor0 (mod x 2) (mod y 2) 1))))
    :hints (("Goal" :use ((:instance lxor0-def-rational
                                     (y 0)))))
    :rule-classes nil))

 (defthm lxor0-def
   (implies (and (> n 0)
                 (integerp n))
            (equal (lxor0 x y n)
                   (+ (* 2 (lxor0 (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                      (lxor0 (mod x 2) (mod y 2) 1))))
   :rule-classes ()
   :hints (("Goal" :use (lxor0-def-not-rational-1
                         lxor0-def-not-rational-2
                         lxor0-def-rational)))))

(defthm lxor0-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (lxor0 x y n) 2)
		    (lxor0 (mod x 2) (mod y 2) 1)))
  :hints (("Goal" :use (lxor0-def
			(:instance mod012 (m x))
			(:instance mod012 (m y))
			(:instance quot-mod (m (lxor0 x y n)) (n 2))))))

(defthm lxor0-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (lxor0 x y n) 2))
		    (lxor0 (fl (/ x 2)) (fl (/ y 2)) (1- n))))
  :hints (("Goal" :use (lxor0-def
			(:instance mod012 (m x))
			(:instance mod012 (m y))
			(:instance quot-mod (m (lxor0 x y n)) (n 2))))))

(in-theory (disable lxor0-mod-2 lxor0-fl-2))

(defthm bitn-lxor0-0
    (implies (and (integerp x)
                  (integerp y)
		  (not (zp n))
                  )
	     (= (bitn (lxor0 x y n) 0)
		(bitn (+ x y) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-logxor-0 (a (bits x (1- n) 0)) (b (bits y (1- n) 0)))
			(:instance mod-mod-sum (n (expt 2 n)) (a x) (b y))
			(:instance mod-of-mod-cor (a n) (b 1) (x (+ x y)))
			(:instance mod-of-mod-cor (a n) (b 1) (x (+ (mod x (expt 2 n)) (mod y (expt 2 n))))))
		  :in-theory (enable lxor0 bitn-rec-0 bits-mod bitn-bits))))

(defthm lxor0-x-y-0
  (equal (lxor0 x y 0) 0)
  :hints (("Goal" :in-theory (enable lxor0))))


;N is a free variable
(defthm lxor0-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (< n m)
		  (case-split (integerp m))
		  )
	     (equal (lxor0 x y m)
                    (lxor0 x y n)))
  :hints (("Goal" :in-theory (enable lxor0))))


;move
(defthm lxor0-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (lxor0 x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable lxor0))))

;move
(defthm lxor0-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (lxor0 x y n) (1- (expt 2 n)))))

(defthmd lxor0-bits-1
  (equal (lxor0 (bits x (1- n) 0)
               y
               n)
         (lxor0 x y n))
  :hints (("Goal" :in-theory (e/d (lxor0) (logior lxor0-commutative)))))

(defthmd lxor0-bits-2
  (equal (lxor0 x
               (bits y (1- n) 0)
               n)
         (lxor0 x y n))
  :hints (("Goal" :in-theory (e/d (lxor0) (logior lxor0-commutative)))))

(local
 (defthm lxor0-base-lemma
   (implies (and (bvecp x 1) (bvecp y 1))
            (equal (lxor0 x y 1)
                   (if (iff (equal (bitn x 0) 1)
                            (equal (bitn y 0) 1))
                       0
                     1)))
   :rule-classes nil))

(defthm lxor0-base
  (equal (lxor0 x y 1)
         (if (iff (equal (bitn x 0) 1)
                  (equal (bitn y 0) 1))
             0
           1))
  :hints (("Goal" :use ((:instance lxor0-base-lemma
                                   (x (bits x 0 0))
                                   (y (bits y 0 0)))
                        (:instance lxor0-bits-1
                                   (x x)
                                   (y (bits y 0 0))
                                   (n 1))
                        (:instance lxor0-bits-2 (n 1)))))
  :rule-classes nil)
