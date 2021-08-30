; More rules about floor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;TODO: add this stuff to the main floor book? but actually, a lot of this stuff is about mod

(include-book "floor")
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "times"))
(local (include-book "minus"))
(local (include-book "times-and-divides"))
(local (include-book "plus"))
(local (include-book "plus-and-minus"))
(local (include-book "mod"))
(local (include-book "numerator"))
(local (include-book "mod2"))

;; ;dup
;; (DEFTHM MOVE-NEGATIVE-ADDEND-1
;;   (EQUAL (< (+ X (- Y)) Z)
;;          (< X (+ Y Z))))

;; (defthm <-of-0-and-+-of---arg2
;;   (equal (< 0 (+ x (- y)))
;;          (< y x)))

;; (defthm <-of-0-and-+-of---arg1
;;   (equal (< 0 (+ (- y) x))
;;          (< y x)))



(in-theory (disable floor-peel-off-constant))

;when all we care about is divisibility, we can flip the sign of the divisor to mod?

(defthm divisible-when-divisible-by-multiple
  (implies (and (equal (mod i free) 0) ;what does this idiom mean when the values are not integers?
                (equal (mod free j) 0)
                (not (equal 0 free))
                ;; (rationalp j)
                (rationalp free)
                (rationalp i))
           (equal (mod i j)
                  0))
  :hints (("Goal" :use (:instance integerp-of-* (x (* (/ free) i)) (y (* free (/ j))))
           :cases ((rationalp j))
           :in-theory (e/d (equal-of-0-and-mod) (integerp-of-*)))))

;in what cases do we prefer / to floor?
;i think / is simpler than floor
(defthm floor-when-divisible-cheap
  (implies (and (equal 0 (mod i j))
                (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (floor i j)
                  (/ i j)))
  :hints (("Goal" :in-theory (enable floor equal-of-0-and-mod)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil))))

(defthm floor-when-divisible
  (implies (and (equal 0 (mod i j))
                (rationalp i)
                (rationalp j)
                (not (equal 0 j)))
           (equal (floor i j)
                  (/ i j)))
  :hints (("Goal" :use (:instance floor-when-divisible-cheap)
           :in-theory (disable floor-when-divisible-cheap))))

;move?
(defthm mod-is-0-when-multiple
  (implies (and (integerp (/ x y)) ;can be expensive?
                ;; (rationalp x)
                (acl2-numberp y)
                (not (equal 0 y)) ;move to conclusion?
                )
           (equal (mod x y)
                  0)))

;make sure this doesn't loop
;fixme gen
(defthm multiple-idioms-for-multiple
  (implies (and (equal 0 (mod i 64))
                (rationalp i))
           (integerp (* 1/64 i))))

(defthm multiple-idioms-for-multiple-4
  (implies (and (equal 0 (mod i 4))
                (rationalp i))
           (integerp (binary-* '1/4 i))))

(defthm mod-less-than-1
  (implies (and (integerp i)
                (integerp j)
                (< 0 j))
           (equal (< (mod i j) 1)
                  (equal (mod i j) 0)))
  :hints (("Goal" :in-theory (disable)
           :cases ((equal (MOD I J) 0)))))

;move
(defthm floor-of-divide-hack
  (implies (rationalp n)
           (equal (floor (* 1/4 n) 16)
                  (floor n 64)))
  :hints (("Goal" :in-theory (e/d (FLOOR-NORMALIZE-DENOMINATOR)
                                  (FLOOR-OF-*-OF-/-AND-1))))
;  :hints (("Goal" :use (:instance floor-floor-integer (i 4) (j 16) (x n))))
  )

;; (INTEGERP (* 1/16 (FLOOR N 4)))

(defthm floor-bound-lemma2
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j)
                )
           (< i (+ j (* j (floor i j)))))
  :hints (("Goal" :use (:instance my-floor-upper-bound))))

(defthm floor-bound-lemma3
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j ))
           (not (< i (* j (floor i j)))))
  :hints (("Goal" :use (:instance my-floor-upper-bound))))

;for stuff like this (where we can prove it for a constant but not in general), try to figure out which literals are needed by analyzing what happens with the constant.  here, it's all 3 of the big ones

(local
 (defthmd helper-lemmm
   (IMPLIES (AND (POSP N)
                 (POSP J)
                 (NOT (EQUAL (+ (FLOOR N J)
                                (- (* m (FLOOR N (* J m)))))
                             K))
                 (NATP K) ;(equal j 100)
                 (posp m)
                 (< K m)
                 (<= (+ (* J K) (* J m (FLOOR N (* J m))))
                     N))
            (<= (+ J (* J K)
                   (* J m (FLOOR N (* J m))))
                N))
   :hints (("Goal" :in-theory (disable FLOOR-BOUND-LEMMA2 FLOOR-BOUND-LEMMA3 FLOOR-UNIQUE-EQUAL-VERSION)
            :use ((:instance floor-unique (i n) (j j) (n (+ k (* m (FLOOR N (* m J))))))
;(:instance floor-bounded-by-/ (x n) (y (* 16 j)))
;(:instance floor-bounded-by-/ (x n) (y j))
                  )))))

(in-theory (disable floor-when-divisible))

;rephrase
;use distance from true quotient

(defthmd floor-in-terms-of-mod
  (implies (and (rationalp i)
                (rationalp j)
                (not (equal 0 j))
                )
           (equal (floor i j)
                  (- (/ i j) (/ (mod i j) j))))
  :hints (("Goal" ;:use (:instance floor-unique (n (- (* I (/ J)) (/ (MOD I J) J))))
           :in-theory (e/d (mod
                            ) (floor-unique ;MOD-=-0 ;MOD-RECOLLAPSE-LEMMA2 MOD-RECOLLAPSE-LEMMA
                               )))))

;gen
;move
(defthm floor-of-*-bound-arg2
  (IMPLIES (AND (INTEGERP I)
                (< 0 I)
                (INTEGERP J1)
                (< 0 J1)
                (INTEGERP J2)
                (< 0 J2))
           (<= (* J2 (FLOOR I (* J1 J2)))
               (FLOOR I J1)))
  :hints (("Goal" :use (:instance my-floor-upper-bound
                                  (j (* j1 j2))
                                  )
           :in-theory (disable my-floor-upper-bound))))

(defthm <=-of-mod-and-mod-of-*-same
  (IMPLIES (AND (INTEGERP I)
                (< 0 I)
                (INTEGERP J1)
                (< 0 J1)
                (INTEGERP J2)
                (< 0 J2))
           (<= (MOD I J1) (MOD I (* J1 J2))))
  :hints (("Goal" :in-theory (enable mod))))


(defthm floor-bound-hack
  (implies (and (posp i)
                (posp j1)
                (posp j2))
           (not (< (floor i j1)
                   (* j2 (floor i (* j1 j2))))))
  :hints (("Goal"
;          :cases ((< (* j2 (FLOOR i (* j1 j2))) (+ 1 (FLOOR i j1))))
           :use ((:instance my-floor-upper-bound (j (* j1 j2)))
                 (:instance my-floor-upper-bound (j j1))
                 )
           :in-theory (e/d (floor-in-terms-of-mod)
                           (floor-bound-lemma2
                            floor-bound-lemma3
                            ;;MOD-X-I*J
                            ;; MOD-RECOLLAPSE-LEMMA2 MOD-RECOLLAPSE-LEMMA
                            FLOOR-MINUS-ERIC-BETTER ;bozo looped!
                            mod-sum-cases ;for speed
                            )))))

(defthm floor-bound-hack2
  (implies (and (posp i)
                (posp j1)
                (posp j2))
           (equal (< (floor i j1)
                     (+ j2 (* j2 (floor i (* j1 j2)))))
                  t))
  :hints (("Goal"
;          :cases ((< (* j2 (FLOOR i (* j1 j2))) (+ 1 (FLOOR i j1))))
           :use (;(:instance floor-bounded-by-/ (x i) (y (* j1 j2)))
                 (:instance my-floor-upper-bound (i i) (j j1))
                 (:instance my-floor-lower-bound (i i) (j (* j1 j2)))
                 ;(:instance *-PRESERVES->-FOR-NONNEGATIVES-1 (x2 (* I (/ J1) (/ J2))) (y1 j2) (x1 (+ 1 (FLOOR I (* J1 J2)))) (y2 j2))
                 )
           :in-theory (e/d (;floor-in-terms-of-mod
                            ;mod
                            )
                           ( ;floor-bounded-by-/
                            floor-bound-lemma2 floor-bound-lemma3
                                          ;<-*-/-LEFT
                                          ;<-*-/-RIGHT
                                          ;<-*-/-RIGHT-commuted
                                          ;NORMALIZE-<-MINUS-/
;                                          MOD-X-I*J
;                                          MOD-RECOLLAPSE-LEMMA2 MOD-RECOLLAPSE-LEMMA
                                          FLOOR-MINUS-ERIC-BETTER ;bozo looped!
                                          )))))

(encapsulate
 ()
 (local (include-book "ihs/ihs-lemmas" :dir :system)) ;todo
 (local (in-theory (disable /R-WHEN-ABS-NUMERATOR=1)))
 (defthm mod-of-floor-equal-rewrite
   (implies (and (posp n)
                 (posp j)
;               (equal j 100)
;               (equal m 17)
                 (posp m)
                 )
            (equal (equal (mod (floor n j) m) k)
                   (and (natp k)
                        (< k m)
                        (<= (* k j) (mod n (* m j)))
                        (< (mod n (* m j)) (* j (+ 1 k))))))
   :hints (("Goal" :use (:instance helper-lemmm (m m ;17
                                                   ))
            :in-theory (e/d ( ;mod
                             natp)
                            ( ;MOD-=-0 ;MOD-RECOLLAPSE-LEMMA MOD-RECOLLAPSE-LEMMA2
;FLOOR-=-X/Y
                             FLOOR-WHEN-DIVISIBLE))))))

;bozo gen the 1/4
(defthm quotient-is-multiple
  (implies (and (posp i)
                (posp k))
           (equal (equal (mod (* 1/4 i) k) 0)
                  (equal (mod i (* 4 k)) 0)))
  :hints (("Goal" :use (:instance integerp-of-* (x (* 1/4 (/ K) i)) (y k))
           :in-theory (e/d (;mod-=-0
                            EQUAL-OF-0-AND-MOD
                            ) (integerp-of-*)))))

;FIXME gen
(defthm floor-of-plus-of-floor-15-3-4-16
  (implies (posp n)
           (equal (floor (+ 15 (floor (+ 3 n) 4)) 16)
                  (floor (+ 63 n) 64)))
  :hints (("Goal" :in-theory (e/d (floor-of-sum
                                   mod-sum-cases)
                                  (floor-when-divisible
                                   ;mod-bounded-by-modulus
                                   ;floor-bounded-by-/
                                   ;floor-=-x/y
                                   ;mod-=-0
                                   )))))


;; (thm
;;  (implies (posp n)
;;           (equal (equal (mod (floor n 4) 16) 0)  ;;says that n mod 64 is in [0,3]??
;;                  (< (mod n 64) 4)))
;;  :hints (("Goal" :in-theory (e/d (mod)( MOD-=-0 MOD-RECOLLAPSE-LEMMA MOD-RECOLLAPSE-LEMMA2
;;                                                 FLOOR-=-X/Y
;;                                                 FLOOR-WHEN-DIVISIBLE)))))

;; ;from arithmetic/mod-gcd.lisp
;; (defun nonneg-int-mod ( n d )
;;   (declare (xargs :guard (and (integerp n)
;; 			      (>= n 0)
;; 			      (integerp d)
;; 			      (< 0 d))))
;;   (if (zp d)
;;       (nfix n)
;;       (if (< (nfix n) d)
;; 	  (nfix n)
;; 	(nonneg-int-mod (- n d) d))))

;; (defun nonneg-int-gcd ( x y )
;;   (declare (xargs :guard (and (integerp x)
;; 			      (>= x 0)
;; 			      (integerp y)
;; 			      (>= y 0))))
;;   (if (zp y)
;;       (nfix x)
;;     (nonneg-int-gcd y (nonneg-int-mod x y))))

(defthm cancel-from-<-of-+
  (equal (< (+ x y) (+ x z))
         (< y z)))

(defthm cancel-from-<-of-+-another
  (equal (< (+ x y) (+ z x))
         (< y z)))

(defun non-neg-gcd (a b)
  (declare (xargs :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (or (zp b)
          (not (natp a)))
      a
    (non-neg-gcd b (mod a b))))

;FIXME what about non integer factors?
(defun get-common-positive-integer-factor (term)
  (if (variablep term)
      1 ;could return a nil status to indicate failure
    (if (fquotep term)
        (if (integerp (unquote term))
            (abs (unquote term))
          1)
      (if (equal 'binary-* (ffn-symb term))
          (* (get-common-positive-integer-factor (second term))
             (get-common-positive-integer-factor (third term)) ;could skip this if constants are collected?
             )
        (if (equal 'binary-+ (ffn-symb term))
            (non-neg-gcd ;nonneg-int-gcd
             (get-common-positive-integer-factor (second term))
                 (get-common-positive-integer-factor (third term)))
          (if (equal 'unary-- (ffn-symb term))
              (get-common-positive-integer-factor (second term))
            1 ;FIXME handle more operators?
            ))))))

(defun get-common-positive-integer-factor-of-terms (term1 term2)
  (non-neg-gcd ;nonneg-int-gcd
   (get-common-positive-integer-factor term1)
                  (get-common-positive-integer-factor term2)))

(defun bind-common-positive-integer-factor-of-terms (term1 term2)
  (let ((factor (get-common-positive-integer-factor-of-terms term1 term2)))
    (if (> factor 1)
        (acons 'factor (list 'quote factor) nil)
      nil)))

;floor by 0?

;turns (floor (+ 64 (* 8 n)) 512) into  (FLOOR (+ 8 N) 64)
(defthm floor-divide-by-common-constant-factor
  (implies (and (bind-free (bind-common-positive-integer-factor-of-terms i j) (factor))
                (rationalp i)
                (rationalp factor)
                (not (equal 0 factor))
                (rationalp j)
                (not (equal 0 j))
                )
           (equal (floor i j)
                  (floor (/ i factor) (/ j factor)))))

(defthm <-of-floor-and-1
  (implies (and (< 0 y)
                (<= 0 x)
                (rationalp x)
                (rationalp y)
                )
           (equal (< (FLOOR x y) 1)
                  (< x y))))

(defthm floor-when-<=
  (implies (and (<= x y) ;expensive?
                (< 0 y)
                (<= 0 x)
                (rationalp x)
                (rationalp y))
           (equal (floor x y)
                  (if (equal x y)
                      1
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil nil nil)))
  )

;yuck?
(defthm floor-must-be-1
  (implies (and (< x (* 2 N))
                (<= N x)
                (rationalp x)
                (rationalp N))
           (equal (floor x n)
                  1))
  :hints (("Goal" :use (:instance FLOOR-UNIQUE (i x) (j n) (n 1)))))

(defthm mod-of-floor-is-0-when-multiple
  (implies (and (equal (mod n (* i j)) 0)
                (posp i)
                (posp j)
                (posp n))
           (equal (mod (floor n i) j)
                  0))
  :hints (("Goal" :in-theory (enable equal-of-0-and-mod))))
