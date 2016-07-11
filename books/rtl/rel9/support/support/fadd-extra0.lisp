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

; This book, but with land0/lior0/lxor0 replaced by land/lior/lxor, was the
; original state of fadd-extra.lisp.

(in-package "ACL2")

; This book illustrates how to extend the library.

; Typically, one first does the proof after including ../lib/top/.  (For this
; particular file we happened to include ../lib/ books bits, arith, and util.)
; But in order to prove them in this support/ directory, we instead locally
; include a book top1 and put ourselves in a theory, lib-top1.  The resulting
; environment is the same (or at least very close to the same) as the
; environment after including ../lib/top -- or more precisely, a snapshot of
; lib/top at the time top1 was created.  The present book is locally included
; in ../lib/fadd.lisp.

; Some day there might be a need for top2 and theory lib-top2, which will
; include the state of lib/top after the inclusion of the present book
; (fadd-extra.lisp) and any other *-extra.lisp books in this support/
; directory.  But that should be a long time off.

; A reasonable book name in this directory could be
; <lib-book-name>-extra.lisp.

; Be sure to modify the Makefile and top.lisp accordingly.  You can do this by
; searching in those files for fadd-extra and making the analogous mods.

(include-book "rtl")  ; needed for some definitions
(include-book "fadd") ; needed for some definitions

; Now put ourselves in what amounts to the environment of ../lib/top, as
; explained above.
(local (include-book "top1"))
(local (in-theory (theory 'lib-top1)))

; Proof of bits-sum-swallow:

; Proof:  Since y < 2^(k+1), y[i:k+1] = 0.
;
; Since x[k] = 0, x[k:0] = x[k-1:0] < 2^k.
;
; Hence,
;
;   x[k:0] + y[k:0] < 2^k + 2^k = 2^(k+1)
;
; and
;
;   (x[k:0] + y[k:0])[k+1] = 0.
;
; By BITS-SUM-ORIGINAL,
;
;   (x+y)[i:k+1] = (x[i:k+1] + y[i:k+1] + (x[k:0] + y[k:0])[k+1])[i-k-1:0]
;                = (x[i:k+1])[i-k-1:0]
;                = x[i:k+1] {by BITS-BITS}.
;
; By BITS-BITS,
;
;   (x+y)[i:j] = (x+y)[i:k+1][i-k-1:j-k-1]
;              = x[i:k+1][i-k-1:j-k-1]
;              = x[i:j].

(local-defthm bits<expt
  (implies (and (natp x)
                (integerp i)
                (natp j)
                (<= j i)
                (equal n (1+ (- i j))))
           (< (bits x i j)
              (expt 2 n)))
  :hints (("Goal" :use ((:instance bits-bvecp
                                   (k n)))
           :in-theory (e/d (bvecp) (bits-bvecp bits-bvecp-simple))))
  :rule-classes :linear)

(local-defthm bits-sum-swallow-1-1-1-1
  (implies (and (natp x)
                (natp k)
                (= (bitn x k) 0))
           (< (bits x k 0)
              (expt 2 k)))
  :hints (("Goal" :use ((:instance bitn-plus-bits (n k) (m 0))
                        (:theorem (or (zp k) (< 0 k))))))
  :rule-classes :linear)

(local-defthm bits-sum-swallow-1-1-1-2
  (implies (and (natp y)
                (natp k)
                (<= y (expt 2 k)))
           (equal (bits y k 0) y))
  :hints (("Goal" :in-theory (enable bvecp)
           :expand ((expt 2 (1+ k))))))

(local-defthm bits-sum-swallow-1-1-1
  (implies (and (natp x)
                (natp y)
                (natp k)
                (= (bitn x k) 0)
                (<= y (expt 2 k)))
           (< (+ (bits x k 0) (bits y k 0))
              (expt 2 (1+ k))))
  :hints (("Goal" :expand ((expt 2 (1+ k)))))
  :rule-classes nil)

(local-defthm bits-sum-swallow-1-1
  (implies (and (natp x)
                (natp y)
                (natp k)
                (= (bitn x k) 0)
                (<= y (expt 2 k)))
           (equal (bitn (+ (bits x k 0) (bits y k 0))
                        (1+ k))
                  0))
  :hints (("Goal" :in-theory (enable bvecp) ; for bvecp-bitn-0
           :use bits-sum-swallow-1-1-1))
  :rule-classes nil)

(local-defthm bits-sum-swallow-1-2
  (implies (and (natp y)
                (natp k)
                (>= i k)
                (<= y (expt 2 k)))
           (equal (bits y i (1+ k))
                  0))
  :hints (("Goal" :in-theory (enable bvecp-bits-0 bvecp)
           :expand ((expt 2 (1+ k))))))

(local-defthm bits-sum-swallow-1
  (implies (and (natp x)
                (natp y)
                (natp k)
                (>= i k)
                (= (bitn x k) 0)
                (<= y (expt 2 k)))
            (equal (bits (+ x y) i (1+ k))
                   (bits x i (1+ k))))
  :hints (("Goal" :use ((:instance bits-sum-original (j (1+ k)))
                        bits-sum-swallow-1-1))))

(defthmd bits-sum-swallow
  (implies (and (equal (bitn x k) 0)
                (natp x)
                (natp y)
                (integerp i)
                (integerp j)
                (integerp k)
                (>= i j)
                (> j k)
                (>= k 0)
                (<= y (expt 2 k)))
           (equal (bits (+ x y) i j)
                  (bits x i j)))
  :hints (("Goal"
           ;; We deliberately leave bits-bits enabled because we need another
           ;; instance of it too.
           :use ((:instance bits-bits
                            (x (+ x y))
                            (i i)
                            (j (1+ k))
                            (k (1- (- i k)))
                            (l (1- (- j k))))))))

(defthmd bits-sum-of-bits
  (implies (and (integerp x)
                (integerp y)
                (natp i))
           (equal (bits (+ x (bits y i 0)) i 0)
                  (bits (+ x y) i 0)))
  :hints (("Goal" :use ((:instance bits-sum-original
                                   (x x)
                                   (y (bits y i 0))
                                   (i i)
                                   (j 0))
                        (:instance bits-sum-original
                                   (x x)
                                   (y y)
                                   (i i)
                                   (j 0))))))

(defthm bits-sum-3-original
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (bitn (+ (bits x (1- j) 0) (bits y (1- j) 0))
                                 j)
                           (bitn (+ (bits (+ x y) (1- j) 0) (bits z (1- j) 0))
                                 j))
                        (- i j) 0)))
  :hints (("Goal" :use ((:instance bits-sum-original
                                   (x x)
                                   (y y)
                                   (i (1- j))
                                   (j 0))
                        (:instance bits-sum-original
                                   (x x)
                                   (y y)
                                   (i i)
                                   (j j))
                        (:instance bits-sum-original
                                   (x (+ x y))
                                   (y z)
                                   (i i)
                                   (j j))
                        (:instance bits-sum-of-bits
                                   (x (+ (bits z i j)
                                         (bitn (+ (bits z (1- j) 0)
                                                  (bits (+ x y) (1- j) 0))
                                               j)))
                                   (y (+ (bits x i j)
                                         (bits y i j)
                                         (bitn (+ (bits x (1- j) 0)
                                                  (bits y (1- j) 0))
                                               j)))
                                   (i (+ i (* -1 j)))))))
  :rule-classes ())

(local-defthm bits-sum-3-with-gen-normal-case
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp i)
                (integerp j)
                (< 0 j))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use bits-sum-3-original
           :in-theory (enable gen-val-cor1)))
  :rule-classes ())

(local-defthm bits-sum-3-with-gen-numberp-not-integerp-i
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp j)
                (acl2-numberp i)
                (not (integerp i)))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-3-original bits-sum-3-with-gen-normal-case)
           :in-theory (enable bits-with-i-not-an-integer
                              bits-with-j-not-an-integer)))
  :rule-classes ())

(local-defthm bits-sum-3-with-gen-not-numberp-i-positive-j
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp j)
                (> j 0)
                (not (acl2-numberp i)))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-3-original bits-sum-3-with-gen-normal-case)
           :in-theory (enable bits-with-i-not-an-integer
                              bits-with-j-not-an-integer)))
  :rule-classes ())

(local-defthm bits-sum-3-with-gen-not-numberp-i-not-positive-j
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp j)
                (<= j 0)
                (not (acl2-numberp i)))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-3-original bits-sum-3-with-gen-normal-case)
           :in-theory (enable bits-with-i-not-an-integer
                              bits-with-j-not-an-integer)))
  :rule-classes ())

(defthm bits-sum-3
  (implies (and (integerp x) (integerp y) (integerp z))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :hints (("Goal" :use (bits-sum-3-original bits-sum-3-with-gen-normal-case
                                   bits-sum-3-with-gen-numberp-not-integerp-i
                                   bits-sum-3-with-gen-not-numberp-i-positive-j
                                   bits-sum-3-with-gen-not-numberp-i-not-positive-j)
           :in-theory (enable bits-with-j-not-an-integer)))
  :rule-classes ())

; Proof of lior0-slice:

; Note that (2^i - 2^j) = 2^j(2^(i-j)-1) = {2^(i-j)-1,j'b0}

; x[n-1:0] | (2^i - 2^j) =
; {x[n-1:i], x[i-1:j], x[j-1:0]} | {(n-i)'b0, 2^(i-j), j'b0} =
; [by LIOR0-CAT, LIOR0-0, and LIOR0-ONES]
; {{x[n-1:i], 2^(i-j)-1, x[j-1:0]}.

(local-defthm lior0-slice-1
  (implies (and (<= j i)
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j))
           (equal (cat (bits x (1- n) i) (- n i)
                       (bits x (1- i) j) (- i j)
                       (bits x (1- j) 0) j)
                  (bits x (1- n) 0)))
  :hints (("Goal" :use ((:instance cat-bits-bits
                                   (x (bits x (1- i) 0))
                                   (i (1- i))
                                   (j j)
                                   (k (1- j))
                                   (l 0)
                                   (m (- i j))
                                   (n j))
                        (:instance cat-bits-bits
                                   (x x)
                                   (i (1- n))
                                   (j i)
                                   (k (1- i))
                                   (l 0)
                                   (m (- n i))
                                   (n i)))))
  :rule-classes nil)

(local-defthm bvecp-power-of-2-minus-1
  (implies (and (integerp k)
                (equal k k2)
                (< 0 k))
           (bvecp (1- (expt 2 k))
                  k2))
  :hints (("Goal" :in-theory (enable bvecp))))

(local-defthm bvecp-power-of-2-minus-1-alt
  (implies (and (natp k)
                (equal k2 (1+ k)))
           (bvecp (1- (* 2 (expt 2 k)))
                  k2))
  :hints (("Goal" :in-theory (enable bvecp expt))))

(local-defthm lior0-slice-2
  (implies (and (<= j i)
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j))
           (equal (cat 0                     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       0                     j)
                  (- (expt 2 i) (expt 2 j))))
  ;; The following hint is very weird!!  It can't be on Goal or Goal'.  The
  ;; idea came from a proof-builder proof.  I should investigate....
  :hints (("Goal''" :in-theory (enable cat expt)))
  :rule-classes nil)

(local
 (defthmd lior0-slice-3-1
   (implies (and (<= j i)
                 (integerp i)
                 (integerp j)
                 (<= 0 j)
                 (equal k (1- (expt 2 (- i j))))
                 (equal diff (- i j)))
            (equal (lior0 k
                         (bits x (1- i) j)
                         diff)
                   (1- (expt 2 (- i j)))))
   :hints (("Goal" :use ((:instance lior0-ones
                                    (x (bits x (1- i) j))
                                    (n (- i j))))))))

(local-defthm lior0-slice-3
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior0 (cat (bits x (1- n) i) (- n i)
                             (bits x (1- i) j) (- i j)
                             (bits x (1- j) 0) j)
                        (cat 0                     (- n i)
                             (1- (expt 2 (- i j))) (- i j)
                             0                     j)
                        n)
                  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :in-theory (e/d (lior0-cat lior0-slice-3-1)
                                  (cat-bits-bits cat-0))
           :cases ((and (equal j i) (equal j 0) (equal i n))
                   (and (equal j i) (not (equal j 0)) (equal i n))
                   (and (not (equal j i)) (equal j 0) (equal i n))
                   (and (equal j i) (equal j 0) (not (equal i n)))
                   (and (equal j i) (not (equal j 0)) (not (equal i n)))
                   (and (not (equal j i)) (equal j 0) (not (equal i n)))
                   (and (not (equal j i)) (not (equal j 0)) (not (equal i n))))))
  :rule-classes nil)

(local-defthm lior0-slice-almost
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior0 (bits x (1- n) 0)
                        (- (expt 2 i) (expt 2 j))
                        n)
		  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :use (lior0-slice-1 lior0-slice-2 lior0-slice-3)
           :in-theory (theory 'ground-zero)))
  :rule-classes nil)

(defthmd lior0-slice
  (implies (and (<= j i)
		(<= i n)
		(integerp n)
		(integerp i)
		(integerp j)
		(<= 0 j))
	   (equal (lior0 x
                        (- (expt 2 i) (expt 2 j))
                        n)
		  (cat (bits x (1- n) i)     (- n i)
                       (1- (expt 2 (- i j))) (- i j)
                       (bits x (1- j) 0)     j)))
  :hints (("Goal" :use (lior0-slice-almost)
           :in-theory (enable lior0-bits-1))))

(local (in-theory (theory 'lib-top1)))

(local-defthm lxor0-1-not-2
  (equal (equal 2 (lxor0 i j 1))
         nil)
  :hints (("Goal" :expand ((lxor0 i j 1))
           :use ((:instance bvecp-1-rewrite
                            (x (bitn i 0)))
                 (:instance bvecp-1-rewrite
                            (x (bitn j 0)))))))

(local
 (encapsulate
  ()

  (local-defthm bitn-of-1-less-than-power-of-2-lemma-1
    (implies (natp j)
             (equal (bitn (1- (expt 2 (1+ j))) j)
                    1))
    :hints (("Goal" :in-theory (enable bvecp-bitn-1 bvecp)
             :expand ((expt 2 (+ 1 j))))))

  (defthm bitn-of-1-less-than-power-of-2
    (implies (and (integerp i)
                  (natp j)
                  (< j i))
             (equal (bitn (1- (expt 2 i)) j)
                    1))
    :hints (("Goal" :use ((:instance bitn-plus-mult
                                     (x (1- (expt 2 (1+ j))))
                                     (k (1- (expt 2 (- i (1+ j)))))
                                     (m (1+ j))
                                     (n j))))))))

(local-defun prop-as-lxor0-thm (i j x y)
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop x y i j)
                  (log= (lxor0 (bits x i j) (bits y i j) (1+ (- i j)))
                        (1- (expt 2 (1+ (- i j))))))))

(local-defthm prop-as-lxor0-thm-proved-1
  (implies (not (and (natp i) (natp j) (<= j i)))
           (prop-as-lxor0-thm i j x y)))

(local-defthm prop-as-lxor0-thm-proved-3-1
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j)
                (<= j i)
                (equal (bitn x i) (bitn y i))
                (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y))
           (not (equal (bitn (+ -1 (expt 2 (+ 1 i (* -1 j)))) (- i j))
                       (bitn (lxor0 (bits x i j)
                                   (bits y i j)
                                   (+ 1 i (* -1 j)))
                             (- i j)))))
  :rule-classes nil)

(local-defthm prop-as-lxor0-thm-proved-3
  (implies (and (and (natp i) (natp j) (<= j i))
                (= (bitn x i) (bitn y i)))
           (prop-as-lxor0-thm i j x y))
  :hints (("Goal" :use prop-as-lxor0-thm-proved-3-1
           :in-theory (e/d (log=)
                           (bitn-of-1-less-than-power-of-2)))))

(local (in-theory (enable bvecp-0)))

(local-defthm prop-as-lxor0-thm-proved-2
  (implies (and (and (natp i) (natp j) (<= j i))
                (not (= (bitn x i) (bitn y i)))
                (prop-as-lxor0-thm (+ -1 i) j x y))
           (prop-as-lxor0-thm i j x y))
  :hints (("Goal" :in-theory (enable log=)
           :expand ((expt 2 (+ 1 i (* -1 j))))
           :use ((:instance bitn-plus-bits (m 0)
                            (n (- i j))
                            (x (lxor0 (bits x i j)
                                      (bits y i j)
                                      (+ 1 i (* -1 j)))))
                 (:instance bvecp-1-rewrite
                            (x (bitn x i)))
                 (:instance bvecp-1-rewrite
                            (x (bitn y i)))
                 (:instance bvecp-1-rewrite
                            (x (bitn x 0)))
                 (:instance bvecp-1-rewrite
                            (x (bitn y 0)))))))

(local-defthm prop-as-lxor0-thm-proved
  (prop-as-lxor0-thm i j x y)
  :hints (("Goal" :induct (prop x y i j)
           :in-theory (disable prop-as-lxor0-thm)))
  :rule-classes nil)

(defthmd prop-as-lxor0
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (natp x)
                (natp y))
           (equal (prop x y i j)
                  (log= (lxor0 (bits x i j) (bits y i j) (1+ (- i j)))
                        (1- (expt 2 (1+ (- i j)))))))
  :hints (("Goal" :use prop-as-lxor0-thm-proved)))

; Added for rel5: bitn-neg

(local-defthm bitn-neg-1
  (implies (natp x)
           (equal (bitn x -1) 0))
  :hints (("Goal" :use ((:instance bits-times-2 (x x) (i 0) (j 0))
                        (:instance bitn-rec-0 (x (* 2 x))))
           :in-theory (e/d (bitn) (bits-n-n-rewrite)))))

(local-defun bitn-neg-induction (x n)
  (if (zp n)
      (+ x n)
    (bitn-neg-induction (* 2 x) (1- n))))

(defthm bitn-neg-alt
  (implies (and (natp x)
                (integerp k)
                (< 0 k))
           (equal (bitn x (* -1 k)) 0))
  :hints (("Goal" :induct (bitn-neg-induction x k))
          ("Subgoal *1/2.1"
           :use ((:instance bits-times-2 (x x) (i (- 1 k)) (j (- 1 k)))))))
