; Proof that hl-addr-combine is one-to-one
; Copyright (C) 2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
;
; The hl-addr-combine function was derived from Bob Boyer's function, ADDR-FOR,
; which was found in ACL2 3.6.1 as the function ADDR-FOR.  Jared split up this
; function into separate addressing and hashing portions, and hl-addr-combine
; is the hashing portion.  Jared then developed the proof below which shows
; that hl-addr-combine is one-to-one.

(in-package "ACL2")
(local (include-book "arithmetic-5/top" :dir :system))

; hl-addr-combine.lisp
;
; We introduce the HL-ADDR-COMBINE function and prove that it is one-to-one.
; This function is important in the implementation of static honsing; see
; hons-raw.lisp in the ACL2 sources directory.

(local
 (encapsulate
  ()
  ;; Opposite direction of logior-floor-expt-2-n
  (local (defthm logior-floor-expt-2-n-opposite
           (implies (and (integerp x)
                         (integerp y)
                         (integerp n)
                         (<= 0 n))
                    (equal (floor (logior x y) (expt 2 n))
                           (logior (floor x (expt 2 n))
                                   (floor y (expt 2 n)))))))

  ;; Opposite direction of mod-logior-expt-2
  (local (defthm mod-logior-expt-2-n-opposite
           (implies (and (integerp x)
                         (integerp y)
                         (integerp n))
                    (equal (mod (logior x y) (expt 2 n))
                           (logior (mod x (expt 2 n))
                                   (mod y (expt 2 n)))))))

  (local (in-theory (disable logior-floor-expt-2-n
                             mod-logior-expt-2-n)))



  (defthm |(logior a (* b (expt 2 n)))|
    (implies (and (natp a)
                  (integerp b)
                  (natp n)
                  (< a (expt 2 n)))
             (equal (logior a (* b (expt 2 n)))
                    (+ a (* b (expt 2 n)))))
    :hints(("Goal"
            :in-theory (disable floor-mod-elim)
            :use ((:instance floor-mod-elim
                             (x (logior a (* b (expt 2 n))))
                             (y (expt 2 n)))))))

  (defthm |(logior a (* (expt 2 n) b))|
    (implies (and (natp a)
                  (integerp b)
                  (natp n)
                  (< a (expt 2 n)))
             (equal (logior a (* (expt 2 n) b))
                    (+ a (* (expt 2 n) b)))))))


(local
 (encapsulate
  ()
  (local (defthm lemma1
           (implies (and (< a (expt 2 n))
                         (< b (expt 2 n))
                         (natp a)
                         (natp b)
                         (natp n))
                    (equal (mod (+ b (* (expt 2 n) a))
                                (expt 2 n))
                           (mod b (expt 2 n))))))

  (local (defthm lemma2
           (implies (and (< a (expt 2 n))
                         (< b (expt 2 n))
                         (natp a)
                         (natp b)
                         (natp n))
                    (equal (floor (+ b (* (expt 2 n) a))
                                  (expt 2 n))
                           a))))

  (local (defthm equal-by-floor-and-mod
           (implies (and (natp a)
                         (natp b)
                         (natp n))
                    (equal (equal a b)
                           (and (equal (floor a n) (floor b n))
                                (equal (mod a n) (mod b n)))))
           :rule-classes nil))

  (defthm |a*2^n + b == c*2^n + d when <= 2^n|
    (implies (and (< a (expt 2 n))
                  (< b (expt 2 n))
                  (< c (expt 2 n))
                  (< d (expt 2 n))
                  (natp a)
                  (natp b)
                  (natp c)
                  (natp d)
                  (natp n))
             (equal (equal (+ b (* (expt 2 n) a))
                           (+ d (* (expt 2 n) c)))
                    (and (equal a c)
                         (equal b d))))
    :hints(("Goal"
            :use ((:instance equal-by-floor-and-mod
                             (a (+ b (* (expt 2 n) a)))
                             (b (+ d (* (expt 2 n) c)))
                             (n (expt 2 n)))))))))



(defund hl-nat-combine (a b)

; (hl-nat-combine a b) computes (a+b+1)(a+b)/2 + b, an important one-to-one
; mapping for the static hons hashing scheme.
;
; The important properties of this function are that it is one-to-one and that
; it monotonically increases as either argument is increased.

  (declare (xargs :guard (and (natp a)
                              (natp b))))
  (mbe :logic
       (+ (/ (* (+ a b 1)
                (+ a b))
             2)
          b)
       :exec
       ;; We strength-reduces the division into a shift.  Also, doing the
       ;; division before the multiplication may allow this to be done using
       ;; only fixnums for a bit longer.
       (+ (let* ((a+b   (+ a b))
                 (a+b+1 (+ 1 a+b)))
            (if (= (logand a+b 1) 0)
                (* (ash a+b -1) a+b+1)
              (* a+b (ash a+b+1 -1))))
          b)))

(encapsulate
  ()

; Proof that hl-nat-combine is one-to-one.  Suppose hl-nat-combine(a,b) =
; hl-nat-combine(c,d).  Recall that n(n+1)/2 = 1 + 2 + ... + n, so we know:
;
;    1 + ... + (a+b) + b = 1 + ... + (c+d) + d.
;
; Case 1. Suppose a+b = c+d.  Now the leading terms all cancel and we may
; conclude b = d.  Then, since we just assumed a+b = c+d, substituting b = d
; into both sides yields a = c.
;
; Case 2. WLOG suppose a+b < c+d.  Let M = (a+b+1) + ... + (c+d).  Clearly M >
; 0.  The right-hand side is then equivalent to: 1 + ... + (a+b) + M + d.
; Cancelling terms on the left and right sides, we find b = M + d.  But since
; a+b < c+d, clearly b < c+d, so b < M, so b < M + d.  Hence, b cannot be d,
; and this case cannot occur.  QED.

  (local (in-theory (enable hl-nat-combine)))

  (local (defun sum-up-to (n) ; 1 + 2 + ... + n
           (declare (xargs :guard (natp n)))
           (if (zp n)
               0
             (+ n (sum-up-to (1- n))))))

  (local (defthm sum-up-to-identity
           (implies (natp n)
                    (equal (/ (* n (+ 1 n)) 2)
                           (sum-up-to n)))))

  (local (defthm hl-nat-combine-redefinition
           (implies (and (natp a)
                         (natp b))
                    (equal (hl-nat-combine a b)
                           (+ (sum-up-to (+ a b)) b)))
           :hints(("Goal" :use ((:instance sum-up-to-identity (n (+ a b))))))))

  (defthm natp-of-hl-nat-combine
    (implies (and (natp a)
                  (natp b))
             (natp (hl-nat-combine a b))))

  (local (defun sum-interval (a b) ; a+1 + ... + b.
           (declare (xargs :guard (and (natp a)
                                       (natp b))
                           :measure (nfix (- (nfix b) (nfix a)))))
           (let ((a (nfix a))
                 (b (nfix b)))
             (if (<= b a)
                 0
               (+ b (sum-interval a (- b 1)))))))

  (local (defthmd decompose-sum-up-to
           (implies (and (natp a)
                         (natp b)
                         (< a b))
                    (equal (sum-up-to b)
                           (+ (sum-up-to a) (sum-interval a b))))))

  (local (defthm decompose-rhs
           (implies (and (natp a)
                         (natp b)
                         (natp c)
                         (natp d)
                         (< (+ a b) (+ c d)))
                    (equal (hl-nat-combine c d)
                           (+ (sum-up-to (+ a b))
                              (sum-interval (+ a b) (+ c d)) ; a+b+1 + ... + c+d
                              d)))
           :hints(("Goal" :use ((:instance decompose-sum-up-to
                                           (b (+ c d))
                                           (a (+ a b))))))))

  (local (defthm sum-interval-lower-bound
           (implies (and (natp a)
                         (natp b)
                         (< a b))
                    (< a (sum-interval a b)))
           :rule-classes :linear))

  (defthm hl-nat-combine-is-one-to-one
    (implies (and (natp a)
                  (natp b)
                  (natp c)
                  (natp d))
             (equal (equal (hl-nat-combine a b)
                           (hl-nat-combine c d))
                    (and (equal a c)
                         (equal b d))))
    :hints(("Goal"
            :cases ((equal (+ a b) (+ c d))
                    (< (+ a b) (+ c d))
                    (< (+ c d) (+ a b))))))

  (defthm hl-nat-combine-monotonic-a
    (implies (and (natp a)
                  (natp a2)
                  (natp b)
                  (< a a2))
             (< (hl-nat-combine a b)
                (hl-nat-combine a2 b)))
    :rule-classes :linear)

  (defthm hl-nat-combine-monotonic-b
    (implies (and (natp a)
                  (natp b)
                  (natp b2)
                  (< b b2))
             (< (hl-nat-combine a b)
                (hl-nat-combine a b2)))
    :rule-classes :linear))






(local (defthm guard-lemma
         (implies (and (< b 1073741824)
                       (natp b)
                       (integerp a))
                  (equal (logior b (* 1073741824 a))
                         (+ b (* 1073741824 a))))
         :hints(("Goal"
                 :in-theory (disable |(logior a (* (expt 2 n) b))|)
                 :use ((:instance |(logior a (* (expt 2 n) b))|
                                  (n 30)
                                  (a b)
                                  (b a)))))))


(defund hl-addr-combine (a b)

; (hl-addr-combine a b) is a one-to-one mapping from N^2 to Z
;
; Given two natural numbers, hl-addr-combine merges them to produce a single
; integer that can be used as a hash key.
;
; The crucial correctness property for hl-addr-combine is that it must be a
; one-to-one function.  We prove this as hl-addr-combine-is-one-to-one, just
; below.
;
; In static honsing, the purpose of this function is roughly as follows.
; Suppose we have a cons, X = (foo . bar), where a and b are the addresses of
; foo and bar, respectively.  Then, (hl-addr-combine a b) will be the index for
; X in the ADDR-HT.
;
; This function might produce a fixnum or a bignum as its output.  We want to
; produce a fixnum "whenever possible," so we may (and in fact often do)
; produce negative results.  The basic idea is to use the whole available
; fixnum range, instead of just the positive range.  In practice, this means we
; subtract a big number so that our hash results "start" from the "most
; negative" fixnums and count upwards.  Of course, even with this, we will need
; to produce bignums for some arguments.
;
; Change #1 from the ADDR-FOR hashing scheme.  We now use the small case even
; when a == 2^30-1 or b == 2^30-1.  This "fixes" a corner case that wasn't
; really a problem.  Specifically, previously, if a = 2^30-1 and b=0, then the
; large case was triggered, but produced a negative result!  This was not
; exactly a problem, because the resulting bit pattern could never be generated
; by the small case.  However, it was still ugly, and it seemed easier to fix
; than to argue in a separate, special case.
;
; Change #2.  We now just negate the answer in the small case, rather than
; subtracting 2^60.  This might be negligibly faster.
;
; Change #3.  We subtract (2^59 + 2^29 - 1) from the large case result, rather
; than 2^59.  This should result in slightly more of the available fixnum space
; being used.

  (declare (xargs :guard (and (natp a)
                              (natp b))))
  (mbe :logic
       (if (and (< a (expt 2 30))
                (< b (expt 2 30)))
           ;; Small Case.  Result is usually negative (but might be 0)
           (- (+ (* a (expt 2 30)) b))
         ;; Large Case.  Result is always greater than 0.
         (- (hl-nat-combine a b)
            (+ (expt 2 59) (expt 2 29) -1)))
       :exec
       (if (and (< a 1073741824)
                (< b 1073741824))
           ;; Optimized version of the small case
           (the (signed-byte 61)
             (- (the (signed-byte 61)
                  (logior (the (signed-byte 61)
                            (ash (the (signed-byte 31) a) 30))
                          (the (signed-byte 31) b)))))
         ;; Large case.
         (- (hl-nat-combine a b)
            576460752840294399))))


(encapsulate
 ()

; The proof that hl-addr-combine is one-to-one is done in three parts.
; First, we show that the small case is selfwise one-to-one, then that the
; large case is selfwise one-to-one, then finally that the two cases do not
; intersect (because the small case produces negative results and the large
; case produces positive results).

 (local (in-theory (enable hl-addr-combine)))

 (local (defthm small-case-non-positive
          (implies (and (< a (expt 2 30))
                        (< b (expt 2 30))
                        (natp a)
                        (natp b))
                   (<= (hl-addr-combine a b) 0))))

 (local
  (encapsulate
   ()
   (local (defthmd monotonicity-corollary-1
            ;; Lower bound for (hl-nat-combine (expt 2 30) 0)
            (implies (and (natp a)
                          (natp b)
                          (<= (expt 2 30) a))
                     (<= 576460752840294400 (hl-nat-combine a b)))
            :hints(("Goal"
                    :in-theory (disable hl-nat-combine-monotonic-a
                                        hl-nat-combine-monotonic-b)
                    :use ((:instance hl-nat-combine-monotonic-b
                                     (a a)
                                     (b 0)
                                     (b2 b))
                          (:instance hl-nat-combine-monotonic-a
                                     (a (expt 2 30))
                                     (a2 a)
                                     (b 0)))))))

   (local (defthmd monotonicity-corollary-2
            ;; Lower bound for (hl-nat-combine 0 (expt 2 30)).
            (implies (and (natp a)
                          (natp b)
                          (<= (expt 2 30) b))
                     (<= 576460753914036224 (hl-nat-combine a b)))
            :hints(("Goal"
                    :in-theory (disable hl-nat-combine-monotonic-a
                                        hl-nat-combine-monotonic-b)
                    :use ((:instance hl-nat-combine-monotonic-b
                                     (a 0)
                                     (b (expt 2 30))
                                     (b2 b))
                          (:instance hl-nat-combine-monotonic-a
                                     (a 0)
                                     (a2 a)
                                     (b b)))))))

   (defthm large-case-positive
     (implies (and (or (not (< a (expt 2 30)))
                       (not (< b (expt 2 30))))
                   (natp a)
                   (natp b))
              (< 0 (hl-addr-combine a b)))
     :hints(("Goal"
             :use ((:instance monotonicity-corollary-1)
                   (:instance monotonicity-corollary-2)))))))

 (local (defthm small-case-one-to-one
          (implies (and (< a (expt 2 30))
                        (< b (expt 2 30))
                        (< c (expt 2 30))
                        (< d (expt 2 30))
                        (natp a)
                        (natp b)
                        (natp c)
                        (natp d))
                   (equal (equal (hl-addr-combine a b)
                                 (hl-addr-combine c d))
                          (and (equal a c)
                               (equal b d))))
          :hints(("Goal" :in-theory (disable (expt))))))

 (local (defthm large-case-one-to-one
          (implies (and (or (<= (expt 2 30) a)
                            (<= (expt 2 30) b))
                        (or (<= (expt 2 30) c)
                            (<= (expt 2 30) d))
                        (natp a)
                        (natp b)
                        (natp c)
                        (natp d))
                   (equal (equal (hl-addr-combine a b)
                                 (hl-addr-combine c d))
                          (and (equal a c)
                               (equal b d))))))

 (local (in-theory (disable hl-addr-combine)))

 (defthm hl-addr-combine-is-one-to-one
   (implies (and (natp a)
                 (natp b)
                 (natp c)
                 (natp d))
            (equal (equal (hl-addr-combine a b)
                          (hl-addr-combine c d))
                   (and (equal a c)
                        (equal b d))))
   :hints(("Goal"
           :cases ( ;; both small case
                   (and (< a (expt 2 30))
                        (< b (expt 2 30))
                        (< c (expt 2 30))
                        (< d (expt 2 30)))
                   ;; both large case
                   (and (or (<= (expt 2 30) a)
                            (<= (expt 2 30) b))
                        (or (<= (expt 2 30) c)
                            (<= (expt 2 30) d)))))
          ("Subgoal 3" ;; One large, one small
           :in-theory (disable small-case-non-positive
                               large-case-positive)
           :use ((:instance small-case-non-positive (a a) (b b))
                 (:instance small-case-non-positive (a c) (b d))
                 (:instance large-case-positive (a a) (b b))
                 (:instance large-case-positive (a c) (b d)))))))


