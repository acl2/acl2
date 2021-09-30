; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "fnc-defs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (fetch-new-theory
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5))

(defthm ifix-opener
  (implies (integerp x)
           (equal (ifix x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (ifix) ()))))

(defthm integerp-m2-f2-d2
  (and (integerp (m2 x))
       (integerp (d2 x))
       (integerp (f2 x))
       (integerp (sum x y))
       (integerp (sum-list x)))
  :hints (("Goal"
           :in-theory (e/d (m2  f2 sum-list sum) ()))))

(defthm integerp-ifix
  (integerp (ifix x)))

(defthm m2-f2-d2-sum-of-ifix
  (and (equal (f2 (ifix x))
              (f2 x))
       (equal (d2 (ifix x))
              (d2 x))
       (equal (m2 (ifix x))
              (m2 x))
       (equal (sum (ifix x) b)
              (sum x b))
       (equal (sum b (ifix x))
              (sum x b)))
  :hints (("Goal"
           :in-theory (e/d (m2 f2 d2 sum)
                           (
                            (:REWRITE ACL2::|(equal (if a b c) x)|)
                            (:REWRITE ACL2::|(floor x 2)| . 1))))))

(defthm consp-of-rp-trans-lst
  (equal (CONSP (RP-TRANS-LST lst))
         (consp lst))
  :hints (("Goal"
           :induct (len lst)
           :do-not-induct t
           :in-theory (e/d () ()))))

(progn

  (defun sum-comm-order-aux (x cnt)
    (case-match x
      (('m2 &)
       (mv 'm2 x))
      (('f2 &)
       (mv 'f2 x))
      (('d2 &)
       (mv 'd2 x))
      (('-- x)
       (sum-comm-order-aux x (1+ cnt)))
      (('times2 x)
       (sum-comm-order-aux x (1+ cnt)))
      (('sum-list x)
       (sum-comm-order-aux x (1+ cnt)))
      (('sum-list-eval x &)
       (sum-comm-order-aux x (1+ cnt)))
      (('rp-evl x &)
       (sum-comm-order-aux x (1+ cnt)))
      (('rp-trans x)
       (sum-comm-order-aux x (1+ cnt)))
      (('mv-nth & &)
       (mv 'mv-nth (list (caddr x) (cadr x))))
      (('pp-sum-merge & &)
       (mv 'merge x))
      (('s-sum-merge & &)
       (mv 'merge x))
      (('car x)
       (sum-comm-order-aux x (1+ cnt)))
      (('cdr x)
       (sum-comm-order-aux x (1+ cnt)))
      (('binary-sum & &)
       (mv 'binary-sum x))
      (('binary-m2-chain & &)
       (mv 'binary-m2-chain x))
      (('ex-from-rp/-- &)
       (mv 'm2 x))
      (&
       (mv cnt x))))

  (defun sum-comm-order (a b)
    (b* (((mv a-type a)
          (sum-comm-order-aux a 0))
         ((mv b-type b)
          (sum-comm-order-aux b 0)))
      (cond
       ((or (equal a-type 'binary-sum)
            (equal a-type 'binary-m2-chain)
            (equal b-type 'binary-sum)
            (equal b-type 'binary-m2-chain))
        nil)
       ((or (and (equal a-type 'm2)
                 (equal b-type 'm2))
            (and (equal a-type 'mv-nth)
                 (equal b-type 'mv-nth))
            (and (equal a-type 'merge)
                 (equal b-type 'merge)))
        (b* (((mv res &) (lexorder2 a b)))
          res))
       ((or (equal a-type 'm2)
            (equal b-type 'm2))
        (not (equal b-type 'm2)))
       ((or (equal a-type 'mv-nth)
            (equal b-type 'mv-nth))
        (not (equal b-type 'mv-nth)))
       ((or (equal a-type 'merge)
            (equal b-type 'merge))
        (not (equal b-type 'merge)))
       ((or (and (equal a-type 'd2)
                 (equal b-type 'd2))
            (and (equal a-type 'f2)
                 (equal b-type 'f2)))
        (b* (((mv res &) (lexorder2 a b)))
          res))
       ((or (equal a-type 'd2)
            (equal b-type 'd2))
        (not (equal a-type 'd2)))
       ((or (equal a-type 'f2)
            (equal b-type 'f2))
        (not (equal a-type 'f2)))
       ((and (integerp a-type)
             (integerp b-type))
        (b* (((mv res equals) (lexorder2 a b)))
          (if equals
              (> a-type b-type)
            res)))
       ((or (integerp a-type)
            (integerp b-type))
        (not (integerp a-type)))
       (t (b* (((mv res &) (lexorder2 a b)))
            res)))))

  (defthm sum-comm-1
    (implies (syntaxp (sum-comm-order a b))
             (equal  (sum b a)
                     (sum a b)))
    :rule-classes ((:rewrite :loop-stopper nil))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))
  (defthmd sum-comm-1-loop-stopper
    (implies t
             (equal  (sum b a)
                     (sum a b)))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-comm-2
    (implies (syntaxp (sum-comm-order a b))
             (equal  (sum b a c)
                     (sum a b c)))
    :rule-classes ((:rewrite :loop-stopper nil))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthmd sum-comm-2-loop-stopper
    (implies t
             (equal  (sum b a c)
                     (sum a b c)))
    
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-assoc
    (equal (sum (sum a b) c)
           (sum a b c))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-of-0
    (and (equal (sum 0 a)
                (ifix a))
         (equal (sum a 0)
                (ifix a)))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-of-ifix
    (and (equal (sum (ifix x) y)
                (sum x y))
         (equal (sum x (ifix y))
                (sum x y)))
    :hints (("Goal"
             :in-theory (e/d (ifix sum) ()))))

  )

(in-theory (disable ifix))

(defthm sum-list-of-append
  (EQUAL (SUM-LIST (APPEND lst1 lst2))
         (SUM (sum-list lst1)
              (sum-list lst2)))
  :hints (("Goal"
           :in-theory (e/d (sum-list sum) ()))))

(defthm sum-list-of-true-list-fix
  (equal (SUM-LIST (TRUE-LIST-FIX lst))
         (SUM-LIST lst))
  :hints (("Goal"
           :induct (true-list-fix lst)
           :do-not-induct t
           :in-theory (e/d (sum-list true-list-fix)
                           ((:REWRITE ACL2::LIST-FIX-WHEN-TRUE-LISTP)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:REWRITE ACL2::CDR-OF-LIST-FIX)
                            (:DEFINITION TRUE-LISTP))))))

(defthmd and-list-is-and$
  (implies (consp lst)
           (equal (and-list hash lst)
                  (if (atom (cdr lst))
                      (bit-fix (car lst))
                    (and$ (car lst) (and-list hash (cdr lst))))))
  :hints (("Goal"
           :in-theory (e/d (and$ and-list) ()))))

(defthmd and$-is-and-list
  (implies t
           (equal (and$ a b)
                  (and-list 0 (list a b))))
  :hints (("Goal"
           :in-theory (e/d (and$ and-list) ()))))

(defthm -of-
  (implies (integerp a)
           (equal (- (- a))
                  a)))

(defthm sum-of-subtracted
  (and (equal (sum x (-- x))
              0)
       (equal (sum (-- x) x)
              0)
       (equal (sum (-- x) x z)
              (ifix z))
       (equal (sum x (-- x) z)
              (ifix z)))
  :hints (("Goal"
           :in-theory (e/d (sum --) ()))))

(defthmd +-is-SUM
  (implies (and (integerp a)
                (integerp b))
           (equal (+ a b)
                  (sum a b)))
  :hints (("Goal"
           :in-theory (e/d (sum) ()))))

(defthmd mod2-is-m2
  (implies (integerp x)
           (equal (mod x 2)
                  (m2 x)))
  :hints (("Goal"
           :in-theory (e/d (m2) (mod)))))

(defthmd floor2-if-f2
  (implies (integerp x)
           (equal (floor x 2)
                  (f2 x)))
  :hints (("Goal"
           :in-theory (e/d (f2) (floor)))))

(defthm c-is-f2
  (equal (c hash-code a b c)
         (f2 (sum (sum-list a) (sum-list b) (sum-list c))))
  :hints (("Goal"
           :in-theory (e/d (c f2 sum sum-list)
                           (+-is-SUM
                            floor2-if-f2
                            mod2-is-m2)))))

#|(defthm d-sum-to-sum
  (equal (d-sum x y z)
         (sum (sum-list x)
              (sum-list y)
              z))
  :hints (("Goal"
           :in-theory (e/d (d-sum) ()))))||#

#|(defthm d-is-d2
  (equal (d x)
         (d2 x))
  :hints (("Goal"
           :in-theory (e/d (d2 d  --
                               FLOOR2-IF-F2
                               mod2-is-m2)
                           (floor mod
                                  (:REWRITE ACL2::|(- (if a b c))|)
                                  (:REWRITE ACL2::|(floor x 2)| . 1)
                                  (:REWRITE ACL2::|(mod x 2)| . 1)
                                  (:REWRITE SUM-COMM-1))))))||#

(defthm s-is-m2
  (equal (s hash-code b c)
         (m2 (sum (sum-list b) (sum-list c))))
  :hints (("Goal"
           :in-theory (e/d (s m2 sum sum-list)
                           (+-is-SUM
                            floor2-if-f2
                            mod2-is-m2)))))

(defthm sum-list-is-sum
  (equal (sum-list (cons a b))
         (sum a (sum-list b)))
  :hints (("Goal"
           :expand (sum-list (cons a b))
           :in-theory (e/d (sum-list sum
                                     )
                           (SUM-OF-IFIX
                            +-is-SUM)))))

(defthm s-spec-is-m2
  (equal (s-spec lst)
         (m2 (sum-list lst)))
  :hints (("Goal"
           :in-theory (e/d (s-spec
                            mod2-is-m2)
                           ((:REWRITE ACL2::|(equal (if a b c) x)|)
                            (:REWRITE ACL2::|(mod x 2)| . 1))))))

(defthm c-spec-is-f2
  (equal (c-spec lst)
         (f2 (sum-list lst)))
  :hints (("Goal"
           :in-theory (e/d (c-spec
                            floor2-if-f2) ()))))

(defthm s-c-spec-is-list-m2-f2
  (equal (s-c-spec sum)
         (list (m2 (sum-list sum))
               (f2 (sum-list sum))))
  :hints (("Goal"
           :in-theory (e/d (s-c-spec) ()))))

(defthm c-s-spec-is-list-m2-f2
  (equal (c-s-spec sum)
         (list (f2 (sum-list sum))
               (m2 (sum-list sum))))
  :hints (("Goal"
           :in-theory (e/d (c-s-spec) ()))))

(defthm s-of-c-trig-def
  (equal (s-of-c-trig x)
         x)
  :hints (("Goal"
           :in-theory (e/d (s-of-c-trig) ()))))

(defthm s-of-s-lemma1
  (implies t
           (equal (equal (m2 (sum x1 rest1))
                         (m2 (sum x1 rest2)))
                  (equal (m2 rest1) (m2 rest2))))
  :hints (("Goal"
           :in-theory (e/d (m2 sum)
                           (mod2-is-m2
                            +-is-SUM)))))

(defthm s-of-s-lemma2
  (implies t
           (equal (equal (m2 x1)
                         (m2 (sum x1 rest2)))
                  (equal 0 (m2 rest2))))
  :hints (("Goal"
           :in-theory (e/d (m2 sum)
                           (mod2-is-m2
                            +-is-SUM)))))

(encapsulate
  nil

  (defthm f2-of-times2
    (and (equal (f2 (sum (times2 a) b))
                (sum a (f2 (sum b))))
         (equal (f2 (times2 a))
                (ifix a)))
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (sum
                              f2
                              times2)
                             ()))))

  (local
   (defthm f2-of-minus-lemma1
     (equal (f2 (sum (-- a) b))
            (f2 (sum (times2 (-- a)) a b)))
     :hints (("Goal"
              :in-theory (e/d (sum  --
                                    times2) ())))))

  (defthm f2-of-minus
    (implies t ;(bitp a)
             (equal (f2 (sum (-- a) b))
                    (sum (-- a) (f2 (sum a b)))))
    :hints (("Goal"
             :in-theory (e/d () (SUM-COMM-1
                                 SUM-COMM-2))))))

(encapsulate
  nil

  (defthm m2-of-times2
    (and (equal (m2 (sum (times2 a) b))
                (m2 b))
         (equal (m2 (times2 a))
                0))
    :hints (("Goal"
             :in-theory (e/d (m2 sum times2) ()))))

  (local
   (defthm s-of-minus-lemma
     (and (equal (m2 (sum  (-- a) b))
                 (m2 (sum (times2 (-- a)) a b)))
          (equal (m2 (sum (-- a) b))
                 (m2 (sum (times2 (-- a)) a b))))
     :hints (("Goal"
              :in-theory (e/d (sum times2 --) ())))))

  (defthm s-of-minus
    (and (equal (m2 (sum (-- a) b))
                (m2 (sum a b))))
    :hints (("Goal"
             :in-theory (e/d () (SUM-COMM-1
                                 SUM-COMM-2))))))

(encapsulate
  nil

  (defthm d2-of-times2
    (and (equal (d2 (sum (times2 a) b))
                (sum a (d2 (sum b))))
         (equal (d2 (times2 a))
                (ifix a)))
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (d2)
                             (SUM-COMM-1
                              SUM-COMM-2)))))

  (local
   (defthm d2-of-minus-lemma1
     (equal (d2 (sum (-- a) b))
            (d2 (sum (times2 (-- a)) a b)))
     :hints (("Goal"
              :in-theory (e/d (sum  --
                                    times2) ())))))

  (defthm d2-of-minus
    (implies t ;(bitp a)
             (equal (d2 (sum (-- a) b))
                    (sum (-- a) (d2 (sum a b)))))
    :hints (("Goal"
             :in-theory (e/d () (SUM-COMM-1
                                 SUM-COMM-2))))))

(defthm m2-of---
  (and
   (equal (m2 (sum (-- x) rest))
          (m2 (sum x rest)))
   (equal (m2 (sum rest1 (-- x) rest))
          (m2 (sum x rest rest1)))
   (equal (m2 (sum rest1 (-- x)))
          (m2 (sum x rest1)))
   (equal (m2 (-- x))
          (m2 x)))
  :hints (("Goal"
           :use ((:instance s-of-minus
                            (a x) (b rest))
                 (:instance s-of-minus
                            (a x) (b (sum rest rest1))))
           :in-theory (e/d (  ) (s-of-minus)))))

(defthm m2-of-ifix
  (equal (m2 (ifix x))
         (m2 x))
  :hints (("Goal"
           :in-theory (e/d (m2) ()))))

(defthm f2-of-ifix
  (equal (f2 (ifix x))
         (f2 x))
  :hints (("Goal"
           :in-theory (e/d (f2) ()))))

(defthm ifix-of-f2
  (equal (ifix (f2 x))
         (f2 x))
  :hints (("Goal"
           :in-theory (e/d (ifix f2) ()))))

(defthm ifix-of-m2
  (equal (ifix (m2 x))
         (m2 x))
  :hints (("Goal"
           :in-theory (e/d (ifix)
                           ()))))

(defthm sum-of-equals
  (and (equal (equal (sum a b)
                     (sum a c))
              (equal (ifix b)
                     (ifix c)))
       (equal (equal (sum b a)
                     (sum a c))
              (equal (ifix b)
                     (ifix c)))
       (equal (equal (sum x a b)
                     (sum a c))
              (equal (sum b x)
                     (ifix c)))
       (equal (equal (sum x a b)
                     (sum y a c))
              (equal (sum x b)
                     (sum y c))))
  :hints (("Goal"
           :in-theory (e/d (sum) (+-is-SUM)))))

(defthm integerp-f2
  (integerp (f2 x)))

(defthm dummy-sum-cancel-lemma1
  (implies (equal (sum a b) 0)
           (equal (sum a b c) (ifix c)))
  :hints (("Goal"
           :in-theory (e/d (sum) ()))))

(defthm f2-of-bit
  (implies (bitp x)
           (equal (f2 x)
                  0))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule m2-of-m2
  (and (equal (m2 (m2 x))
              (m2 x))
       (equal (m2 (sum (m2 x) y))
              (m2 (sum x y))))
  :hints (("Goal"
           :in-theory (e/d (m2 sum) ()))))

(defthm m2-of-m2-extended
  (and (equal (m2 (sum a b c (m2 x)))
              (m2 (sum a b c x)))
       (equal (m2 (sum a b (m2 x)))
              (m2 (sum a b x))))
  :hints (("Goal"
           :use ((:instance M2-OF-M2
                            (x x)
                            (y (sum a b c)))
                 (:instance M2-OF-M2
                            (x x)
                            (y (sum a b))))
           :in-theory (e/d () (M2-OF-M2)))))

(defthmd sum-of-repeated-to-times2
  (and (equal (sum x x)
              (times2 x))
       (equal (sum x x y)
              (sum (times2 x) y)))
  :hints (("Goal"
           :in-theory (e/d (times2) ()))))

(defthm times2-of-sum
  (equal (times2 (sum a b))
         (sum (times2 a) (times2 b)))
  :hints (("Goal"
           :in-theory (e/d (times2) ()))))

(defthm d2-to-f2
  (and (EQUAL (d2 (sum (-- (m2 x)) x))
              (f2 x))
       (EQUAL (d2 (sum x (-- (m2 x))))
              (f2 x)))
  :hints (("Goal"
           :in-theory (e/d (sum m2 d2 f2) ()))))

(defthmd f2-to-d2
  (EQUAL (f2 x)
         (d2 (sum (-- (m2 x)) x)))
  :hints (("Goal"
           :in-theory (e/d ()
                           (SUM-COMM-1
                            SUM-COMM-2
                            (:REWRITE ACL2::|(mod x 2)| . 1)
                            (:REWRITE ACL2::|(equal (if a b c) x)|)
                            (:REWRITE ACL2::|(floor x 2)| . 1))))))

(defthmd equal-sum-of-negated
  (and (equal (equal (sum x y) (sum (-- a) b))
              (equal (sum x y a) (ifix b)))
       (equal (equal (sum x y) (sum k (-- a) b))
              (equal (sum x y a) (sum k b)))
       (equal (equal (sum x y) (sum k (-- a)))
              (equal (sum x y a) (ifix k)))
       (equal (equal (sum x y) (sum k l (-- a) b))
              (equal (sum x y a) (sum k l b))))
  :hints (("Goal"
           :in-theory (e/d (sum --) ()))))

(defthm evenpi-of-times2
  (and (equal (evenpi (sum (times2 a) x))
              (evenpi x))
       (equal (evenpi (sum x (times2 a)))
              (evenpi x))
       (equal (evenpi (sum x y (times2 a)))
              (evenpi (sum x y)))
       (equal (evenpi (times2 a))
              t))
  :hints (("Goal"
           :in-theory (e/d (sum evenpi times2) ()))))

(defthmd sum-with-oddp
  (implies (and (not (evenp x))
                (integerp x)
                (integerp other))
           (equal (evenp (+ x other))
                  (not (evenp other)))))

(defthmd sum-with-evenp
  (implies (and (evenp x)
                (integerp x)
                (integerp other))
           (equal (evenp (+ x other))
                  (evenp other))))

(defthmd evenpi-lemma-1-lemma
  (IMPLIES (AND (EQUAL (EVENP (IFIX S1))
                       (EVENP (IFIX B1)))
                (EQUAL (EVENP (IFIX S2))
                       (EVENP (IFIX B2))))
           (equal (EVENP (+ (IFIX S1) (IFIX S2)))
                  (EVENP (+ (IFIX B1) (IFIX B2))))))

(defthmd evenpi-lemma-1
  (implies (and (equal (evenpi s1) (evenpi b1))
                (equal (evenpi s2) (evenpi b2))
                (evenpi (sum a s1 s2)))
           (evenpi (sum a b1 b2)))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance evenpi-lemma-1-lemma))
           :cases ((evenpi a))
           :in-theory (e/d (evenpi
                            sum-with-evenp
                            sum
                            sum-with-oddp)
                           (evenp)))))

(add-invisible-fns binary-sum --)
(add-invisible-fns binary-sum m2)
(add-invisible-fns binary-sum sum-list)
(add-invisible-fns binary-sum times2)

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (local
   (in-theory (disable mod floor)))

  (defthmd d2-is-divide-by-2
    (implies (evenpi x)
             (equal (d2 x)
                    (/ (ifix x) 2)))
    :hints (("Goal"
             :in-theory (e/d (d2 f2 m2 sum evenp evenpi) ()))))

  (defthm evenpi-of-sum
    (implies (and (evenpi x)
                  (evenpi y))
             (evenpi (sum x y)))
    :hints (("Goal"
             :in-theory (e/d (evenpi sum) ()))))

  (local
   (defthm sum-of-d2-lemma
     (IMPLIES (AND (EVENPI X) (EVENPI Y))
              (EQUAL (SUM (* 1/2 (IFIX X)) (* 1/2 (IFIX Y)))
                     (* 1/2 (SUM X Y))))
     :hints (("Goal"
              :in-theory (e/d (sum evenpi) ())))))

  (defthm sum-of-d2
    (implies (and (evenpi x)
                  (evenpi y))
             (and (equal (sum (d2 x) (d2 y))
                         (d2 (sum x Y)))
                  (equal (sum (d2 x) (d2 y) z)
                         (sum (d2 (sum x Y)) z))))
    :hints (("Goal"
             :use ((:instance sum-of-d2-lemma))
             :in-theory (e/d (d2-is-divide-by-2)
                             (sum-of-d2-lemma)))))

  (defthm evenpi-of-term-minus-its-mod
    (and (evenpi (SUM A (-- (M2 A))))
         (evenpi (SUM (-- (M2 A)) A)))
    :hints (("Goal"
             :in-theory (e/d (m2 sum evenpi) ()))))

  (defthm sum-of-f2s
    (and (equal (sum (f2 a) (f2 b))
                (d2 (sum (-- (m2 a)) (-- (m2 b))
                         a b)))
         (equal (sum (f2 a) (f2 b) c)
                (sum (d2 (sum (-- (m2 a)) (-- (m2 b))
                              a b))
                     c)))
    :hints (("Goal"
             :in-theory (e/d (f2-to-d2)
                             (d2-to-f2
                              D2-OF-MINUS
                              )))))

  (defthm sum-of-f2s-and-d2
    (implies (evenpi b)
             (and (equal (sum (f2 a) (d2 b))
                         (d2 (sum (-- (m2 a))
                                  a b)))
                  (equal (sum (d2 b) (f2 a))
                         (d2 (sum (-- (m2 a))
                                  a b)))
                  (equal (sum (f2 a) (d2 b) c)
                         (sum (d2 (sum (-- (m2 a))
                                       a b))
                              c))
                  (equal (sum (d2 b) (f2 a) c)
                         (sum (d2 (sum (-- (m2 a))
                                       a b))
                              c))))
    :hints (("Goal"
             :in-theory (e/d (f2-to-d2)
                             (d2-to-f2
                              D2-OF-MINUS
                              ))))))

(defthm evenpi-for-2-d2-arguments
  (evenpi (sum a b (-- (m2 (sum a b)))))
  :hints (("Goal"
           :in-theory (e/d (evenpi sum m2) ()))))

(defthm evenpi-for-3-d2-arguments
  (evenpi (sum a b c (-- (m2 (sum a b c)))))
  :hints (("Goal"
           :in-theory (e/d (evenpi sum m2) ()))))

(defthm evenpi-for-4-d2-arguments
  (evenpi (sum a b c d (-- (m2 (sum a b c d)))))
  :hints (("Goal"
           :in-theory (e/d (evenpi sum m2) ()))))

(defthm evenpi-sum-clear
  (and (equal (evenpi (sum a a b))
              (evenpi (ifix b)))
       (equal (evenpi (sum a a))
              t)
       (equal (evenpi (sum c a a b))
              (evenpi (sum b c)))
       (equal (evenpi (sum c a a))
              (evenpi (sum c)))

       (equal (evenpi (sum c d a a b))
              (evenpi (sum b c d)))
       (equal (evenpi (sum c d a a ))
              (evenpi (sum c d)))

       (equal (evenpi (sum c d e a a b))
              (evenpi (sum b c d e)))
       (equal (evenpi (sum c d e a a))
              (evenpi (sum c d e))))
  :hints (("Goal"
           :in-theory (e/d (sum evenpi) ()))))

(defthm m2-with-extra
  (implies (equal (m2 x) (m2 y))
           (equal (equal (m2 (sum x other))
                         (m2 (sum y other)))
                  t))
  :hints (("Goal"
           :in-theory (e/d (m2 sum) ()))))

(defthm m2-with-extra-dummy-lemma
  (implies (equal (m2 (sum a b)) (m2 (sum x y z)))
           (equal (equal (m2 (sum other a b))
                         (m2 (sum x y z other)))
                  t))
  :hints (("Goal"
           :use ((:instance
                  m2-with-extra
                  (x (sum a b))
                  (y (sum x y z))
                  (other other)))
           :in-theory (e/d ( ) (m2-with-extra)))))

(defthm evenpi-with-other
  (implies (equal (evenpi x) (evenpi y))
           (equal (equal (evenpi (sum x z))
                         (evenpi (sum y z)))
                  t))
  :hints (("Goal"
           :in-theory (e/d (evenpi sum)
                           ()))))
(defthm bitp-m2
  (bitp (m2 x))
  :hints (("Goal"
           :in-theory (e/d (m2 sum f2) ()))))

(in-theory (enable +-is-SUM
                   mod2-is-m2
                   floor2-if-f2))


(defthm sum-of-negated-elements
  (implies (equal (-- a) b)
           (and (equal (sum a b) 0)
                (equal (sum b a) 0)
                (equal (sum b a rest) (ifix rest))
                (equal (sum a b rest) (ifix rest))))
  :hints (("Goal"
           :in-theory (e/d (sum --)
                           (+-IS-SUM)))))


(defthmd f2-of-times2-reverse
  (implies (syntaxp (or (atom term)
                        (not (equal (car term) 'f2))))
           (and (equal (sum term (f2 term2))
                       (f2 (sum (times2 term) term2)))
                (equal (sum (f2 term2) term)
                       (f2 (sum (times2 term) term2)))
                (equal (sum term (f2 term2) other)
                       (sum other (f2 (sum (times2 term) term2)))))))
