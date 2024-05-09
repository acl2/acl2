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

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(defthm <-1+-cancel
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (< (+ 1 x) (+ 1 y))
                  (< x y))))

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

  (define ex-from-rp/--loose (x)
    :returns (res rp-termp :hyp (rp-termp x))
    (cond ((and (consp x)
                (consp (cdr x)))
           (if (or (equal (car x) '--))
               (ex-from-rp/--loose (cadr x))
             (if (and (equal (car x) 'rp)
                      (consp (cddr x)))
                 (ex-from-rp/--loose (caddr x))
               x)))
          (t x)))

  (define sum-comm-order-aux (x (cnt natp)
                                &key
                                (orig-term 'orig-term))
    (case-match x
      (('m2 &)
       (mv 'm2 x))
      (('f2 &)
       (mv 'f2 x))
      (('d2 &)
       (mv 'd2 x))
      (('rp-trans x)
       (sum-comm-order-aux x (1+ cnt)))
      (('rp-evl x)
       (sum-comm-order-aux x (1+ cnt)))
      (('ex-from-rp x)
       (sum-comm-order-aux x (1+ cnt)))
      (('-- x)
       (sum-comm-order-aux x (1+ cnt)))
      (('times & x)
       (sum-comm-order-aux x (1+ cnt)))
      (('unary-- x)
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
       (mv 'mv-nth (list (caddr x) (cadr x) orig-term)))
      (('pp-sum-merge & &)
       (mv 'merge x))
      (('s-sum-merge & &)
       (mv 'merge x))
      (('car x)
       (sum-comm-order-aux x (1+ cnt)))
      (('ifix x)
       (sum-comm-order-aux x (1+ cnt)))
      (('cdr x)
       (sum-comm-order-aux x (1+ cnt)))
      (('binary-sum & &)
       (mv 'binary-sum x))
      (('binary-m2-chain & &)
       (mv 'binary-m2-chain x))
      (('ex-from-rp/-- &)
       (mv 'm2 x))
      (('quote x)
       (mv 'quote x))
      (('ex-from-rp x)
       (sum-comm-order-aux x (1+ cnt)))
      (&
       (if (consp x)
           (mv 'mv-nth (list x cnt orig-term))
         (mv 'atom (list x cnt orig-term))))))

  (define sum-comm-order (a b &key (for-m2-chain 'nil))
    (b* ((a (ex-from-rp/--loose a))
         (b (ex-from-rp/--loose b))
         ((mv a-type a)
          (sum-comm-order-aux a 0 :orig-term a))
         ((mv b-type b)
          (sum-comm-order-aux b 0 :orig-term b)))
      (cond
       ((and (not for-m2-chain)
             (or (equal a-type 'binary-sum)
                 (equal b-type 'binary-sum)))
        nil)
       ((and for-m2-chain
             (or (equal a-type 'binary-m2-chain)
                 (equal b-type 'binary-m2-chain)))
        nil)
       ((equal a-type b-type)
        (b* (((mv res &) (lexorder2 a b)))
          res))
       ((xor (equal a-type 'quote)
             (equal b-type 'quote))
        (equal b-type 'quote))
       ((xor (equal a-type 'm2)
             (equal b-type 'm2))
        (not (equal b-type 'm2)))
       ((xor (equal a-type 'mv-nth)
             (equal b-type 'mv-nth))
        (not (equal b-type 'mv-nth)))
       ((xor (equal a-type 'merge)
             (equal b-type 'merge))
        (not (equal b-type 'merge)))
       ((xor (and (equal a-type 'd2)
                  (equal b-type 'd2))
             (and (equal a-type 'f2)
                  (equal b-type 'f2)))
        (b* (((mv res &) (lexorder2 a b)))
          res))
       ((xor (equal a-type 'd2)
             (equal b-type 'd2))
        (not (equal a-type 'd2)))
       ((xor (equal a-type 'f2)
             (equal b-type 'f2))
        (not (equal a-type 'f2)))
       ((and (integerp a-type)
             (integerp b-type))
        (b* (((mv res equals) (lexorder2 a b)))
          (if equals
              (> a-type b-type)
            res)))
       ((xor (equal a-type 'atom)
             (equal b-type 'atom))
        (equal a-type 'atom))
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
                                 SUM-COMM-2)))))

  (defthm f2-of-minus-2
    (implies t ;(bitp a)
             (equal (f2 (sum (- a) b))
                    (sum (- a) (f2 (sum a b)))))
    :hints (("Goal"
             :use ((:instance f2-of-minus))
             :in-theory (e/d (-- ifix sum f2) (SUM-COMM-1
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
          (m2 x))

   )
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

(defthm --of---
  (equal (-- (-- a))
         (ifix a))
  :hints (("Goal"
           :in-theory (e/d (-- sum)
                           (+-is-SUM)))))

(defthm sumof-the-same-cancel-with--
  (and (equal (sum (-- a) a)
              0)
       (equal (sum a (-- a))
              0)
       (equal (sum (-- a) a b)
              (ifix b))
       (equal (sum a (-- a) b)
              (ifix b)))
  :hints (("Goal"
           :in-theory (e/d (-- sum)
                           (+-is-SUM)))))

(defthm logbit-p-of-quoted
  (implies (and (syntaxp (quotep x)))
           (equal (logbit-p (cons x y))
                  (and (equal x 'logbit$inline)
                       (consp y)
                       (consp (cdr y))
                       (not (cddr y)))))
  :hints (("Goal"
           :in-theory (e/d (logbit-p) ()))))

(defthm bit-fix-p-of-quoted
  (implies (and (syntaxp (quotep x)))
           (equal (bit-fix-p (cons x y))
                  (and (equal x 'bit-fix)
                       (consp y)
                       (not (cdr y)))))
  :hints (("Goal"
           :in-theory (e/d (bit-fix-p) ()))))

(defthm pp-p-of-quoted
  (implies (and (syntaxp (quotep x)))
           (equal (pp-p (cons x y))
                  (and (equal x 'pp)
                       (consp y)
                       (not (cdr y)))))
  :hints (("Goal"
           :in-theory (e/d (pp-p) ()))))

(defthm rpterm-p-of-quoted
  (implies (and (syntaxp (quotep x))
                (not (equal x 'quote))
                (not (equal x 'rp))
                (not (equal x 'falist)))
           (equal (rp-termp (cons x y))
                  (and (symbolp x)
                       x
                       (rp-term-listp y))))
  :hints (("Goal"
           :in-theory (e/d (pp-p) ()))))

(defthm is-rp-of-quoted
  (implies (and (syntaxp (quotep x)))
           (equal (is-rp (cons x y))
                  (and (equal x 'rp)
                       (CASE-MATCH y
                         ((('QUOTE TYPE) &)
                          (AND (SYMBOLP TYPE)
                               (NOT (BOOLEANP TYPE))
                               (NOT (EQUAL TYPE 'QUOTE))
                               (NOT (EQUAL TYPE 'RP))
                               (NOT (EQUAL TYPE 'LIST))
                               (NOT (EQUAL TYPE 'FALIST))))
                         (& NIL)))))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm pull-out-nums-last-bit
  (implies (integerp x)
           (equal x
                  (logcons (logcar x)
                           (logcdr x))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d () (+-is-SUM mod2-is-m2 floor2-if-f2)))))

(local
 (use-arithmetic-5 nil))

#!acl2
(defthmd evenp-and-oddp-as-logcar
  (implies (integerp i)
           (and (equal (evenp i)
                       (equal (logcar i) 0))
                (equal (oddp i)
                       (equal (logcar i) 1))))
  :hints (("Goal"
           :in-theory '((:DEFINITION BITP)
                        (:DEFINITION EVENP)
                        (:DEFINITION IFIX)
                        (:DEFINITION IMOD$INLINE)
                        (:DEFINITION LOGCAR$INLINE)
                        (:DEFINITION NOT)
                        (:DEFINITION ODDP)
                        (:EXECUTABLE-COUNTERPART EQUAL)
                        (:EXECUTABLE-COUNTERPART IFIX)
                        (:EXECUTABLE-COUNTERPART UNARY-/)
                        ;;(:FAKE-RUNE-FOR-TYPE-SET NIL)
                        (:REWRITE COMMUTATIVITY-OF-*)
                        (:REWRITE MOD-=-0 . 1)
                        (:REWRITE MOD-=-0 . 2))
           :use acl2::bitp-mod-2)))

(local
 (use-ihs-logops-lemmas t))

(define *-recursive-shfadd (x y)
  :measure (ifix (abs x))
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d* (ifix)
                            (+-is-sum floor2-if-f2))))
  :prepwork ((local (use-arithmetic-5 t)))
  (cond ((not (integerp x))
         0)
        ((= x 0)
         0)
        ((= x 1)
         y)
        ((= x -1)
         (- y))
        (t (+ (if (equal (logcar x) 1) y 0)
              (ash (*-recursive-shfadd (logcdr x) y) 1))))
  ///
  (defthmd *-redef-to-*-recursive-shfadd
    (implies (and (integerp x)
                  (integerp y))
             (equal (* x y)
                    (*-recursive-shfadd x y)))
    :hints (("Goal"
             :in-theory (e/d () ((:REWRITE ACL2::|(floor x 2)| . 1)
                                 +-is-sum
                                 mod2-is-m2
                                 floor2-if-f2))))))

(defthm logcar-of-*
  (implies (and (integerp x)
                (integerp y))
           (equal (logcar (* x y))
                  (* (logcar x)
                     (logcar y))))
  :hints (("Goal"
           :cases ((equal (LOGCAR Y) 1))
           :use ((:instance pull-out-nums-last-bit
                            (x x))
                 (:instance pull-out-nums-last-bit
                            (x y))
                 (:instance *-redef-to-*-recursive-shfadd
                            )
                 #|(:instance *-of-sums
                 (x x)
                 (y (LOGCAR y))
                 (z (* 2 (LOGCDR y))))|#)
           :expand ((*-RECURSIVE-SHFADD X Y))
           :in-theory (e/d* (BITOPS::LOGCAR-MINUS-A
                             bitops::logcar-of-+
                             BITOPS::LOGCAR-OF-LEFT-SHIFT)
                            (logcons
                             ash floor logcar logcdr
                             mod2-is-m2 +-is-SUM
                             floor2-if-f2)))))

(defthm evenp-lemma1
  (implies (and (integerp coef)
                (integerp term)
                (evenp (* coef term)))
           (or (evenp term)
               (evenp coef)))

  :hints (("goal"
           :do-not-induct t
           :use ((:instance pull-out-nums-last-bit
                            (x coef))
                 (:instance pull-out-nums-last-bit
                            (x term)))

           :in-theory (e/d* (acl2::evenp-and-oddp-as-logcar f2 m2 sum)
                            (logcar evenp mod floor floor2-if-f2 mod2-is-m2 +-is-sum)))
          ))

(defthm m2-of-times-when-odd
  (implies (and (not (evenp coef))
                (integerp coef))
           (equal (m2 (times coef term))
                  (m2 term)))
  :hints (("Goal"
           :in-theory (e/d (acl2::evenp-and-oddp-as-logcar
                            BITOPS::SMALL-MODS
                            m2 f2 times sum ifix)
                           (evenp
                            ACL2::LOGCAR$INLINE
                            ACL2::IMOD$INLINE
                            floor mod floor2-if-f2 MOD2-IS-M2 +-is-sum)))))

(defthm m2-of-times-when-odd-2
  (implies (and (not (evenp coef))
                (integerp coef))
           (equal (m2 (sum (times coef term) other))
                  (m2 (sum term other))))
  :hints (("Goal"
           :in-theory (e/d (acl2::evenp-and-oddp-as-logcar
                            bitops::logcar-of-+
                            bitops::small-mods
                            m2 f2 times sum ifix)
                           (evenp
                            acl2::logcar$inline
                            acl2::imod$inline
                            floor mod floor2-if-f2 mod2-is-m2 +-is-sum)))))

(defthm m2-of-times-when-even
  (implies (and (evenp coef)
                (integerp coef))
           (equal (m2 (times coef term))
                  0))
  :hints (("Goal"
           :in-theory (e/d (acl2::evenp-and-oddp-as-logcar
                            BITOPS::SMALL-MODS
                            m2 f2 times sum ifix)
                           (evenp
                            ACL2::LOGCAR$INLINE
                            ACL2::IMOD$INLINE
                            floor mod floor2-if-f2 MOD2-IS-M2 +-is-sum)))))

(defthm m2-of-times-when-even-2
  (implies (and (evenp coef)
                (integerp coef))
           (equal (m2 (sum (times coef term) other))
                  (m2 other)))
  :hints (("Goal"
           :use ((:instance m2-of-times-when-even))
           :in-theory (e/d (acl2::evenp-and-oddp-as-logcar
                            bitops::logcar-of-+
                            bitops::small-mods
                            m2 f2 times sum ifix)
                           (evenp
                            acl2::logcar$inline
                            acl2::imod$inline
                            floor mod floor2-if-f2 mod2-is-m2 +-is-sum)))))

(defthm *-with-0
  (and (equal (* 0 x) 0)
       (equal (* x 0) 0)))

(local
 (use-arithmetic-5 t))

(local
 (defthmd f2-when-oddp
   (implies (and (not (evenp coef))
                 (integerp coef))
            (equal (f2 coef)
                   (/ (1- coef) 2)))
   :hints (("Goal"
            :in-theory (e/d (ifix sum f2)
                            (+-is-sum floor2-if-f2))))))

(defthm |x + (* (f2 coef) x) + (* (f2 coef) x)|-when-oddp-lemma
  (IMPLIES (AND (NOT (EVENP COEF))
                (INTEGERP COEF)
                (INTEGERP X))
           (EQUAL (+ 1 (* 2 (F2 COEF))) COEF))
  :hints (("Goal"
           :in-theory (e/d (f2-when-oddp) ()))))

(defthm |x + (* (f2 coef) x) + (* (f2 coef) x)|-when-oddp
  (implies (and (not (evenp coef))
                (integerp coef)
                (integerp x))
           (and (equal (sum x (* (f2 coef) x) (* (f2 coef) x))
                       (* coef x))
                (equal (sum x (times (f2 coef) x) (times (f2 coef) x))
                       (* coef x))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (ifix sum times)
                           (evenp floor2-if-f2 +-is-sum)))))

(defthm |(1/2 coef x) (1/2 coef x)|-when-evenp
  (implies (and (integerp x)
                (evenp coef)
                (integerp coef))
           (equal (sum (* 1/2 coef x) (* 1/2 coef x))
                  (sum (* coef x))))
  :hints (("Goal"
           :in-theory (e/d (sum ifix) (+-is-sum)))))

(defthm d2-of-repeated
  (and (equal (d2 (sum x x))
              (ifix x))
       (equal (d2 (sum a a b))
              (sum a (d2 b))))
  :hints (("Goal"
           :in-theory (e/d (evenpi
                            d2 m2 sum
                            f2)
                           (floor2-if-f2 mod2-is-m2 +-is-sum)))))

(defthm m2+f2+f2-of-num-is-num
  (equal (sum (m2 x)
              (f2 x)
              (f2 x))
         (ifix x))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(defthmd times-of-sum-reverse
  (and (equal (sum (times coef x)
                   (times coef y))
              (times coef (sum x y)))
       (equal (sum (times coef x)
                   (-- (times coef y)))
              (times coef (sum x (-- y))))
       (equal (sum (-- (times coef y))
                   (times coef x))
              (times coef (sum x (-- y))))

       (equal (sum (times coef x)
                   (times coef y)
                   other)
              (sum (times coef (sum x y))
                   other))
       (equal (sum (times coef x)
                   (-- (times coef y))
                   other)
              (sum (times coef (sum x (-- y)))
                   other))
       (equal (sum (-- (times coef y))
                   (times coef x)
                   other)
              (sum (times coef (sum x (-- y)))
                   other))

       (equal (sum (times coef x)
                   x)
              (times (1+ (ifix coef)) x))
       (equal (sum (times coef x)
                   x
                   other)
              (sum (times (1+ (ifix coef)) x)
                   other))

       (equal (sum (times coef x)
                   (-- x))
              (sum (times (1- (ifix coef)) x)))
       (equal (sum (times coef x)
                   (-- x)
                   other)
              (sum (times (1- (ifix coef)) x)
                   other))
       )
  :hints (("Goal"
           :in-theory (e/d (-- ifix times sum)
                           (+-IS-SUM)))))

(defthm times-of-repeated-f2-coefs
  (implies (not (evenp (ifix coef)))
           (and (equal (sum (times (f2 coef) y)
                            (times (f2 coef) y)
                            y  other)
                       (sum (times coef y) other))
                (equal (sum (times (f2 coef) y)
                            (times (f2 coef) y)
                            y )
                       (times coef y))))
  :hints (("Goal"
           :cases ((integerp coef))
           :in-theory (e/d (times-of-sum-reverse
                            ifix sum times)
                           (evenp
                            +-IS-SUM
                            floor2-if-f2)))))

(defthm times-of-repeated-f2-coefs-when-even
  (implies (evenp (ifix coef))
           (and (equal (sum (times (f2 coef) y)
                            (times (f2 coef) y)
                            other)
                       (sum (times coef y) other))
                (equal (sum (times (f2 coef) y)
                            (times (f2 coef) y))
                       (times coef y))))
  :hints (("Goal"
           :in-theory (e/d (times-of-sum-reverse
                            f2 ifix times sum)
                           (floor2-if-f2  +-IS-SUM)))))

(defthmd divide-by-2-is-floor2-when-even
  (implies (evenp x)
           (equal (* 1/2 x)
                  (floor x 2))))

(progn
  (define binary-m2-chain (a b)
    (m2 (sum a b)))

  (defmacro m2-chain (&rest rp::rst)
    (cond ((null rp::rst) 0)
          ((null (cdr rp::rst))
           (list 'm2 (car rp::rst)))
          (t (xxxjoin 'binary-m2-chain rp::rst))))

  (add-macro-fn m2-chain binary-m2-chain t)

  (defthmd m2-to-m2-chain
    (and #|(implies (syntaxp (or (atom a)
     (not (equal (car a) 'binary-sum))))
     (equal (m2 a)
     (m2-chain a 0)))|#
     (equal (m2 (sum a b))
            (m2-chain a b)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))


  (defthm m2-chain-comm
    (and
     (implies (syntaxp (sum-comm-order a b :for-m2-chain t))
              (equal  (m2-chain b a)
                      (m2-chain a b)))
     (implies (syntaxp (sum-comm-order a b :for-m2-chain t))
              (equal  (m2-chain b a c)
                      (m2-chain a b c))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) (m2-to-m2-chain)))))

  (defthm m2-chain-reorder
    (and (equal (m2-chain (sum a b) c)
                (m2-chain a b c))
         (equal (m2-chain a (sum b c))
                (m2-chain a b c))
         (equal (m2-chain (m2-chain a b) c)
                (m2-chain a b c)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) (m2-to-m2-chain)))))

  (defthm m2-chain-of-nil
    (and (equal (m2-chain nil a)
                (m2-chain a))
         (equal (m2-chain a nil)
                (m2-chain a)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))

  (defthm m2-of-m2-chain
    (equal (m2 (m2-chain a b))
           (m2-chain a b))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))

  (defthm m2-chain-of-m2
    (and (equal (m2-chain (m2 x) y)
                (m2-chain x y))
         (equal (m2-chain y (m2 x))
                (m2-chain x y)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))

  (defthm m2-chain-of-0
    (and (equal (m2-chain 0 a)
                (m2-chain a))
         (equal (m2-chain a 0)
                (m2-chain a)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))

  (defthm m2-chain-of-same-e
    (equal (equal (m2-chain x a)
                  (m2-chain y a))
           (equal (m2 x) (m2 y)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))
  )
(defthm dummy-m2-lemma7
  (implies (and (EQUAL (M2 y)
                       (M2 z))
                (EQUAL (M2 x)
                       (M2 z)))
           (equal (M2 (SUM x y))
                  0))
  :hints (("Goal"
           :in-theory (e/d (m2 sum f2 ifix) (floor2-if-f2 mod2-is-m2
                                                          +-is-sum)))))

(defthm evenp-of-sum-of-evenps-2
  (and (implies (and (not (evenp x))
                     (not (evenp y))
                     (integerp x)
                     (integerp y))
                (evenp (sum x y)))
       (implies (and (not (evenp x))
                     (evenp y)
                     (integerp x)
                     (integerp y))
                (and (not (evenp (sum x y)))
                     (not (evenp (sum y x))))))
  :hints (("goal"
           :in-theory (e/d (sum ifix evenp) (+-is-sum)))))

(defthm times-of-negated-coef
  (implies (integerp coef)
           (equal (times (- coef) term)
                  (- (times coef term))))
  :hints (("Goal"
           :in-theory (e/d (times ifix) ()))))

(defthm times-of-1
  (equal (times 1 x)
         (ifix x))
  :hints (("Goal"
           :in-theory (e/d (times) ()))))

(define *-recursive-cntadd (x y)
  :measure (ifix (abs x))
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d* (ifix)
                            (+-is-sum floor2-if-f2))))
  :prepwork ((local (use-arithmetic-5 t)))
  (cond ((not (integerp x))
         0)
        ((= x 0)
         0)
        ((= x 1)
         y)
        ((= x -1)
         (- y))
        (t (if (< x 0)
               (+ (- y)
                  (*-recursive-cntadd (1+ x) y))
             (+ y
                (*-recursive-cntadd (1- x) y)))))
  ///
  (defthmd *-redef-to-*-recursive-cntadd
    (implies (and (integerp x)
                  (integerp y))
             (equal (* x y)
                    (*-recursive-cntadd x y)))
    :hints (("Goal"
             :in-theory (e/d () ((:REWRITE ACL2::|(floor x 2)| . 1)
                                 +-is-sum
                                 mod2-is-m2
                                 floor2-if-f2))))))

(defthmd move-over-multiplier
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (not (equal y 0)))
           (equal (equal (* x y) z)
                  (equal x (/ z y)))))

(defthm when-mult-of-two-integers-is-1
  (implies (and (EQUAL (* x y) 1)
                ;;(< x 0)
                (integerp x)
                (integerp y))
           (or (and (equal x -1)
                    (equal y -1))
               (and (equal x 1)
                    (equal y 1))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal y 0))
           ;; :cases ((< x -1)
           ;;         (< y -1)
           ;;         (> x 1)
           ;;         (> y 1))
           :in-theory (e/d (move-over-multiplier
                            sum f2 m2 *-recursive-shfadd
                            ;;*-redef-to-*-recursive-cntadd
                            *-recursive-cntadd)
                           (ash floor2-if-f2
                                +-is-sum
                                mod2-is-m2)))))
(defthm times-of---
  (and (equal (times a (-- b))
              (-- (times a b)))
       (equal (times (-- a) b)
              (-- (times a b))))
  :hints (("Goal"
           :in-theory (e/d (times ifix --) ()))))

(defthm type-fix-of-times
  (equal (ifix (times a b))
         (times a b))
  :hints (("goal"
           :in-theory (e/d (times ifix) ()))))

(defthm times-comm
  (and (equal (times b (times a c))
              (times a (times b c)))
       (equal (times b a)
              (times a b)))
  :hints (("goal"
           :in-theory (e/d (times) ()))))

(defthm times-reoder
  (equal (times (times a b) c)
         (times a (times b c)))
  :hints (("goal"
           :in-theory (e/d (times) ()))))

(defthm and$-of-repeated-vars
  (and (equal (and$ a a b)
              (and$ a b))
       (equal (and$ a a)
              (bit-fix a)))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthmd sum-of-repeated-to-times
  (and (equal (sum x x)
              (times 2 x))
       (equal (sum x x o)
              (sum (times 2 x) o)))
  :hints (("Goal"
           :in-theory (e/d (times sum)
                           (+-IS-SUM)))))

#|(skip-proofs
(defthm f2-of-negated-oddp
(implies (and (not (evenp x))
(integerp x))
(equal (f2 (- x))
(1- (- (f2 x)))))))|#

(defthmd -to---
  (and (implies (syntaxp (and (not (quotep x))
                              (not (integerp x))))
                (and (equal (sum (- x) y)
                            (sum (-- x) y))
                     (equal (sum y (- x))
                            (sum (-- x) y))
                     (equal (ifix (- x))
                            (-- x))
                     (equal (times2 (- x))
                            (-- (times2 x)))))
       (equal (- (times coef x))
              (-- (times coef x))))
  :hints (("Goal"
           :in-theory (e/d (ifix -- times2 sum)
                           (+-IS-SUM)))))

(defthm multiplication-of-1-and-sum
  (and (equal (* -1 (sum x y))
              (-- (sum x y)))
       (equal (* 1 (sum x y))
              (sum x y)))
  :hints (("Goal"
           :in-theory (e/d (sum ifix --) (+-IS-SUM)))))

(defthm odd+1-is-even
  (implies (and (not (evenp (ifix x))))
           (and (evenp (sum 1 x))
                (evenp (sum x 1))
                (evenp (sum -1 x))
                (evenp (sum x -1))))
  :hints (("Goal"
           :in-theory (e/d (sum ifix) (+-IS-SUM)))))

(defthm times-of-repeated-sum-elements
  (equal (times coef (sum x x))
         (times (* 2 (ifix coef)) x))
  :hints (("Goal"
           :in-theory (e/d (TIMES
                            sum)
                           (+-IS-SUM)))))

(defthm f2*2-when-evenp
  (implies (evenp (ifix x))
           (equal (* 2 (f2 x))
                  (ifix x)))
  :hints (("Goal"
           :in-theory (e/d (f2 ifix)
                           (floor2-if-f2)))))

(defthm integerp-of-1/2+1/2*odd
  (implies (and (not (evenp x))
                (integerp x))
           (and (integerp (+ 1/2 (* 1/2 x)))
                (integerp (+ -1/2 (* 1/2 x)))))
  :hints (("goal"
           :in-theory (e/d () ()))))



(progn
  (defun find-common-sum-item (x y)
    (declare (ignorable x y)
             (xargs :measure (+ (acl2-count x)
                                (acl2-count y))
                    :otf-flg nil
                    :hints (("Goal"
                             :do-not-induct t
                             :in-theory (e/d ()
                                             (
                                              +-IS-SUM))))))
    (b* (((mv cur-x rest-x) (case-match x
                              (('binary-sum cur-x rest-x)
                               (mv cur-x rest-x))
                              (('binary-m2-chain cur-x rest-x)
                               (mv cur-x rest-x))
                              (('ifix cur-x)
                               (mv cur-x nil))
                              (& (mv x nil))))
         ((mv cur-y rest-y) (case-match y
                              (('binary-sum cur-y rest-y)
                               (mv cur-y rest-y))
                              (('binary-m2-chain cur-y rest-y)
                               (mv cur-y rest-y))
                              (('ifix cur-y)
                               (mv cur-y nil))
                              (& (mv y nil))))
         ((when (equal cur-y cur-x))
          `((common . ,cur-y))))
      (cond ((and rest-x
                  rest-y)
             (or (find-common-sum-item rest-x y)
                 (find-common-sum-item x rest-y)))
            (rest-y
             (find-common-sum-item x rest-y))
            (rest-x
             (find-common-sum-item rest-x y))
            (t nil))))

  (defthm sum-cancel-common
    (and (implies (bind-free (find-common-sum-item `(binary-sum ,x ,y) `(binary-sum ,a ,b))
                             (common))
                  (equal (equal (sum x y)
                                (sum a b))
                         (equal (sum x y (-- common))
                                (sum a b (-- common)))))
         (implies (bind-free (find-common-sum-item `(binary-sum ,x ,y) a)
                             (common))
                  (and (equal (equal (sum x y)
                                     (ifix a))
                              (equal (sum x y (-- common))
                                     (sum a (-- common))))
                       (equal (equal (ifix a)
                                     (sum x y))
                              (equal (sum x y (-- common))
                                     (sum a (-- common)))))))
    :hints (("Goal"
             :in-theory (e/d (sum --)
                             (+-IS-SUM)))))

  (defthm m2-of-sum-cancel-common
    (and (implies (bind-free (find-common-sum-item `(binary-sum ,x ,y) `(binary-sum ,x2 ,y2))
                             (common))
                  (equal (equal (m2 (sum x y))
                                (m2 (sum x2 y2)))
                         (equal (m2 (sum x y (-- common)))
                                (m2 (sum x2 y2 (-- common))))))
         (implies (bind-free (find-common-sum-item `(binary-sum ,x ,y) x2)
                             (common))
                  (and (equal (equal (m2 (sum x y))
                                     (m2 x2))
                              (equal (m2 (sum x y (-- common)))
                                     (m2 (sum x2 (-- common)))))
                       (equal (equal (m2 x2)
                                     (m2 (sum x y)))
                              (equal (m2 (sum x y (-- common)))
                                     (m2 (sum x2 (-- common))))))))
    :hints (("Goal"
             :in-theory (e/d ()
                             (M2-OF---
                              S-OF-MINUS)))))

  (defthm m2-chain-cancel-common
    (and (implies (bind-free (find-common-sum-item `(binary-m2-chain ,x ,y) `(binary-m2-chain ,x2 ,y2))
                             (common))
                  (equal (equal (m2-chain x y)
                                (m2-chain x2 y2))
                         (equal (m2-chain x y (-- common))
                                (m2-chain x2 y2 (-- common)))))
         (implies (bind-free (find-common-sum-item `(binary-m2-chain ,x ,y) x2)
                             (common))
                  (and (equal (equal (m2-chain x y)
                                     (m2-chain x2))
                              (equal (m2-chain x y (-- common))
                                     (m2-chain x2 (-- common))))
                       (equal (equal (m2-chain x2)
                                     (m2-chain x y))
                              (equal (m2-chain x y (-- common))
                                     (m2-chain x2 (-- common)))))))
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (m2-chain)
                             (M2-CHAIN-OF-M2))))))

(defthm --of-ifix
  (equal (-- (ifix x))
         (-- x))
  :hints (("Goal"
           :in-theory (e/d (--) ()))))

(defthm m2-chain-of---
  (and (equal (m2-chain (-- x) y)
              (m2-chain x y))
       (equal (m2-chain y (-- x))
              (m2-chain y x))
       (equal (m2-chain (-- x))
              (m2-chain x)))
  :hints (("Goal"
           :in-theory (e/d (m2-chain)
                           (M2-CHAIN-OF-M2)))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))

  (defthm m2-chain-of-repeated
    (and (equal (m2-chain x x y)
                (m2-chain y))
         (equal (m2-chain x x)
                0))
    :hints (("Goal"
             :in-theory (e/d (m2-chain m2 sum)
                             (M2-CHAIN-OF-M2
                              MOD2-IS-M2
                              +-IS-SUM))))))

(defthm bitp-of-m2-chain
  (bitp (m2-chain x y))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))

(encapsulate
  nil

  ;;(local (use-arithmetic-5 t))


  (defthmd m2-of-oddp
    (implies (and (oddp a)
                  (case-split (integerp a))
                  (syntaxp (atom a)))
             (equal (m2 (sum a b))
                    (m2 (sum 1 b))))
    :hints (("Goal"
             :in-theory (e/d (m2
                              --
                              sum
                              (:REWRITE ACL2::|(* a (/ a) b)|)
                              (:REWRITE ACL2::|(* x (+ y z))|)
                              (:REWRITE ACL2::|(* y x)|)
                              (:REWRITE ACL2::|(mod x 2)| . 1)
                              (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                              (:REWRITE IFIX-OPENER)
                              (:REWRITE ACL2::SUM-IS-EVEN . 1))
                             (mod2-is-m2 +-IS-SUM)))))

  (defthmd rw-times-when-coef-is-odd 
    (and (implies (and (integerp coef)
                       (oddp coef))
                  (equal (times coef x)
                         (sum (times (* 2 (floor coef 2)) x)
                              x))))
    :hints (("Goal"
             :in-theory (e/d (times sum f2)
                             (FLOOR2-IF-F2 +-IS-SUM)))))

  (defthmd rw-times-when-coef-is-even
    (and (implies (and (integerp coef)
                       (evenp coef))
                  (equal (times coef x)
                         (times (* 2 (floor coef 2)) x))))
    :hints (("Goal"
             :in-theory (e/d (times sum f2)
                             (FLOOR2-IF-F2 +-IS-SUM)))))
  
  (defthm m2-chain-of-oddp-times
    (implies (and (case-split (integerp coef))
                  (oddp coef))
             (and (equal (m2-chain (times coef x) y)
                         (m2-chain x y))
                  (equal (m2-chain y (times coef x))
                         (m2-chain x y))
                  (equal (m2-chain (times coef x))
                         (m2-chain x))))
    :hints (("Goal"
             :expand ((:free (x y) (TIMES (* 2 x) y)))
             :in-theory (e/d (RW-TIMES-WHEN-COEF-IS-ODD 
                              (:DEFINITION BINARY-SUM)
                              (:DEFINITION CASE-SPLIT)
                              (:DEFINITION EVENP)
                              (:DEFINITION M2)
                              (:DEFINITION NOT)
                              (:DEFINITION ODDP)
                              (:DEFINITION SYNP)
                              (:REWRITE ACL2::|(* a (/ a) b)|)
                              (:REWRITE ACL2::|(* x (+ y z))|)
                              (:REWRITE ACL2::|(* y x)|)
                              (:REWRITE ACL2::|(mod x 2)| . 1)
                              (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                              (:REWRITE IFIX-OPENER)
                              (:REWRITE ACL2::SUM-IS-EVEN . 1))
                             (TIMES-COMM
                              (:REWRITE ACL2::|(equal x (if a b c))|)
                              (:REWRITE ACL2::|(equal (if a b c) x)|)
                              mod2-is-m2 +-IS-SUM)))))

  (defthm m2-chain-of-evenp-times
    (implies (and (evenp coef)
                  (case-split (integerp coef)))
             (and (equal (m2-chain (times coef x) y)
                         (m2-chain y))
                  (equal (m2-chain y (times coef x))
                         (m2-chain y))
                  (equal (m2-chain (times coef x))
                         0)))
    :hints (("Goal"
             
             :use ((:instance RW-TIMES-WHEN-COEF-IS-EVEN))
             :expand ((:free (x y) (TIMES (* 2 x) y)))
             :in-theory (e/d (;;rw-times-when-coef-is-even
                              (:DEFINITION BINARY-SUM)
                              (:DEFINITION EVENP)
                              )
                             (TIMES-COMM evenp floor f2
                              RW-TIMES-WHEN-COEF-IS-EVEN
                              (:REWRITE ACL2::|(equal x (if a b c))|)
                              (:REWRITE ACL2::|(equal (if a b c) x)|)
                              mod2-is-m2 +-IS-SUM)))
            )))
