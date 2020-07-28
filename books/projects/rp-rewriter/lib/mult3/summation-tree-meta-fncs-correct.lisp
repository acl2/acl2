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
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(include-book "summation-tree-meta-fncs")

(include-book "pp-flatten-meta-correct")

(include-book "sum-merge-fncs-correct")

(local
 (include-book "lemmas-2"))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (in-theory (enable ex-from-rp-loose-is-ex-from-rp)))

(local
 (in-theory (enable rp-trans trans-list)))

(create-regular-eval-lemma c 4 mult-formula-checks)
(create-regular-eval-lemma s 3 mult-formula-checks)
(create-regular-eval-lemma c-res 3 mult-formula-checks)
(create-regular-eval-lemma and-list 2 mult-formula-checks)
(create-regular-eval-lemma -- 1 mult-formula-checks)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get-max-min-val

(in-theory (disable (:DEFINITION ACL2::APPLY$-BADGEP)
                    (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                    (:DEFINITION RP-TERM-LISTP)
                    (:DEFINITION RP-TERMP)
                    (:DEFINITION EX-FROM-RP)
                    (:REWRITE NOT-INCLUDE-RP)
                    (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)))

(defthm get-max-min-val-correct-lemma1
  (implies (and (lte (ifix a) (ifix b))
                (lte (ifix x) (ifix y))
                )
           (not (gt (sum a x)
                    (sum b y))))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2
                            ifix
                            sum)
                           (rw-dir1
                            +-IS-SUM)))))

#|(defthmd rp-evlt-of-ex-from-rp-reverse
  (implies (syntaxp (atom term))
           (equal (rp-evlt term a)
                  (rp-evlt (ex-from-rp term) a))))||#

(defthmd minus-to---
  (implies (integerp term)
           (equal (- term)
                  (-- term)))
  :hints (("Goal"
           :in-theory (e/d (--) ()))))

(defthm gt-of-minues
  (and (equal (gt (-- a) (-- b))
              (gt (ifix b) (ifix a)))
       (equal (lte (-- a) (-- b))
              (lte (ifix b) (ifix a))))
  :hints (("Goal"
           :in-theory (e/d (-- rw-dir2
                               (:REWRITE ACL2::|(- (- x))|)
                               (:REWRITE ACL2::|(< (- x) (- y))|))
                           (rw-dir1)))))

(defthm get-max-min-val-correct-lemma2
  (implies (bitp term)
           (and (not (gt term 1))
                (not (gt 0 term)))))

(defthmd RP-TRANS-LST-of-consp
  (implies (consp lst)
           (equal (rp-trans-lst lst)
                  (cons (rp-trans (car lst))
                        (rp-trans-lst (cdr lst))))))

(defthm IS-RP-BITP-implies
  (implies (IS-RP-BITP term)
           (CASE-MATCH TERM (('RP ''BITP &) T)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (IS-RP-BITP) ()))))

(defthm get-max-min-val-correct-lemma3
  (and (implies (and (lte (ifix a) (ifix x)))
                (not (gt (f2 a)
                         (f2 x))))
       (implies (and (lte (ifix a) (ifix x))
                     (lte (ifix b) (ifix y)))
                (not (gt (f2 (sum a b))
                         (f2 (sum x y)))))
       (implies (and (lte (ifix a) (ifix x))
                     (lte (ifix b) (ifix y))
                     (lte (ifix c) (ifix z)))
                (not (gt (f2 (sum a b c))
                         (f2 (sum x y z))))))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2
                            f2
                            sum
                            (:REWRITE ACL2::|(* a (/ a) b)|)
                            (:REWRITE ACL2::|(* x (+ y z))|)
                            (:REWRITE ACL2::|(* y x)|)
                            (:REWRITE ACL2::|(+ 0 x)|)
                            (:REWRITE ACL2::|(+ y x)|)
                            (:REWRITE ACL2::|(/ (/ x))|)
                            (:REWRITE ACL2::|(< (+ c/d x) y)|)
                            (:REWRITE ACL2::|(equal (/ x) c)|)
                            (:REWRITE ACL2::|(floor (if a b c) x)|)
                            (:REWRITE ACL2::|(floor x 2)| . 1)
                            (:REWRITE ACL2::DEFAULT-LESS-THAN-1)
                            (:REWRITE ACL2::DEFAULT-LESS-THAN-2)
                            (:REWRITE IFIX-OPENER)
                            (:REWRITE ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<)
                            (:REWRITE ACL2::SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON)
                            (:REWRITE
                             ACL2::SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
                           (rw-dir1
                            (:DEFINITION NFIX)
                            (:DEFINITION FLOOR)
                            +-IS-SUM)))))

(defthm valid-sc-when-single-c-p
  (implies (and (SINGLE-C-P term)
                (valid-sc term a))
           (and (valid-sc (caddr term) a)
                (valid-sc (cadddr term) a)
                (valid-sc (car (cddddr term)) a)))
  :hints (("Goal"
           :expand ((VALID-SC TERM A)
                    (VALID-SC-SUBTERMS (CDDR TERM) A)
                    (VALID-SC-SUBTERMS (CDdDR TERM) A)
                    (VALID-SC-SUBTERMS (CDDDDR TERM) A)
                    (VALID-SC-SUBTERMS (CDR TERM) A))
           :in-theory (e/d (SINGLE-C-P is-rp)
                           (valid-sc valid-sc-subterms)))))

(defthm valid-sc-subterms-cons
  (implies (consp lst)
           (equal (valid-sc-subterms lst a)
                  (and (valid-sc (car lst) a)
                       (valid-sc-subterms (cdr lst) a)))))

(defthm valid-sc-when-list-instance
  (and (implies (and (valid-sc term a)
                     (case-match term
                       (('list . &) t)))
                (valid-sc-subterms (cdr term) a)))
  :hints (("Goal"
           :expand (valid-sc term a)
           :in-theory (e/d (valid-sc is-rp) ()))))

(defthm is-rp-bitp-implies-bitp-term
  (implies (and (VALID-SC TERM A)
                (IS-RP-BITP TERM))
           (and (INTEGERP (RP-EVLt (EX-FROM-RP TERM) A))
                (INTEGERP (RP-EVLt term A))
                (bitp (RP-EVLt (EX-FROM-RP TERM) A))
                (bitp (RP-EVLt term A))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC TERM A)
                    (CONTEXT-FROM-RP TERM NIL))
           :in-theory (e/d (is-rp IS-RP-BITP) (valid-sc)))))

(defthm drop-ex-from-rp-when-list
  (implies (equal (car term) 'list)
           (equal (ex-from-rp term)
                  term))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp)
                           ()))))
(std::defret-mutual
 get-max-min-val-correct
 (defret
   get-max-min-val-correct
   (implies (and valid
                 (rp-evl-meta-extract-global-facts :state state)
                 (valid-sc term a)
                 (mult-formula-checks state))
            (and (integerp (rp-evlt term a))
                 (<= (rp-evlt term a)
                     max-val)
                 (<= min-val
                     (rp-evlt term a))))
   :fn get-max-min-val)
 (defret
   get-max-min-val-lst-correct
   (implies (and valid
                 (rp-evl-meta-extract-global-facts :state state)
                 (valid-sc-subterms lst a)
                 (mult-formula-checks state))
            (and (<= (sum-list (rp-evlt-lst lst a))
                     max-val)
                 (<= min-val
                     (sum-list (rp-evlt-lst lst a)))))
   :fn get-max-min-val-lst)
 :mutual-recursion get-max-min-val
;:otf-flg t
 :hints (("Goal"
          :do-not-induct t
          :in-theory (e/d (get-max-min-val
                           RP-TRANS-LST-of-consp
                           RP-TRANS-LST
                           RP-TRANS
                           rp-evlt-of-ex-from-rp-reverse
                           minus-to---
                           get-max-min-val-lst)
                          (RP-EVLT-OF-EX-FROM-RP
                           (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                           (:TYPE-PRESCRIPTION GT)
                           (:DEFINITION FLOOR)
                           (:TYPE-PRESCRIPTION O<)
                           (:TYPE-PRESCRIPTION VALID-SC)
                           (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                           (:TYPE-PRESCRIPTION SINGLE-C-P$INLINE)
                           (:TYPE-PRESCRIPTION IS-RP-BITP)
                           (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                           (:REWRITE IS-IF-RP-TERMP)
                           (:REWRITE DEFAULT-CAR)
                           (:REWRITE DEFAULT-Cdr)
                           (:REWRITE IS-RP-PSEUDO-TERMP)
                           (:DEFINITION INCLUDE-FNC)
                           (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
                           (:REWRITE LTE-AND-GTE-IMPLIES)
                           (:REWRITE VALID-SC-EX-FROM-RP-2)
                           (:DEFINITION EVAL-AND-ALL)
                           (:DEFINITION NFIX)
                           (:REWRITE ACL2::O-P-O-INFP-CAR)
                           (:REWRITE DEFAULT-*-2)
                           (:REWRITE LT-TO-GT)
                           (:DEFINITION TRANS-LIST)
                           VALID-SC-SUBTERMS
;to-list*-sum-eval
;to-list*-sum-eval-2
                           valid-sc
                           bitp)))))

(local
 (in-theory (disable bitp)))

(defret
  is-c-bitp-traverse-correct
  (implies (and res
                (rp-evl-meta-extract-global-facts :state state)
                (valid-sc single-c a)
                (mult-formula-checks state))
           (bitp (rp-evlt single-c a)))
  :rule-classes (:rewrite)
  :fn is-c-bitp-traverse
  :hints (("Goal"
           :use ((:instance get-max-min-val-correct
                            (term single-c)))
           :in-theory (e/d (is-c-bitp-traverse
                            bitp
                            rw-dir2)
                           (get-max-min-val-correct
                            rw-dir1)))) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; compress-s-c and decompress-s-c correct

(defthm is-rp-of-s-c-list
  (and (not (is-rp (cons 'c rest)))
       (not (is-rp (cons 'c-res rest)))
       (not (is-rp (cons '-- rest)))
       (not (is-rp (cons 'list rest)))
       (not (is-rp (cons 's rest))))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm is-if-of-s-c-list
  (and (not (is-if (cons 'c rest)))
       (not (is-if (cons 'c-res rest)))
       (not (is-if (cons '-- rest)))
       (not (is-if (cons 'list rest)))
       (not (is-if (cons 's rest))))
  :hints (("Goal"
           :in-theory (e/d (is-if) ()))))

(defthmd rp-evlt-of-ex-from-rp-reverse-only-atom
  (and (implies (syntaxp (atom term))
                (EQUAL (RP-EVL (RP-TRANS TERM) A)
                       (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)))
       (implies (syntaxp (consp term))
                (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)
                       (RP-EVL (RP-TRANS term) A)))))

(defthm decompress-s-c-correct-lemma1
  (implies (valid-sc term a)
           (and (b* (((mv pp ?valid)
                      (|CASE-MATCH-('c & ''nil pp ''nil)| term)))
                  (valid-sc pp a))))
  :hints (("Goal"
           :in-theory (e/d (|CASE-MATCH-('c & ''nil pp ''nil)|)
                           ()))))

(DEFTHM
  VALID-SC-CAr-cddDDR
  (IMPLIES (AND (CONSP TERM)
                (NOT (EQUAL (CAR TERM) 'IF))
                (NOT (EQUAL (CAR TERM) 'RP))
                (NOT (EQUAL (CAR TERM) 'QUOTE))
                (CONSP (CDR TERM))
                (CONSP (CDDR TERM))
                (CONSP (CDDdR TERM))
                (CONSP (CDDddR TERM))
                (VALID-SC TERM A))
           (VALID-SC (CAR (cddDDR TERM)) A))
  :HINTS
  (("Goal" :IN-THEORY (E/D (EX-FROM-RP IS-IF IS-RP) NIL))))

(defthm equivalence-of-two-f2
  (implies (and (equal (ifix a)
                       (ifix b))
                (equal (ifix x)
                       (ifix y)))
           (equal (equal (f2 (sum a x))
                         (f2 (sum b y)))
                  t))
  :hints (("Goal"
           :in-theory (e/d (sum)
                           (+-IS-SUM)))))

(defthmd equivalence-of-two-f2-2
  (implies (and (equal (sum a b)
                       (ifix x))
                (equal (ifix c)
                       (ifix y)))
           (equal (equal (f2 (sum a b c))
                         (f2 (sum x y)))
                  t))
  :hints (("Goal"
           :in-theory (e/d (sum)
                           (+-IS-SUM)))))

(defret
  decompress-s-c-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a))
           (and (valid-sc res-term a)
                (valid-sc coughed-term a)
                (equal (sum (rp-evlt res-term a)
                            (sum-list (rp-evlt coughed-term a)))
                       (ifix (rp-evlt term a)))
                (equal (sum (rp-evlt res-term a)
                            (sum-list (rp-evlt coughed-term a))
                            other)
                       (sum (rp-evlt term a)
                            other))))
  :fn decompress-s-c
  :hints (("Goal"
           :do-not-induct t
           :induct (decompress-s-c term :limit limit)
           :in-theory (e/d (decompress-s-c
                            equivalence-of-two-f2-2
                            |CASE-MATCH-('s & pp ('list single-c))|
                            |CASE-MATCH-('c & ''nil pp ''nil)|
                            |CASE-MATCH-('c & ''nil pp ('list single-c))|
                            f2-of-times2-reverse
                            RP-TRANS-LST-of-consp
                            rp-evlt-of-ex-from-rp-reverse-only-atom
;rp-evlt-of-ex-from-rp-reverse
                            )
                           (rp-evlt-of-ex-from-rp
                            f2-of-times2
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:REWRITE VALID-SC-WHEN-SINGLE-C-P)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:REWRITE DEFAULT-CAR)

                            rp-termp
                            rp-trans-lst)))))

(defthm times2-of---
  (equal (times2 (-- x))
         (-- (times2 x)))
  :hints (("Goal"
           :in-theory (e/d (times2 -- sum)
                           (+-IS-SUM)))))

(defthm dummy-sum-lemma1
  (and (equal (equal (sum x y a)
                     (sum k l a m))
              (equal (sum x y)
                     (sum k l m)))
       (equal (equal (sum x y a)
                     (sum l a m))
              (equal (sum x y)
                     (sum l m)))

       (equal (equal (sum x y a)
                     (sum a l))
              (equal (sum x y)
                     (sum l))))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(defthm sum-of-nil
  (and (equal (sum a nil)
              (ifix a))
       (equal (sum nil a)
              (ifix a)))
  :hints (("Goal"
           :in-theory (e/d (sum)
                           (+-IS-SUM)))))

(defthm times2-plus-minus
  (and (equal (sum (times2 x) (-- x))
              (sum x))
       (equal (sum (-- x) (times2 x))
              (sum x))
       (equal (sum (times2 x) (-- x) rest)
              (sum x rest))
       (equal (sum (-- x) (times2 x) rest)
              (sum x rest))

       (equal (sum (-- (times2 x)) x)
              (sum (-- x)))
       (equal (sum x (-- (times2 x)))
              (sum (-- x)))
       (equal (sum (-- (times2 x)) x rest)
              (sum (-- x) rest))
       (equal (sum x (-- (times2 x)) rest)
              (sum (-- x) rest)))
  :hints (("Goal"
           :in-theory (e/d (times2 sum --) (+-IS-SUM)))))

(defthm valid-sc-subterms-of-nil
  (VALID-SC-SUBTERMS NIL A))

(defthmd SUM-LIST-EVAL-when-consp
  (implies (consp lst)
           (equal (sum-list-eval lst a)
                  (SUM (RP-EVLT (CAR LST) A)
                       (SUM-LIST-EVAL (CDR LST) A)))))

(defret
  light-compress-s-c$pass-pp-lst-correct
  (and
   (implies (and (valid-sc-subterms pp1-lst a)
                 (valid-sc-subterms pp2-lst a))
            (and (valid-sc-subterms res-pp1-lst a)
                 (valid-sc-subterms res-pp2-lst a)))
   (implies (and (valid-sc-subterms pp1-lst a)
                 (valid-sc-subterms pp2-lst a)
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (sum (times2 (sum-list-eval res-pp1-lst a))
                        (sum-list-eval res-pp2-lst a))
                   (sum (times2 (sum-list-eval pp1-lst a))
                        (sum-list-eval pp2-lst a)))))
  :fn light-compress-s-c$pass-pp-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x y)
                           (valid-sc (cons x y) a)))
           :induct (light-compress-s-c$pass-pp-lst pp1-lst pp2-lst)
           :in-theory (e/d (light-compress-s-c$pass-pp-lst
                            SUM-LIST-EVAL-when-consp
                            abs-term)
                           (rp-trans-lst
                            (:DEFINITION SUM-LIST-EVAL)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:DEFINITION VALID-SC-SUBTERMS)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:TYPE-PRESCRIPTION --)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:TYPE-PRESCRIPTION SUM-LIST-EVAL)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE VALID-SC-WHEN-SINGLE-C-P)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_IFIX_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_BIT-OF_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            (:DEFINITION RP-EQUAL)
                            ;;(:DEFINITION SUM-LIST-EVAL)
                            (:DEFINITION VALID-SC)
                            (:TYPE-PRESCRIPTION TIMES2)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)

;(:DEFINITION SUM-LIST-EVAL)
                            rp-trans
                            eval-and-all
                            is-falist)))))

(defthm list-to-lst-correct
  (and (equal (valid-sc-subterms (list-to-lst term) a)
              (valid-sc term a))
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (mult-formula-checks state))
                (equal (sum-list-eval (list-to-lst term) a)
                       (sum-list (rp-evlt term a)))))
  :hints (("Goal"
           :in-theory (e/d (list-to-lst
                            is-rp)
                           ()))))

(defret
  light-compress-s-c$pass-pp-correct
  (and
   (implies (and (valid-sc pp1 a)
                 (valid-sc pp2 a))
            (and (valid-sc res-pp1 a)
                 (valid-sc res-pp2 a)))
   (implies (and (valid-sc pp1 a)
                 (valid-sc pp2 a)
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (sum (times2 (sum-list (rp-evlt res-pp1 a)))
                        (sum-list (rp-evlt res-pp2 a)))
                   (sum (times2 (sum-list (rp-evlt pp1 a)))
                        (sum-list (rp-evlt pp2 a))))))
  :fn light-compress-s-c$pass-pp
  :hints (("Goal"
           :in-theory (e/d (light-compress-s-c$pass-pp) ()))))

(defret
  light-compress-s-c$pass-pp-correct-2
  (and
   (implies (and (valid-sc pp1 a)
                 (valid-sc pp2 a))
            (and (valid-sc res-pp1 a)
                 (valid-sc res-pp2 a)))
   (implies (and (valid-sc pp1 a)
                 (valid-sc pp2 a)
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (sum (times2 (sum-list (rp-evlt res-pp1 a)))
                        (sum-list (rp-evlt res-pp2 a))
                        other)
                   (sum (times2 (sum-list (rp-evlt pp1 a)))
                        (sum-list (rp-evlt pp2 a))
                        other))))
  :fn light-compress-s-c$pass-pp
  :hints (("Goal"
           :in-theory (e/d () ()))))

(defthm reduce-same-args-of-m2
  (and (equal (equal (m2 (sum a x))
                     (m2 (sum b x)))
              (equal (m2 (sum a))
                     (m2 (sum b))))
       (equal (equal (m2 (sum x a))
                     (m2 (sum x b)))
              (equal (m2 (sum a))
                     (m2 (sum b)))))
  :hints (("Goal"
           :in-theory (e/d (sum
                            m2
                            (:REWRITE ACL2::EQUAL-OF-PREDICATES-REWRITE)
                            (:REWRITE ACL2::|(* x (+ y z))|)
                            (:REWRITE ACL2::|(equal (if a b c) x)|)
                            (:REWRITE ACL2::|(mod x 2)| . 1)
                            (:REWRITE ACL2::SUM-IS-EVEN . 1))
                           (+-IS-SUM

                            MOD2-IS-M2)))))

(defthm reduce-same-args-of-m2-2
  (and (equal (equal (m2 (sum a m x))
                     (m2 (sum b n x)))
              (equal (m2 (sum a m))
                     (m2 (sum b n))))
       (equal (equal (m2 (sum a m x p))
                     (m2 (sum b n x q)))
              (equal (m2 (sum a m p))
                     (m2 (sum b n q)))))
  :hints (("Goal"
           :use ((:instance reduce-same-args-of-m2
                            (a (sum a m))
                            (b (sum b n)))
                 (:instance reduce-same-args-of-m2
                            (a (sum a m p))
                            (b (sum b n q))))
           :in-theory (e/d () (reduce-same-args-of-m2)))))

(defthm abs-term-of---
  (equal (abs-term `(-- ,x))
         (mv x t))
  :hints (("Goal"
           :in-theory (e/d (abs-term) ()))))

(defret
  ligth-compress-s-c$fix-pp-lst$for-s-correct
  (and
   (implies (valid-sc-subterms pp1-lst a)
            (valid-sc-subterms res-pp1-lst a))
   (implies (and (valid-sc-subterms pp1-lst a)
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (and (equal (m2 (sum (sum-list-eval res-pp1-lst a) rest))
                        (m2 (sum (sum-list-eval pp1-lst a) rest)))
                 (equal (m2 (sum-list-eval res-pp1-lst a))
                        (m2 (sum (sum-list-eval pp1-lst a))))
                 #|(equal (sum-list-eval (abs-lst res-pp1-lst) a)
                 (sum (sum-list-eval (abs-lst pp1-lst) a)))||#)))
  :fn ligth-compress-s-c$fix-pp-lst$for-s
  :hints (("Goal"
           :do-not-induct t
           :induct (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst pp2-lst)
           :in-theory (e/d (ligth-compress-s-c$fix-pp-lst$for-s) ()))))

(defret
  light-compress-s-c$fix-pp$for-s-correct
  (and
   (implies (valid-sc pp1 a)
            (valid-sc res-pp1 a))
   (implies (and (valid-sc pp1 a)
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (and (equal (m2 (sum (sum-list (rp-evlt res-pp1 a)) rest))
                        (m2 (sum (sum-list (rp-evlt pp1 a)) rest)))
                 (equal (m2 (sum-list (rp-evlt res-pp1 a)))
                        (m2 (sum-list (rp-evlt pp1 a))))
                 #|(equal (sum-list-eval (abs-lst res-pp1-lst) a)
                 (sum (sum-list-eval (abs-lst pp1-lst) a)))||#)))
  :fn light-compress-s-c$fix-pp$for-s
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (light-compress-s-c$fix-pp$for-s) ()))))

(defthmd rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
  (AND (IMPLIES (SYNTAXP (or (ATOM TERM)
                             (equal (car term) 'car)))
                (EQUAL (RP-EVL (RP-TRANS TERM) A)
                       (RP-EVL (RP-TRANS (EX-FROM-RP TERM))
                               A)))
       (IMPLIES (SYNTAXP (not (or (ATOM TERM)
                                  (equal (car term) 'car))))
                (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)
                       (RP-EVL (RP-TRANS TERM) A)))))

(defret light-compress-s-c-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c-arg a))
           (and (valid-sc pp-res a)
                (valid-sc c-arg-res a)
                (equal (sum (sum-list (rp-evlt pp-res a))
                            (sum-list (rp-evlt c-arg-res a)))
                       (sum (sum-list (rp-evlt pp a))
                            (sum-list (rp-evlt c-arg a))))))
  :fn light-compress-s-c-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (light-compress-s-c-aux pp c-arg)
           :expand ((:free (x) (single-c-p x))
                    (:free (rest) (VALID-SC (cons 'c rest) a))
                    (:free (rest) (VALID-SC (cons 'list rest) a)))
           :in-theory (e/d (light-compress-s-c-aux
;RP-TRANS-LST-of-consp
                            f2-of-times2-reverse
;single-c-p
                            rp-evlt-of-ex-from-rp-reverse-only-atom)
                           (rp-evlt-of-ex-from-rp
                            ex-from-rp
                            f2-of-times2
                            valid-sc)))))

(defret light-compress-s-c-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc term a)))
           (and (equal (rp-evlt res-term a)
                       (rp-evlt term a))
                (valid-sc res-term a)))
  :fn light-COMPRESS-S-C
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (rest) (VALID-SC (cons 'c rest) a)))
           :in-theory (e/d (light-compress-s-C
                            rp-trans-lst-of-consp
                            rp-evlt-of-ex-from-rp-reverse-only-atom)
                           (ex-from-rp
                            rp-evlt-of-ex-from-rp
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-pattern2-reduce and create-c-instance lemmas

(defthm minus-of-sum
  (equal (-- (sum a b))
         (sum (-- a) (-- b)))
  :hints (("Goal"
           :in-theory (e/d (sum --)
                           (+-IS-SUM)))))

(defthm minus-of-minus
  (equal (-- (-- a))
         (ifix a))
  :hints (("Goal"
           :in-theory (e/d (--) ()))))

(defret negate-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (and (valid-sc-subterms negated-lst a)
                (equal (sum-list-eval negated-lst a)
                       (-- (sum-list-eval lst a)))))
  :fn negate-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (negate-lst-aux lst)
           :in-theory (e/d (negate-lst-aux
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-evlt-of-ex-from-rp)))))

(defret negate-list-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc term a)))
           (and (valid-sc res a)
                (equal (sum-list (rp-evlt res a))
                       (if enabled
                           (-- (sum-list (rp-evlt term a)))
                         (sum-list (rp-evlt term a))))))
  :fn negate-list-instance
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (negate-list-instance
                            NEGATE-LST)
                           ()))))

(defthmd f2-of-minus-reverse
  (equal (sum (-- a) (f2 (sum a b)))
         (f2 (sum (-- a) b))))

(defthm c-pattern2-reduce-correct-lemma
  (b* (((mv max min valid)
        (get-max-min-val term)))
    (implies (and valid
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc term a)
                  (equal max 0)
                  (equal min -1))
             (equal (f2 (rp-evlt term a))
                    (rp-evlt term a))))
  :hints (("Goal"
           :use ((:instance get-max-min-val-correct))
           :cases ((= (RP-EVLT TERM A) 0)
                   (= (RP-EVLT TERM A) -1))
           :in-theory (e/d (rw-dir2)
                           (get-max-min-val-correct
                            rw-dir1)))))

(defret c-pattern2-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c a))
           (and (valid-sc s-res a)
                (valid-sc pp-res a)
                (valid-sc c-res a)
                (equal (f2 (sum (sum-list (rp-evlt s-res a))
                                (sum-list (rp-evlt pp-res a))
                                (sum-list (rp-evlt c-res a))))
                       (f2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))))
  :fn c-pattern2-reduce
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance decompress-s-c-correct
                            (term (CADR
                                   (CAR (CDDDDR (LIGHT-COMPRESS-S-C (LIST 'C
                                                                          ''0
                                                                          ''NIL
                                                                          (NEGATE-LIST-INSTANCE PP T)
                                                                          C))))))
                            (limit 1073741824)
                            (other (SUM-LIST (RP-EVLT PP A))))
                 (:instance pp-sum-merge-correct
                            (term1 pp)
                            (term2 (MV-NTH
                                    1
                                    (DECOMPRESS-S-C
                                     (CADR
                                      (CAR (CDDDDR (LIGHT-COMPRESS-S-C (LIST 'C
                                                                             ''0
                                                                             ''NIL
                                                                             (NEGATE-LIST-INSTANCE PP T)
                                                                             C)))))
                                     :LIMIT 1073741824))))
                 (:instance light-compress-s-c-correct
                            (term (LIST 'C
                                        ''0
                                        ''NIL
                                        (NEGATE-LIST-INSTANCE PP T)
                                        C)))
                 )
           :expand ((VALID-SC ''NIL A)
                    (:free (x) (valid-sc (cons 'c x) a)))
           ;;:case-split-limitations (10 1)
           :do-not '()
           :in-theory (e/d (c-pattern2-reduce
                            rp-trans-lst-of-consp
                            ;;f2-of-minus-reverse
                            )
                           (ex-from-rp
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:REWRITE GET-MAX-MIN-VAL-CORRECT)
                            (:TYPE-PRESCRIPTION --)
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS)
                            is-rp
;is-falist
                            ;;(:DEFINITION VALID-SC)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE DEFAULT-CDR)
;(:DEFINITION RP-TRANS)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE DEFAULT-CAR)
                            (:TYPE-PRESCRIPTION O<)
                            ;;f2-of-minus
                            pp-sum-merge-correct
                            decompress-s-c-correct
                            light-compress-s-c-correct
                            )))))

(defthm rp-evlt-of-quoted
  (equal (rp-evlt (list 'quote x) a)
         x))

(defret create-c-instance-is-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c a))
           (and (equal (rp-evlt c-res a)
                       (f2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))
                (valid-sc c-res a)))
  :fn create-c-instance
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-pattern2-reduce-correct))
           :expand ((:free (x) (valid-sc (cons 'c x) a))
                    (:free (x) (valid-sc (cons 'quote x) a)))
           :in-theory (e/d (create-c-instance
                            rp-trans-lst-of-consp)
                           (c-pattern2-reduce-correct
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:TYPE-PRESCRIPTION F2)
                            (:DEFINITION IS-SYNP$INLINE)
                            TO-LIST*-SUM-EVAL
                            (:TYPE-PRESCRIPTION TRANS-LIST)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS)
;RP-TRANS
                            INCLUDE-FNC
                            RP-TRANS-LST
                            VALID-SC
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-s-instance and s-pattern3-reduce lemmas

(defthmd s-pattern3-reduce-correct-lemma
  (implies (and (<= val 0)
                (>= val -1))
           (equal (m2 val) (-- val)))
  :hints (("Goal"
           :cases ((= val 0)
                   (integerp val)
                   (= val -1))
           :in-theory (e/d (rw-dir2
                            (:REWRITE ACL2::|(- (- x))|)
                            (:REWRITE ACL2::|(equal (if a b c) x)|)
                            (:REWRITE ACL2::|(equal c (- x))|)
                            (:REWRITE ACL2::|(mod x 2)| . 1)
                            (:REWRITE ACL2::DEFAULT-LESS-THAN-1)
                            (:REWRITE ACL2::DEFAULT-LESS-THAN-2)
                            (:REWRITE IFIX-OPENER)
                            m2
                            ifix
                            --)
                           (rw-dir1
                            mod2-is-m2)))))

(defret s-pattern3-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and (equal (rp-evlt reduced a)
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))))
  :fn s-pattern3-reduce
  :hints (("Goal"
           :do-not-induct t
           :expand (#|(LIGHT-COMPRESS-S-C (LIST 'S ''0 PP C))||#
                    (EX-FROM-RP (LIST 'S ''0 ''NIL C))
                    (VALID-SC (LIST 'S ''0 PP C) A))
           :use ((:instance
                  light-compress-s-c-correct
                  (term (LIST 'S ''0 PP C)))
                 (:instance
                  decompress-s-c-correct
                  (term (CADR (CADDDR (LIGHT-COMPRESS-S-C (LIST 'S ''0 PP
                                                                C)))))
                  (limit 1073741824))
                 (:instance get-max-min-val-correct
                            (term (CADR (CADDDR (LIGHT-COMPRESS-S-C (LIST 'S ''0 PP C))))))
                 (:instance
                  s-pattern3-reduce-correct-lemma
                  (val (RP-EVLT (CADR (CADDDR (LIGHT-COMPRESS-S-C (LIST 'S ''0 PP C))))
                                A))))
           :in-theory (e/d (s-pattern3-reduce
                            rp-trans-lst-of-consp
                            c-res
                            is-rp)
                           (light-compress-s-c-correct
                            s-pattern3-reduce-correct-lemma
                            get-max-min-val-correct
                            (:REWRITE DEFAULT-CDR)
                            (:TYPE-PRESCRIPTION O<)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION TRANS-LIST)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:TYPE-PRESCRIPTION RP-TRANS-LST)
                            (:TYPE-PRESCRIPTION --)
                            (:TYPE-PRESCRIPTION M2)
                            (:TYPE-PRESCRIPTION LTE)
                            (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)

                            ;;(:DEFINITION RP-TRANS)

                            valid-sc
                            (:TYPE-PRESCRIPTION LIGHT-COMPRESS-S-C)
                            decompress-s-c-correct
                            ex-from-rp)))))

(local
 (defthm is-rp-of-bitp
   (is-rp `(rp 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(defret s-pattern3-reduce-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (valid-sc reduced a))
  :fn s-pattern3-reduce
  :hints (("Goal"
           :use ((:instance s-pattern3-reduce-correct))
           :expand ((:free (x) (valid-sc (cons 'c-res x) a))
                    (:free (x) (valid-sc (cons 'list x) a))
                    (:free (x) (valid-sc (cons '-- x) a)))
           :in-theory (e/d (s-pattern3-reduce
                            valid-sc-single-step
                            is-rp
                            )
                           (s-pattern3-reduce-correct
                            valid-sc
                            )))))
(defthmd m2-of-bitp
  (implies (bitp x)
           (equal (m2 x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defret create-s-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a))
           (and
            (equal (rp-evlt res a)
                   (m2 (sum (sum-list (rp-evlt pp a))
                            (sum-list (rp-evlt c a)))))
            (valid-sc res a)))
  :fn create-s-instance
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (create-s-instance
                            m2-of-bitp
                            valid-sc-single-step
                            rp-trans-lst-of-consp
                            is-rp)
                           (
                            INCLUDE-FNC)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; single-c-try-merge-params

(defret swap-c-lsts-correct
  (and
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (sum (sum-list-eval res1 a)
                        (sum-list-eval res2 a))
                   (sum (sum-list-eval c1-lst a)
                        (sum-list-eval c2-lst a))))
   (implies (and (valid-sc-subterms c1-lst a)
                 (valid-sc-subterms c2-lst a))
            (and (valid-sc-subterms res1 a)
                 (valid-sc-subterms res2 a))))
  :fn swap-c-lsts
  :hints (("Goal"
           :in-theory (e/d (swap-c-lsts)
                           (valid-sc
                            valid-sc-subterms)))))

(defthm m2-of-rp-evlt-ex-from-rp/--
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2 (sum (RP-EVLt (EX-FROM-RP/-- e) A)
                                other))
                       (m2 (sum (RP-EVLT e A)
                                other)))
                (equal (m2 (sum (RP-EVL (EX-FROM-RP/-- e) A)
                                other))
                       (m2 (sum (RP-EVL e A)
                                other)))))
  :hints (("Goal"
           :induct (EX-FROM-RP/-- e)
           :do-not-induct t
           :in-theory (e/d (EX-FROM-RP/-- is-rp --.p)
                           (EX-FROM-RP-LEMMA1)))))

(defthm light-s-of-s-fix-lst-correct-lemma1
  (implies (and (EQUAL (EX-FROM-RP/-- e) ''NIL)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (EQUAL (M2 (RP-EVLT e A)) 0))
  :hints (("Goal"
           :induct (EX-FROM-RP/-- e)
           :do-not-induct t
           :in-theory (e/d (EX-FROM-RP/-- --.p is-rp) (EX-FROM-RP-LEMMA1)))))

(defthm m2-sums-equivalence
  (implies (and (equal (m2 x) (m2 y))
                (equal (m2 a) (m2 b)))
           (equal (m2 (sum x a))
                  (m2 (sum y b))))
  :hints (("Goal"
           :in-theory (e/d (m2 sum
                               (:REWRITE ACL2::|(* x (+ y z))|)
                               (:REWRITE ACL2::|(+ y x)|)
                               (:REWRITE ACL2::|(equal (if a b c) x)|)
                               (:REWRITE ACL2::|(mod x 2)| . 1)
                               (:REWRITE IFIX-OPENER)
                               (:REWRITE ACL2::SUM-IS-EVEN . 2))
                           (mod2-is-m2
                            +-IS-SUM)))))

(defthm m2-sums-dummy-lemma-1
  (implies (and (equal (m2 (sum x y)) (m2 z))
                (equal (m2 (sum k l)) (m2 (sum m n))))
           (equal (equal (m2 (sum x y k l))
                         (m2 (sum m z n)))
                  t))
  :hints (("Goal"
           :use ((:instance m2-sums-equivalence
                            (x (sum x y))
                            (y z)
                            (a (sum k l))
                            (b (sum m n))))
           :in-theory (e/d ( )
                           ()))))

(defret light-s-of-s-fix-lst-correct
  (and
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (m2 (sum (sum-list-eval pp-res-lst a)
                            (sum-list-eval c-res-lst a)))
                   (m2 (sum (sum-list-eval s-lst a)
                            (sum-list-eval c-lst a))))))
  :fn light-s-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (light-s-of-s-fix-lst s-lst c-lst)
           :expand ((:free (x) (nth 3 x))
                    (:free (x) (nth 2 x))
                    (:free (x) (nth 1 x))
                    (:free (x) (nth 0 x)))
           :in-theory (e/d (light-s-of-s-fix-lst
                            is-rp)
                           (eval-and-all
                            rp-trans
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            not-include-rp-means-valid-sc
                            not-include-rp-means-valid-sc-lst)))
          ("Subgoal *1/2"
           :use ((:instance m2-of-rp-evlt-ex-from-rp/--
                            (e (CAR S-LST))
                            (other (sum (SUM-LIST-EVAL (MV-NTH 0
                                                               (LIGHT-S-OF-S-FIX-LST (CDR S-LST)
                                                                                     C-LST))
                                                       A)
                                        (SUM-LIST-EVAL (MV-NTH 1
                                                               (LIGHT-S-OF-S-FIX-LST (CDR S-LST)
                                                                                     C-LST))
                                                       A))))))))

(defthm valid-sc-ex-from-rp/--
  (implies (valid-sc term a)
           (valid-sc (EX-FROM-RP/-- term) a))
  :hints (("Goal"
           :induct (EX-FROM-RP/-- term)
           :do-not-induct t
           :in-theory (e/d (EX-FROM-RP/--
                            valid-sc
                            valid-sc-single-step
                            )
                           ()))))

(defret light-s-of-s-fix-lst-correct-valid-sc-subterms
  (implies (and (valid-sc-subterms s-lst a)
                (valid-sc-subterms c-lst a)) ;
           (and (valid-sc-subterms pp-res-lst a) ;
                (valid-sc-subterms c-res-lst a)))
  :fn light-s-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (light-s-of-s-fix-lst s-lst c-lst)
           :expand ((:free (x) (nth 3 x))
                    (:free (x) (nth 2 x))
                    (:free (x) (nth 1 x))
                    (:free (x) (nth 0 x)))
           :in-theory (e/d (light-s-of-s-fix-lst
                            is-rp)
                           (eval-and-all
                            rp-trans
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            not-include-rp-means-valid-sc
                            not-include-rp-means-valid-sc-lst)))))

(defthm m2-sums-dummy-lemma-2
  (implies (and (equal (m2 (sum x y)) (m2 (sum m n))))
           (equal (equal (m2 (sum x y a))
                         (m2 (sum m a n)))
                  t))
  :hints (("Goal"
           :in-theory (e/d ( )
                           (m2-sums-equivalence)))))

(defthm light-s-of-s-fix-correct-lemma
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (NOT (LIST-TO-LST S))
                (mult-formula-checks state))
           (equal (SUM-LIST (RP-EVLT S A))
                  0))
  :hints (("Goal"
           :in-theory (e/d (LIST-TO-LST) ()))))

(defret light-s-of-s-fix-correct
  (and
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (m2 (sum (sum-list (rp-evlt pp-res a))
                            (sum-list-eval c-res-lst a)))
                   (m2 (sum (sum-list (rp-evlt s a))
                            (sum-list (rp-evlt pp a))
                            (sum-list-eval c-lst a)))))
   (implies (and (valid-sc s a)
                 (valid-sc pp a)
                 (valid-sc-subterms c-lst a))
            (and (valid-sc pp-res a)
                 (valid-sc-subterms c-res-lst a))))
  :fn light-s-of-s-fix
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance light-s-of-s-fix-lst-correct
                            (s-lst (LIST-TO-LST S))))
           :in-theory (e/d (light-s-of-s-fix)
                           (light-s-of-s-fix-lst-correct)))))


#|(local
 (use-arith-5 t))||#

#|(defthm dummy-f2-lemma1
  (implies (equal (f2 a) (sum (f2 b) c))
           (equal (f2 (sum a x)) (sum (f2 (sum b x)) c)))
  :hints (("Goal"
           :in-theory (e/d (f2 rw-dir2 sum) (+-IS-SUM rw-dir1)))))||#

(defun f2x2 (args)
  (sum (-- (m2 args)) args))

#|(defthm dummy-clear-equals-from-sum-lemma
  (equal (equal (sum x1 x2 x3 x4 x5 x6 a) (sum y1 y2 y3 y4 y5 y6 a y7))
         (equal (sum x1 x2 x3 x4 x5 x6) (sum y1 y2 y3 y4 y5 y6 y7))))||#

;; (defthm dummy-sum-lemma
;;   (implies (equal (sum (m2 a) (-- (m2 b)) others) 0)
;;            (equal (sum (m2 (sum a) (-- (m2 b)) others) 0)

(defthmd single-c-try-merge-params-correct-dummy-lemma
  (implies (and (equal (sum a x y b) 0)
                (equal (sum x y) (sum x2 y2)))
           (equal (sum x2 a y2 b) 0)))

(defthmd move-sum-over-to-the-same-side
  (and (equal (equal (sum a b) (sum c))
              (equal (sum a b (-- c)) 0))
       (equal (equal (sum a b) (sum c d))
              (equal (sum a b (-- c) (-- d)) 0)))
  :hints (("Goal"
           :in-theory (e/d (sum ifix --) (+-IS-SUM)))))

(defthmd single-c-try-merge-params-correct-dummy-lemma-2
  (implies (equal (m2 (sum a b)) (m2 (sum x y z)))
           (equal (equal (sum (m2 (sum a b w))
                              (-- (m2 (sum x y z w))))
                         0)
                  t))
  :hints (("Goal"
           :use ((:instance m2-of-m2
                            (x (sum a b))
                            (y w)))
           :in-theory (e/d (-- (:REWRITE ACL2::|(- (- x))|)
                               (:REWRITE ACL2::|(integerp (- x))|)
                               (:REWRITE IFIX-OF-M2)
                               (:REWRITE IFIX-OPENER)
                               (:REWRITE INTEGERP-M2-F2-D2)
                               (:REWRITE S-FIX-PP-ARGS-AUX-CORRECT-DUMMY-LEMMA1)
                               (:REWRITE SUM-ASSOC)
                               (:REWRITE SUM-COMM-1)
                               (:REWRITE SUM-COMM-2)
                               (:REWRITE SUM-OF-NEGATED-ELEMENTS))
                           (+-IS-SUM m2-of-m2)))))

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

(defthmd m2-of-evenp
  (implies (and (evenp a))
           (equal (m2 (sum a b))
                  (m2 b)))
  :hints (("Goal"
           :cases ((integerp a))
           :in-theory (e/d (m2
                            ifix
                            (:REWRITE ACL2::|(mod x 2)| . 1)
                            --
                            sum
                            )
                           (mod2-is-m2 +-IS-SUM)))))

(defthmd sum-of-not-integerp
  (implies (not (integerp a))
           (equal (sum a x1)
                  (ifix x1)))
  :hints (("Goal"
           :in-theory (e/d (ifix sum)
                           (+-IS-SUM)))))

(defthmd m2-of-sum-1-other
  (equal (m2 (sum 1 x1))
         (sum 1 (-- (m2 x1))))
  :hints (("Goal"
           :in-theory (e/d (m2
                            --
                            sum
                            (:REWRITE ACL2::|(* a (/ a) b)|)
                            (:REWRITE ACL2::|(* x (+ y z))|)
                            (:REWRITE ACL2::|(+ x (if a b c))|)
                            (:REWRITE ACL2::|(- (if a b c))|)
                            (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                            (:REWRITE IFIX-OPENER)
                            (:REWRITE ACL2::|(mod x 2)| . 1))
                           (+-IS-SUM mod2-is-m2)))))

(defthmd cancel-m2-args
  (and (equal (sum (m2 (sum a x1))
                   (-- (m2 (sum a x2)))
                   x3)
              (if (or (evenp a)
                      (not (integerp a)))
                  (sum (m2 x1)
                       (-- (m2 x2))
                       x3)
                (sum (-- (m2 x1))
                     (m2 x2)
                     x3))))
  :hints (("Goal"
           :cases ((evenp a))
           :in-theory (e/d (m2-of-oddp
                            m2-of-sum-1-other
                            sum-of-not-integerp
                            m2-of-evenp)
                           (+-IS-SUM
                            mod2-is-m2
                            evenp)))))

#|(defthmd single-c-try-merge-params-correct-lemma-3
  (equal (sum (m2 (sum a b x1))
              (-- (m2 (sum x2 x3 a b x4)))
              x5)

         (sum (m2 x1)
              (-- (m2 (sum x2 x3 x4)))
              x5)))||#



(defret single-c-try-merge-params-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (VALID-SC S-ARG A)
                (VALID-SC pp-arg A)
                (valid-sc-subterms c-arg-lst A)
                (valid-sc-subterms s-lst A)
                success)
           (equal (f2x2 (sum (sum-list (rp-evlt s-arg a))
                             (sum-list (rp-evlt pp-arg a))
                             (sum-list-eval c-arg-lst a)
                             x))
                  (sum (f2x2 (sum (rp-evlt cur-s a) x))
                       (f2x2 (sum (sum-list (rp-evlt s-arg a))
                                  (sum-list (rp-evlt pp-arg a))
                                  (sum-list-eval c-arg-lst a))))))
  :fn single-c-try-merge-params-aux
  :hints (("Goal"
           :use ((:instance light-s-of-s-fix-correct
                            (s s-arg)
                            (pp pp-arg)
                            (c-lst c-arg-lst)))
           :do-not-induct t
           :in-theory (e/d (single-c-try-merge-params-aux
                            single-c-try-merge-params-correct-dummy-lemma
                            move-sum-over-to-the-same-side
                            single-c-try-merge-params-correct-dummy-lemma-2
;single-c-try-merge-params-correct-lemma-3
                            move-sum-over-to-the-same-side
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-termp
                            valid-sc
                            eval-and-all
                            DUMMY-SUM-CANCEL-LEMMA1
                            rp-evlt-of-ex-from-rp

                            SUM-OF-NEGATED-ELEMENTS
                            light-s-of-s-fix-correct
                            include-fnc
                            evenp)))))

(define single-c-try-merge-params$for-proof  (s-lst other-s-lst c-hash-code s-arg pp-arg
                                                    c-arg-lst)
  :returns (mv (updated-s-lst)
               (success))
  :measure (acl2-count s-lst)
  :verify-guards nil
  (b* (((when (atom s-lst))
        (mv other-s-lst nil))
       ((when (single-c-try-merge-params-aux (car s-lst) c-hash-code
                                             s-arg pp-arg c-arg-lst))
        (mv (append other-s-lst (cdr s-lst)) t))
       ((mv rest-s-lst success)
        (single-c-try-merge-params$for-proof (cdr s-lst)
                                             (append other-s-lst (list (car s-lst)))
                                             c-hash-code s-arg pp-arg
                                             c-arg-lst))
       ((when success)
        (mv rest-s-lst t)))
    (mv (append other-s-lst s-lst) nil)))

(defthm single-c-try-merge-params$for-proof-lemma
  (implies (and (true-listp s-lst)
                (true-listp other-s-lst))
           (b* (((mv lst1 success1)
                 (single-c-try-merge-params$for-proof s-lst other-s-lst c-hash-code s-arg pp-arg
                                                      c-arg-lst))
                ((mv lst2 success2)
                 (single-c-try-merge-params s-lst c-hash-code s-arg pp-arg
                                            c-arg-lst)))
             (and (equal success1 success2)
                  (equal lst1 (append other-s-lst lst2)))))
  :hints (("Goal"
           :induct (single-c-try-merge-params$for-proof s-lst other-s-lst c-hash-code s-arg pp-arg
                                                        c-arg-lst)
           :do-not-induct t
           :in-theory (e/d (single-c-try-merge-params$for-proof
                            single-c-try-merge-params)
                           ()))))

(defthm sum-list-eval-of-append
  (equal (sum-list-eval (append x y) a)
         (sum (sum-list-eval x a)
              (sum-list-eval y a)))
  :hints (("Goal"
           :in-theory (e/d (sum-list-eval) ()))))






(defret single-c-try-merge-params$for-proofs-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (VALID-SC S-ARG A)
                (VALID-SC pp-arg A)
                (valid-sc-subterms c-arg-lst A)
                (valid-sc-subterms s-lst A)
                (true-listp s-lst)
                success)
           (equal (f2x2 (sum (sum-list-eval updated-s-lst a)
                             (sum-list (rp-evlt s-arg a))
                             (sum-list (rp-evlt pp-arg a))
                             (sum-list-eval c-arg-lst a)
                             x))
                  (sum (f2x2 (sum (sum-list-eval s-lst a)
                                  (sum-list-eval other-s-lst a)
                                  x))
                       (f2x2 (sum (sum-list (rp-evlt s-arg a))
                                  (sum-list (rp-evlt pp-arg a))
                                  (sum-list-eval c-arg-lst a))))))
  :fn single-c-try-merge-params$for-proof
  :hints (("Goal"
           :do-not-induct t
           :induct (single-c-try-merge-params$for-proof s-lst other-s-lst c-hash-code s-arg pp-arg c-arg-lst)
           :in-theory (e/d (single-c-try-merge-params
                            single-c-try-merge-params$for-proof
                            single-c-try-merge-params-correct-dummy-lemma
                            single-c-try-merge-params-correct-dummy-lemma-2
                            move-sum-over-to-the-same-side
                            sum-of-not-integerp
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-termp
                            single-c-try-merge-params-aux-correct
                            valid-sc
                            eval-and-all
                            DUMMY-SUM-CANCEL-LEMMA1
                            rp-evlt-of-ex-from-rp
                            single-c-try-merge-params$for-proof-lemma
                            SUM-OF-NEGATED-ELEMENTS
                            light-s-of-s-fix-correct
                            include-fnc
                            evenp)))
          ("Subgoal *1/2"
           :use ((:instance single-c-try-merge-params-aux-correct
                            (x (sum (SUM-LIST-EVAL OTHER-S-LST A)
                                    (SUM-LIST-EVAL (CDR S-LST) A)
                                    X))
                            (cur-s (car s-lst)))))))

(defret single-c-try-merge-params-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (VALID-SC S-ARG A)
                (VALID-SC pp-arg A)
                (valid-sc-subterms c-arg-lst A)
                (valid-sc-subterms s-lst A)
                (true-listp s-lst)
                success)
           (equal (f2x2 (sum (sum-list-eval updated-s-lst a)
                             (sum-list (rp-evlt s-arg a))
                             (sum-list (rp-evlt pp-arg a))
                             (sum-list-eval c-arg-lst a)
                             x))
                  (sum (f2x2 (sum (sum-list-eval s-lst a)
                                  x))
                       (f2x2 (sum (sum-list (rp-evlt s-arg a))
                                  (sum-list (rp-evlt pp-arg a))
                                  (sum-list-eval c-arg-lst a))))))
  :fn single-c-try-merge-params
  :hints (("Goal"
           :use ((:instance single-c-try-merge-params$for-proofs-correct
                            (other-s-lst nil)))
           :in-theory (e/d ()
                           (single-c-try-merge-params$for-proofs-correct
                            (:DEFINITION TRUE-LISTP)
                            (:REWRITE VALID-SC-SUBTERMS-CONS)
                            valid-sc))
           :do-not-induct t)))

(defret single-c-try-merge-params-correct-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (VALID-SC S-ARG A)
                (VALID-SC pp-arg A)
                (valid-sc-subterms c-arg-lst A)
                (valid-sc-subterms s-lst A)
                (true-listp s-lst)
                success)
           (equal (f2 (sum (sum-list-eval updated-s-lst a)
                           (sum-list (rp-evlt s-arg a))
                           (sum-list (rp-evlt pp-arg a))
                           (sum-list-eval c-arg-lst a)
                           x))
                  (sum (f2 (sum (sum-list-eval s-lst a)
                                x))
                       (f2 (sum (sum-list (rp-evlt s-arg a))
                                (sum-list (rp-evlt pp-arg a))
                                (sum-list-eval c-arg-lst a))))))
  :fn single-c-try-merge-params
  :hints (("Goal"
           :use ((:instance single-c-try-merge-params-correct))
           :in-theory (e/d (sum-of-f2s
                            f2-to-d2)
                           (d2-to-f2
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:DEFINITION VALID-SC)
                            (:REWRITE MINUS-OF-SUM)
                            eval-and-all
                            (:REWRITE D2-OF-MINUS))))))



(defret single-c-try-merge-params-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst A))
           (valid-sc-subterms updated-s-lst A))
  :fn single-c-try-merge-params
  :hints (("Goal"
           :do-not-induct t
           :induct (single-c-try-merge-params s-lst c-hash-code s-arg pp-arg c-arg-lst)
           :in-theory (e/d (single-c-try-merge-params)
                           ()))))



:i-am-here
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-sum-merge



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-s-instance, d-to-c and c/d-cough lemmas

(defthm create-c-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt (create-c-instance s pp c/d) a)
                  (c (rp-evlt s a)
                     (rp-evlt pp a)
                     (rp-evlt c/d a))))
  :hints (("Goal"
           :in-theory (e/d (create-c-instance)
                           (rp-trans)))))

(defthm create-c-instance-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (rp-evlt-equiv (create-c-instance s pp c/d)
                          `(c ,s ,pp ,c/d)))
  :hints (("Goal"
           :in-theory (e/d ()
                           (rp-trans)))))

(defthm create-c-instance-valid-sc
  (implies (and (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c/d a))
           (valid-sc (create-c-instance s pp c/d) a))
  :hints (("Goal"
           :in-theory (e/d (create-c-instance
                            is-rp
                            is-if) ()))))

(progn
  (create-regular-eval-lemma s 2 mult-formula-checks)
  (create-regular-eval-lemma evenpi 1 mult-formula-checks)
  (create-regular-eval-lemma c 3 mult-formula-checks)
  (create-regular-eval-lemma d 1 mult-formula-checks)
  (create-regular-eval-lemma d-sum 3 mult-formula-checks))

(defthm d-to-c-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt (d-to-c c/d) a)
                  (rp-evlt c/d a)))
  :hints (("Goal"
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 (CADDR (CADDR (CADR C/D))))
                            (term2 (CADR (CADR (CADR (CADR (CADDR (CADR
                                                                   C/D))))))))
                 (:instance rp-evlt-of-rp-equal
                            (term1 (CADDDR (CADDR (CADR C/D))))
                            (term2 (CADDR (CADR (CADR (CADR (CADDR (CADR C/D)))))))))
           :in-theory (e/d (d-to-c
                            sum-comm-2-loop-stopper
                            sum-comm-1-loop-stopper
                            f2-to-d2)
                           (rp-evlt-of-rp-equal
                            (:DEFINITION RP-TERMP)
                            sum-comm-2
                            sum-comm-1
                            (:REWRITE RP-EVL-OF-RP-EQUAL2)
                            (:REWRITE RP-TERMP-OF-RP-TRANS)
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:REWRITE IS-RP-PSEUDO-TERMP)
                            (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION FALIST-CONSISTENT)
                            d2-to-f2
                            rp-equal)))))

(defthm d-to-c-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (rp-evlt-equiv (d-to-c c/d) c/d)))

(defthm d-to-c-valid-sc
  (implies (valid-sc c/d a)
           (valid-sc (d-to-c c/d) a))
  :hints (("Goal"
           :in-theory (e/d (d-to-c
                            is-if
                            valid-sc is-rp)
                           ((:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:DEFINITION RP-TERM-LISTP)
                            (:DEFINITION RP-TERMP)
                            (:definition include-fnc))))))

(defthm c/d-cough-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d))
           (b* (((mv s-coughed pp-coughed c/d-cleaned)
                 (c/d-cough c/d)))
             (and (equal (sum (sum-list (rp-evlt s-coughed a))
                              (sum-list (rp-evlt pp-coughed a))
                              (rp-evlt c/d-cleaned a))
                         (ifix (rp-evlt c/d a)))
                  (equal (sum (sum-list (rp-evlt s-coughed a))
                              (sum-list (rp-evlt pp-coughed a))
                              (rp-evlt c/d-cleaned a)
                              rest)
                         (sum (rp-evlt c/d a) rest))
                  (equal (sum rest
                              (sum-list (rp-evlt s-coughed a))
                              (sum-list (rp-evlt pp-coughed a))
                              (rp-evlt c/d-cleaned a))
                         (sum (rp-evlt c/d a) rest)))))
  ;; (equal (rp-evlt c/d-cleaned a)
  ;;        (sum (-- (sum-list (rp-evlt s-coughed a)))
  ;;             (-- (sum-list (rp-evlt pp-coughed a)))
  ;;             (rp-evlt c/d a)))
  :hints (("Goal"
           :in-theory (e/d (equal-sum-of-negated
                            f2-of-times2-reverse
                            d2-of-times2-reverse
                            c/d-cough
                            get-c/d-args)
                           (f2-of-times2
                            rp-termp
                            d2-of-times2)))))

(defthm c/d-cough-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d))
           (b* (((mv s-coughed pp-coughed c/d-cleaned)
                 (c/d-cough c/d)))
             (and (rp-evlt-equiv `(binary-sum (sum-list ,s-coughed)
                                              (binary-sum (sum-list ,pp-coughed)
                                                          ,c/d-cleaned))
                                 `(ifix ,c/d))
                  (rp-evlt-equiv `(binary-sum
                                   (sum-list ,s-coughed)
                                   (binary-sum (sum-list ,pp-coughed)
                                               (binary-sum ,c/d-cleaned
                                                           ,rest)))
                                 `(binary-sum ,c/d ,rest))))))

(defthm CONTEXT-FROM-RP-opener
  (implies (is-rp (cons 'rp rest))
           (equal (context-from-rp (cons 'rp rest) context)
                  (LET ((TYPE (CAR (CDR (CAR rest))))
                        (X (CAR (CDR rest))))
                       (B* ((RCONTEXT (CONTEXT-FROM-RP X CONTEXT)))
                         (CONS (CONS TYPE (CONS (EX-FROM-RP X) 'NIL))
                               RCONTEXT)))))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp) ()))))

(defthmd CONTEXT-FROM-RP-slow-opener-when-rp
  (implies (and (equal (car term) 'rp)
                (force (is-rp term)))
           (equal (context-from-rp term context)
                  (LET ((TYPE (CAR (CDR (CAR (CDR TERM)))))
                        (X (CAR (CDR (CDR TERM)))))
                       (B* ((RCONTEXT (CONTEXT-FROM-RP X CONTEXT)))
                         (CONS (CONS TYPE (CONS (EX-FROM-RP X) 'NIL))
                               RCONTEXT)))))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp) ()))))

(defthm CONTEXT-FROM-RP-opener-when-not-rp
  (implies (not (equal fnc 'rp))
           (equal (context-from-rp (cons fnc rest) context)
                  context))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp is-rp) ()))))

(defthm c/d-cough-valid-sc
  (implies (and (valid-sc c/d a)
                (rp-termp c/d)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv s-coughed pp-coughed c/d-cleaned)
                 (c/d-cough c/d)))
             (and (valid-sc s-coughed a)
                  (valid-sc pp-coughed a)
                  (valid-sc c/d-cleaned a))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance evenpi-lemma-1
                            (s1 (SUM-LIST (RP-EVL (RP-TRANS (CADR (CADDR (CADR C/D))))
                                                  A)))
                            (s2 (SUM-LIST (RP-EVL (RP-TRANS (CADDR (CADDR (CADR C/D))))
                                                  A)))
                            (b1 (SUM-LIST
                                 (RP-EVL (RP-TRANS (MV-NTH 1
                                                           (C/D-FIX-S-ARGS (CADR (CADDR (CADR C/D))))))
                                         A)))
                            (b2 (SUM-LIST
                                 (RP-EVL (RP-TRANS (MV-NTH 1
                                                           (C/D-FIX-PP-ARGS (CADDR (CADDR (CADR C/D)))
                                                                            1073741824)))
                                         A)))
                            (a (RP-EVL (RP-TRANS (CADDDR (CADDR (CADR C/D))))
                                       A))))
           :in-theory (e/d (c/d-cough
                            CONTEXT-FROM-RP-slow-opener-when-rp
                            get-c/d-args
                            is-if is-rp)
                           (rp-termp
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:REWRITE VALID-SC-CADR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE VALID-SC-CADDDR)
                            (:DEFINITION FALIST-CONSISTENT)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            evenpi-lemma-1
                            rp-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; can-c-merge-fast lemmas

;; (defthm m2-of-negated-subterm-dummy-lemma1
;;   (equal (m2 (sum a b c d e (-- (m2 (sum c e)))))
;;          (m2 (sum a b d)))
;;   :hints (("Goal"
;;            :use ((:instance m2-of---
;;                             (x (m2 (sum c e)))
;;                             (rest1 0)
;;                             (rest (sum a b c d e)))
;;                  (:instance m2-of---
;;                             (x (M2 (SUM C E)))
;;                             (rest1 0)
;;                             (rest (sum c d e)))
;;                  (:instance m2-of-times2
;;                             (a e)
;;                             (b (SUM A B (TIMES2 C) D)))
;;                  (:instance m2-of-times2
;;                             (a c)
;;                             (b (SUM A B D)))
;;                  (:instance M2-OF-M2
;;                             (x (sum c e))
;;                             (y (sum a b c d e))))
;;            :in-theory (e/d (sum-of-repeated-to-times2)
;;                            (m2-of---
;;                             m2-of-times2
;;                             S-OF-S-LEMMA1
;;                             M2-OF-M2
;;                             S-OF-MINUS
;;                             S-FIX-PP-ARGS-AUX-CORRECT-DUMMY-LEMMA1)))))

;; (defthm m2-of-negated-subterm-dummy-lemma2
;;   (equal (m2 (sum a b c d e (-- (m2 (sum b d)))))
;;          (m2 (sum a c e)))
;;   :hints (("Goal"
;;            :use ((:instance m2-of---
;;                             (x (m2 (sum b d)))
;;                             (rest1 0)
;;                             (rest (sum a b c d e)))
;;                  (:instance m2-of---
;;                             (x (M2 (SUM b d)))
;;                             (rest1 0)
;;                             (rest (sum c d e)))
;;                  (:instance m2-of-times2
;;                             (a d)
;;                             (b (SUM A c (TIMES2 b) e)))
;;                  (:instance m2-of-times2
;;                             (a b)
;;                             (b (SUM A c e)))
;;                  (:instance M2-OF-M2
;;                             (x (sum b d))
;;                             (y (sum a b c d e))))
;;            :in-theory (e/d (sum-of-repeated-to-times2)
;;                            (m2-of---
;;                             m2-of-times2
;;                             S-OF-S-LEMMA1
;;                             M2-OF-M2
;;                             S-OF-MINUS
;;                             S-FIX-PP-ARGS-AUX-CORRECT-DUMMY-LEMMA1)))))

(encapsulate
  nil

  (local
   (defthmd can-c-merge-fast-correct-lemma-1
     (implies (and (syntaxp (or (equal x '(CAr (cDR (CAr (cDR C/D1)))))
                                (equal x '(CAr (cDR (CAr (cDR C/D2))))))))
              (equal (rp-evlt x a)
                     (rp-evlt (ex-from-rp x) a)))))

  ;; (defthmd can-c-merge-fast-aux-correct-lemma
  ;;   (implies (and (can-c-merge-fast-aux s-lst pp c/d)
  ;;                 (rp-evl-meta-extract-global-facts :state state)
  ;;                 (mult-formula-checks state))
  ;;            (equal (sum (rp-evlt `(c nil ,pp ,c/d) a)
  ;;                                 (rp-evlt `(c (list . ,s-lst) ,pp2 ,c/d2)))
  ;;                   (f2 (sum

  (defthmd can-c-merge-fast-correct-lemma
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp c/d1)
                  (rp-termp c/d2))
             (b* ((result (can-c-merge-fast c/d1 c/d2))
                  ((mv s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                  ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
               (implies result
                        (equal (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))
                               (if (equal result 0)
                                   (f2 (sum #|(-- (m2 (sum (sum-list (rp-evlt pp-arg1 a))
                                        (rp-evlt c/d-arg1 a))))||#
                                        (sum-list (rp-evlt pp-arg1 a))
                                        (rp-evlt c/d-arg1 a)
                                        (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                        (sum-list (rp-evlt pp-arg2 a))
                                        (rp-evlt c/d-arg2 a)))
                                 (f2 (sum #|(-- (m2 (sum (sum-list (rp-evlt pp-arg2 a))
                                      (rp-evlt c/d-arg2 a))))||#
                                      (sum-list (rp-evlt pp-arg2 a))
                                      (rp-evlt c/d-arg1 a)
                                      (sum-list (rp-evlt `(list . ,(cddr s-arg1)) a))
                                      (sum-list (rp-evlt pp-arg1 a))
                                      (rp-evlt c/d-arg2 a))))))))
;:otf-flg t
    :hints (("Goal"
             :expand ((:free (x) (nth 3 x)))
             :in-theory (e/d (get-c/d-args
                              can-c-merge-fast-correct-lemma-1
                              can-c-merge-fast
                              can-c-merge-fast-aux
                              f2-to-d2)
                             (d2-to-f2
                              rp-termp
                              D2-OF-MINUS
                              (:DEFINITION EX-FROM-RP)
                              (:REWRITE DEFAULT-CDR)
                              (:DEFINITION INCLUDE-FNC)
                              rp-trans
                              RP-EVLT-OF-EX-FROM-RP))))))

(defthm sum-of-swap-c/ds
  (b* (((mv c/d1-new c/d2-new) (swap-c/ds c/d1 c/d2 cond)))
    (equal (sum (rp-evlt c/d1-new a) (rp-evlt c/d2-new a))
           (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))))
  :hints (("Goal"
           :in-theory (e/d (swap-c/ds) ()))))

(defthm swap-c/ds-valid-sc
  (implies (and (valid-sc c/d1 a)
                (valid-sc c/d2 a))
           (b* (((mv c/d1-new c/d2-new) (swap-c/ds c/d1 c/d2 cond)))
             (and (valid-sc c/d1-new a)
                  (valid-sc c/d2-new a))))
  :hints (("Goal"
           :in-theory (e/d (swap-c/ds) ()))))

(defthm can-c-merge-fast-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d1)
                (rp-termp c/d2))
           (b* ((result (can-c-merge-fast c/d1 c/d2))
                ((mv c/d-orig1 c/d-orig2) (mv c/d1 c/d2))
                ((mv c/d1 c/d2)
                 (swap-c/ds c/d1 c/d2 (equal result 1)))
                ((mv ?s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
             (implies result
                      (equal (sum (rp-evlt c/d-orig1 a) (rp-evlt c/d-orig2 a))
                             (f2 (sum (sum-list (rp-evlt pp-arg1 a))
                                      (rp-evlt c/d-arg1 a)
                                      (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                      (sum-list (rp-evlt pp-arg2 a))
                                      (rp-evlt c/d-arg2 a)))))))
  :hints (("Goal"
           :use ((:instance can-c-merge-fast-correct-lemma))
           :in-theory (e/d (swap-c/ds)
                           (rp-termp
                            rp-trans)))))

(defthm can-c-merge-fast-correct-with-sk
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d1)
                (rp-termp c/d2))
           (b* ((result (can-c-merge-fast c/d1 c/d2))
                ((mv c/d-orig1 c/d-orig2) (mv c/d1 c/d2))
                ((mv c/d1 c/d2)
                 (swap-c/ds c/d1 c/d2 (equal result 1)))
                ((mv ?s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
             (implies result
                      (rp-evlt-equiv `(binary-sum ,c/d-orig1 ,c/d-orig2)
                                     `(f2 (binary-sum
                                           (sum-list ,pp-arg1)
                                           (binary-sum
                                            ,c/d-arg1
                                            (binary-sum
                                             (sum-list ,(cons 'list  (cddr s-arg2)))
                                             (binary-sum
                                              (sum-list ,pp-arg2)
                                              ,c/d-arg2)))))))))
  :hints (("Goal"
           :use ((:instance can-c-merge-fast-correct
                            (a (rp-evlt-equiv-witness
                                (list 'binary-sum c/d1 c/d2)
                                (list
                                 'f2
                                 (list
                                  'binary-sum
                                  (list
                                   'sum-list
                                   (mv-nth 1
                                           (get-c/d-args
                                            (mv-nth 0
                                                    (swap-c/ds c/d1 c/d2
                                                               (equal (can-c-merge-fast c/d1 c/d2)
                                                                      1))))))
                                  (list
                                   'binary-sum
                                   (mv-nth 2
                                           (get-c/d-args
                                            (mv-nth 0
                                                    (swap-c/ds c/d1 c/d2
                                                               (equal (can-c-merge-fast c/d1 c/d2)
                                                                      1)))))
                                   (list
                                    'binary-sum
                                    (list
                                     'sum-list
                                     (cons
                                      'list
                                      (cddr
                                       (mv-nth
                                        0
                                        (get-c/d-args
                                         (mv-nth 1
                                                 (swap-c/ds c/d1 c/d2
                                                            (equal (can-c-merge-fast c/d1 c/d2)
                                                                   1))))))))
                                    (list
                                     'binary-sum
                                     (list
                                      'sum-list
                                      (mv-nth
                                       1
                                       (get-c/d-args
                                        (mv-nth 1
                                                (swap-c/ds c/d1 c/d2
                                                           (equal (can-c-merge-fast c/d1 c/d2)
                                                                  1))))))
                                     (mv-nth
                                      2
                                      (get-c/d-args
                                       (mv-nth 1
                                               (swap-c/ds c/d1 c/d2
                                                          (equal (can-c-merge-fast c/d1 c/d2)
                                                                 1))))))))))))))
           :in-theory (e/d ()
                           (rp-termp
                            rp-trans)))))

(define swapped-1 (c/d1 c/d2)
  (b* ((cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                      (EX-FROM-RP C/D2))
                    1))
       ((mv a &)
        (SWAP-C/DS (EX-FROM-RP C/D1)
                   (EX-FROM-RP C/D2)
                   cond)))
    a)
  ///
  (defthm to-swapped-1
    (and (equal (MV-NTH 0
                        (SWAP-C/DS (EX-FROM-RP C/D1)
                                   (EX-FROM-RP C/D2)
                                   (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                            (EX-FROM-RP C/D2))
                                          1)))
                (swapped-1 c/d1 c/d2))
         (implies (not (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                         (EX-FROM-RP C/D2)))
                  (equal (MV-NTH 0
                                 (SWAP-C/DS (EX-FROM-RP C/D1)
                                            (EX-FROM-RP C/D2)
                                            nil))
                         (swapped-1 c/d1 c/d2))))))

(define swapped-2 (c/d1 c/d2)
  (b* ((cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                      (EX-FROM-RP C/D2))
                    1))
       ((mv & A)
        (SWAP-C/DS (EX-FROM-RP C/D1)
                   (EX-FROM-RP C/D2)
                   cond)))
    a)
  ///
  (defthm to-swapped-2
    (and (equal (MV-NTH 1
                        (SWAP-C/DS (EX-FROM-RP C/D1)
                                   (EX-FROM-RP C/D2)
                                   (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                            (EX-FROM-RP C/D2))
                                          1)))
                (swapped-2 c/d1 c/d2))
         (implies (not (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                         (EX-FROM-RP C/D2)))
                  (equal (MV-NTH 1
                                 (SWAP-C/DS (EX-FROM-RP C/D1)
                                            (EX-FROM-RP C/D2)
                                            nil))
                         (swapped-2 c/d1 c/d2))))))

(defthm sum-of-swap-c/ds-for-swapped-fncs
  (and (equal (sum (rp-evlt (swapped-1 c/d1 c/d2) a)
                   (rp-evlt (swapped-2 c/d1 c/d2) a))
              (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a)))
       (equal (sum (rp-evlt (swapped-2 c/d1 c/d2) a)
                   (rp-evlt (swapped-1 c/d1 c/d2) a))
              (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))))
  :hints (("Goal"
           :use ((:instance sum-of-swap-c/ds
                            (c/d1 (ex-from-rp c/d1))
                            (cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                           (EX-FROM-RP C/D2))
                                         1))
                            (c/d2 (ex-from-rp c/d2))))
           :in-theory (e/d ( swapped-1
                             swapped-2)
                           (sum-of-swap-c/ds
                            to-swapped-1
                            to-swapped-2)))))

(defthm swapped-fncs-valid-sc
  (implies (and (valid-sc c/d1 a)
                (valid-sc c/d2 a))
           (and (valid-sc (swapped-1 c/d1 c/d2) a)
                (valid-sc (swapped-2 c/d1 c/d2) a)))
  :hints (("Goal"
           :use ((:instance swap-c/ds-valid-sc
                            (c/d1 (ex-from-rp c/d1))
                            (cond (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                           (EX-FROM-RP C/D2))
                                         1))
                            (c/d2 (ex-from-rp c/d2))))
           :in-theory (e/d (swapped-1
                            swapped-2)
                           (swap-c/ds-valid-sc
                            to-swapped-1
                            to-swapped-2)))))

(defthm can-c-merge-fast-correct-for-swapped-fncs
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp c/d1)
                (rp-termp c/d2))
           (b* ((result (can-c-merge-fast (ex-from-rp c/d1)
                                          (ex-from-rp c/d2)))
                ((mv c/d-orig1 c/d-orig2) (mv c/d1 c/d2))

                ((mv c/d1 c/d2)
                 (mv (swapped-1 c/d1 c/d2 )
                     (swapped-2 c/d1 c/d2 )))

                ((mv ?s-arg1 pp-arg1 c/d-arg1 ?type1) (get-c/d-args c/d1))
                ((mv s-arg2 pp-arg2 c/d-arg2 ?type2) (get-c/d-args c/d2)))
             (implies result
                      (and (equal (sum (rp-evlt c/d-orig1 a) (rp-evlt c/d-orig2 a))
                                  (f2 (sum (sum-list (rp-evlt pp-arg1 a))
                                           (rp-evlt c/d-arg1 a)
                                           (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                           (sum-list (rp-evlt pp-arg2 a))
                                           (rp-evlt c/d-arg2 a))))
                           (equal (sum (rp-evlt c/d-orig1 a)
                                       (rp-evlt c/d-orig2 a)
                                       other)
                                  (sum (f2 (sum (sum-list (rp-evlt pp-arg1 a))
                                                (rp-evlt c/d-arg1 a)
                                                (sum-list (rp-evlt `(list . ,(cddr s-arg2)) a))
                                                (sum-list (rp-evlt pp-arg2 a))
                                                (rp-evlt c/d-arg2 a)))
                                       other))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance can-c-merge-fast-correct
                            (c/d1 (ex-from-rp c/d1))
                            (c/d2 (ex-from-rp c/d2))))
           :in-theory (e/d (to-swapped-1
                            to-swapped-2)
                           (rp-termp
                            ex-from-rp
                            can-c-merge-fast-correct
                            rp-trans
                            )))))

(defthm rp-termp-of-swapped-fncs
  (implies (and (rp-termp c/d1)
                (rp-termp c/d2))
           (and (rp-termp (swapped-1 c/d1 c/d2 ))
                (rp-termp (swapped-2 c/d1 c/d2 ))))
  :hints (("Goal"

           :in-theory (e/d (swapped-1
                            swapped-2)
                           (to-swapped-2
                            to-swapped-1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c/d-merge lemmas

(defthmd sum-of-swap-c/ds-reverse
  (implies (syntaxp (and (equal c/d1 'c/d1)
                         (equal c/d2 'c/d2)))
           (equal
            (sum (rp-evlt c/d1 a) (rp-evlt c/d2 a))
            (sum (rp-evlt (MV-NTH 0
                                  (SWAP-C/DS (EX-FROM-RP C/D1)
                                             (EX-FROM-RP C/D2)
                                             (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                                      (EX-FROM-RP C/D2))
                                                    1)))
                          a)
                 (rp-evlt (MV-NTH 1
                                  (SWAP-C/DS (EX-FROM-RP C/D1)
                                             (EX-FROM-RP C/D2)
                                             (EQUAL (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                                                      (EX-FROM-RP C/D2))
                                                    1)))
                          a))))
  :hints (("Goal"
           :in-theory (e/d (sum-of-swap-c/ds) ()))))

(local
 (defthm is-if-lemma
   (implies (or (atom x)
                (not (equal (car x) 'if)))
            (not (is-if x)))
   :hints (("Goal"
            :in-theory (e/d (is-if) ())))))

(local
 (defthm is-rp-lemma
   (implies (or (atom x)
                (not (equal (car x) 'rp)))
            (not (is-rp x)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm is-falist-lemma
   (implies (or (atom x)
                (not (equal (car x) 'falist)))
            (not (is-falist x)))
   :hints (("Goal"
            :in-theory (e/d (is-falist) ())))))

(local
 (in-theory (disable falist-consistent)))

;; (include-book "misc/untranslate-patterns" :dir :system)

;; (acl2::add-untranslate-pattern-function (swapped-1 c/d1 c/d2)
;;                                         swapped-1)

;; (acl2::add-untranslate-pattern-function (swapped-2 c/d1 c/d2)
;;                                         swapped-2)

(defthm sum-list-of-negated-m2
  (equal (sum-list (list (-- (m2 x))))
         (-- (m2 x)))
  :hints (("Goal"
           :in-theory (e/d (sum-list) ()))))

(defthm rid-of-get-extra-s-arg
  (implies (EQUAL
            (RP-EVL (RP-TRANS (GET-EXTRA-S-ARG cadr caddr cadddr limit))
                    A)
            (LIST (-- (M2 (SUM (SUM-LIST (RP-EVL (RP-TRANS cadr)
                                                 A))
                               (SUM-LIST (RP-EVL (RP-TRANS caddr)
                                                 A))
                               (RP-EVL (RP-TRANS cadddr)
                                       A))))))
           (equal (SUM-LIST (RP-EVL (RP-TRANS (GET-EXTRA-S-ARG cadr caddr cadddr limit))
                                    A))
                  (-- (M2 (SUM (SUM-LIST (RP-EVL (RP-TRANS cadr)
                                                 A))
                               (SUM-LIST (RP-EVL (RP-TRANS caddr)
                                                 A))
                               (RP-EVL (RP-TRANS cadddr)
                                       A)))))))

(defthm rid-of-c/d-merge-sum
  (implies (EQUAL
            (SUM (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 0
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (RP-EVL (RP-TRANS (MV-NTH 2
                                           (C/D-MERGE param1
                                                      param2
                                                      flg limit)))
                         A))
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)))
           (equal
            (sum (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 0
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                     (C/D-MERGE param1
                                                                param2
                                                                flg limit)))
                                   A))
                 (RP-EVL (RP-TRANS (MV-NTH 2
                                           (C/D-MERGE param1
                                                      param2
                                                      flg limit)))
                         A)
                 other)
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)
                 other)))
  :hints (("Goal"
           :in-theory (e/d (sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper)
                           (sum-comm-1
                            sum-comm-2)))))

(defthm rid-of-c/d-merge-sum-2
  (implies (EQUAL
            (SUM
             (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                 (C/D-MERGE param1
                                                            param2
                                                            flg limit)))
                               A))
             (RP-EVL (RP-TRANS (MV-NTH 2
                                       (C/D-MERGE param1
                                                  param2
                                                  flg limit)))
                     A))
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)))
           (equal
            (sum
             (SUM-LIST (RP-EVL (RP-TRANS (MV-NTH 1
                                                 (C/D-MERGE param1
                                                            param2
                                                            flg limit)))
                               A))
             (RP-EVL (RP-TRANS (MV-NTH 2
                                       (C/D-MERGE param1
                                                  param2
                                                  flg limit)))
                     A)
             other)
            (SUM (RP-EVL (RP-TRANS param1)
                         A)
                 (RP-EVL (RP-TRANS param2)
                         A)
                 other)))
  :hints (("Goal"
           :in-theory (e/d (sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper)
                           (sum-comm-1
                            sum-comm-2)))))

(defthm valid-sc-lemma1
  (implies (and (valid-sc term a)
                (case-match term (('d ('rp ''evenpi ('d-sum & & &))) t)))
           (and (VALID-SC (CADDDR (CADDR (CADR term))) A)
                (VALID-SC (CADR (CADDR (CADR term))) A)
                (VALID-SC (CADDR (CADDR (CADR term))) A)
                (VALID-SC (CADR TERM) A)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((EVAL-AND-ALL (CONTEXT-FROM-RP (CADR TERM) NIL)
                                  A)
                    (CONTEXT-FROM-RP (CADR TERM) NIL)
                    (valid-sc term a)
                    (VALID-SC (CADR TERM) A)
                    (VALID-SC (CADR TERM) A)
                    (VALID-SC-SUBTERMS (CDR TERM) A))
           :in-theory (e/d (is-if is-rp
                                  valid-sc-subterms
                                  valid-sc)
                           (is-if-lemma
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            is-rp-lemma)))))

(defthm valid-sc-lemma2
  (implies (and (valid-sc term a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (case-match term (('d ('rp ''evenpi ('d-sum & & &))) t)))
           (and (evenpi (rp-evlt (CADDR (CADR term)) a))
                (evenpi (rp-evlt (CADR term) a))
                (evenpi (SUM (SUM-LIST (RP-EVL (RP-TRANS (CADR (CADDR (CADR term))))
                                               A))
                             (SUM-LIST (RP-EVL (RP-TRANS (CADDR (CADDR (CADR term))))
                                               A))
                             (RP-EVL (RP-TRANS (CADDDR (CADDR (CADR term))))
                                     A)))
                (evenpi (SUM (SUM-LIST (RP-EVL (RP-TRANS (CADDR (CADDR (CADR term))))
                                               A))
                             (RP-EVL (RP-TRANS (CADDDR (CADDR (CADR term))))
                                     A)
                             (SUM-LIST (RP-EVL (RP-TRANS (CADR (CADDR (CADR term))))
                                               A))
                             ))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((EVAL-AND-ALL (CONTEXT-FROM-RP (CADR TERM) NIL)
                                  A)
                    (CONTEXT-FROM-RP (CADR TERM) NIL)
                    (valid-sc term a)
                    (VALID-SC (CADR TERM) A)
                    (VALID-SC-SUBTERMS (CDR TERM) A))
           :in-theory (e/d (is-if is-rp)
                           (is-if-lemma
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                            (:DEFINITION RP-TERMP)
                            is-rp-lemma)))))

(defthm dummy-lemma1
  (implies (case-match term (('rp & &) t))
           (equal (RP-EVL (RP-TRANS term) A)
                  (RP-EVL (RP-TRANS (caddr term)) A))))

(defthmd can-c-merge-fast-and-consp
  (implies
   (can-c-merge-fast c/d1 c/d2)
   (and (consp
         (mv-nth
          0
          (get-c/d-args
           (mv-nth 1
                   (swap-c/ds c/d1 c/d2
                              (equal (can-c-merge-fast c/d1 c/d2)
                                     1))))))
        (consp
         (cdr (mv-nth
               0
               (get-c/d-args
                (mv-nth 1
                        (swap-c/ds c/d1 c/d2
                                   (equal (can-c-merge-fast c/d1 c/d2)
                                          1)))))))
        (equal (car (mv-nth
                     0
                     (get-c/d-args
                      (mv-nth 1
                              (swap-c/ds c/d1 c/d2
                                         (equal (can-c-merge-fast c/d1 c/d2)
                                                1))))))
               'list)))
  :hints (("goal"
           :in-theory (e/d (can-c-merge-fast
                            can-c-merge-fast-aux
                            get-c/d-args
                            swap-c/ds) ()))))

(local
 (defthm dummy-lemma2
   (implies (and (can-c-merge-fast (ex-from-rp c/d1) (ex-from-rp c/d2))
                 (equal (car (swapped-2 c/d1 c/d2)) 'c))
            (and (consp (cadr (swapped-2 c/d1 c/d2)))
                 (consp (cdr (cadr (swapped-2 c/d1 c/d2))))
                 (equal (car (cadr (swapped-2 c/d1 c/d2))) 'list)))
   :hints (("goal"
            :use ((:instance can-c-merge-fast-and-consp
                             (c/d1 (ex-from-rp c/d1))
                             (c/d2 (ex-from-rp c/d2))))
            :in-theory (e/d (get-c/d-args)
                            ())))))

(local
 (defthm valid-sc-dummy-lemma
   (implies (and (valid-sc term a)
                 (consp (cdr term))
                 (consp term)
                 (equal (car term) 'list))
            (VALID-SC-SUBTERMS (CDDR term) A))
   :hints (("Goal"
            :expand (valid-sc term a)
            :in-theory (e/d (is-if is-rp) ())))))

(local
 (defthm rp-termp-dummy-lemma
   (implies (and (rp-termp term)
                 (consp (cdr term))
                 (consp term)
                 (equal (car term) 'list))
            (rp-term-listp (CDDR term)))
   :hints (("Goal"
            :expand ((rp-termp term)
                     (RP-TERM-LISTP (CDR TERM)))
            :in-theory (e/d (is-if is-rp is-falist) ())))))

(defthm REMOVE-S-FROM-FOR-FAST-MERGE-valid-sc
  (implies (and (can-c-merge-fast (ex-from-rp c/d1) (ex-from-rp c/d2))
                (valid-sc c/d1 a)
                (valid-sc c/d2 a))
           (valid-sc (REMOVE-S-FROM-FOR-FAST-MERGE
                      (CADR (SWAPPED-2 C/D1 C/D2)) x y)
                     a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (REMOVE-S-FROM-FOR-FAST-MERGE
                            SWAP-C/DS
                            GET-C/D-ARGS
                            CAN-C-MERGE-FAST-AUX
                            CAN-C-MERGE-FAST
                            SWAPPED-2)
                           (to-SWAPPED-2
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            rp-termp
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION VALID-SC-SUBTERMS)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:DEFINITION EX-FROM-RP)
                            (:DEFINITION RP-TERMP)
                            (:REWRITE EX-FROM-RP-LOOSE-IS-EX-FROM-RP)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:TYPE-PRESCRIPTION RP-TERMP))))))

(defthm REMOVE-S-FROM-FOR-FAST-MERGE-rp-termp
  (implies (and (can-c-merge-fast (ex-from-rp c/d1) (ex-from-rp c/d2))
                (rp-termp c/d1)
                (rp-termp c/d2))
           (rp-termp (REMOVE-S-FROM-FOR-FAST-MERGE
                      (CADR (SWAPPED-2 C/D1 C/D2)) x y)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (REMOVE-S-FROM-FOR-FAST-MERGE
                            SWAP-C/DS
                            GET-C/D-ARGS
                            CAN-C-MERGE-FAST-AUX
                            CAN-C-MERGE-FAST
                            SWAPPED-2)
                           (to-SWAPPED-2
                            (:DEFINITION RP-TERM-LISTP)
                            (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION EX-FROM-RP)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE IS-RP-LEMMA)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:DEFINITION ATOM)
                            (:TYPE-PRESCRIPTION IS-RP$INLINE))))))

#|(skip-proofs
 (defthm REMOVE-S-FROM-FOR-FAST-MERGE-redef
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (CAN-C-MERGE-FAST (EX-FROM-RP C/D1)
                                   (EX-FROM-RP C/D2)))
            (equal (sum-list
                    (RP-EVLt (remove-s-from-for-fast-merge (cadr (swapped-2 c/d1 c/d2))
                                                           (caddr (swapped-1 c/d1 c/d2))
                                                           (cadddr (swapped-1 c/d1 c/d2)))
                             a))
                   (sum-list (rp-evlt (s-sum-merge (cadr (swapped-2 c/d1 c/d2))
                                                   `(list (-- (s ,(caddr
                                                                   (swapped-1 c/d1 c/d2))
                                                                 ,(cadddr
                                                                   (swapped-1 c/d1 c/d2))))))
                                      a))))))||#

(defthm sum-of-SWAP-C/DS-when-one-is-zero
  (and (equal (SUM (RP-EVL (RP-TRANS (MV-NTH 0
                                             (SWAP-C/DS c/d1 ''0 cond)))
                           A)
                   (RP-EVL (RP-TRANS (MV-NTH 1
                                             (SWAP-C/DS c/d1 ''0 cond)))
                           A))
              (IFIX (RP-EVL (RP-TRANS C/D1) A)))
       (equal (SUM (RP-EVL (RP-TRANS (MV-NTH 0
                                             (SWAP-C/DS ''0 c/d1 cond)))
                           A)
                   (RP-EVL (RP-TRANS (MV-NTH 1
                                             (SWAP-C/DS ''0 c/d1 cond)))
                           A))
              (IFIX (RP-EVL (RP-TRANS C/D1) A))))
  :hints (("Goal"
           :in-theory (e/d (SWAP-C/DS) ()))))

(defthm rp-evlt-when-quotep
  (implies (and (consp x)
                (consp (cdr x))
                (equal (car x) 'quote))
           (equal (rp-evlt x a)
                  (unquote x)))
  :hints (("Goal"
           :in-theory (e/d (rp-trans) ()))))

(defthm m2-of-ex-from-rp/--
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term))
           (equal (M2 (SUM (RP-EVL (RP-TRANS (EX-FROM-RP/-- term))  A) rest))
                  (M2 (SUM (RP-EVL (RP-TRANS term)  A) rest))))
  :hints (("Goal"
           :do-not-induct t
           :induct (EX-FROM-RP/-- term)
           :in-theory (e/d (EX-FROM-RP/--) ()))))

(defthm ex-from-rp/--valid-sc
  (implies (valid-sc term a)
           (VALID-SC (EX-FROM-RP/-- term) A))
  :hints (("Goal"
           :induct (EX-FROM-RP/-- term)
           :in-theory (e/d (is-rp is-if
                                  EX-FROM-RP/--)
                           ()))))

(defthm m2-of-lemma1
  (implies (and (EQUAL (EX-FROM-RP/-- term) ''NIL)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term))
           (equal (M2 (RP-EVL (RP-TRANS term) A))
                  0))
  :hints (("Goal"
           :use ((:instance m2-of-ex-from-rp/--
                            (rest 0)))
           :in-theory (e/d () (m2-of-ex-from-rp/--)))))

(defthm m2-of-lemma2
  (implies (and (equal (m2 (sum a b)) (m2 c))
                (equal (m2 (sum x y)) (m2 (sum k l m))))
           (equal (equal (m2 (sum a b x y))
                         (m2 (sum k l m c)))
                  t))
  :hints (("Goal"
           :use ((:instance m2-with-extra
                            (x (sum a b))
                            (y c)
                            (other (sum x y)))
                 (:instance m2-with-extra
                            (x (sum x y))
                            (y (sum k l m))))
           :in-theory (e/d () (m2-with-extra)))))

(defthm is-rp-evenpi
  (is-rp (list 'rp ''evenpi x))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm sum-merge-aux-retains-evenpi-lemma
  (implies (equal (evenpi x) (evenpi (sum a b)))
           (equal (equal (evenpi (sum other x))
                         (evenpi (sum a b other)))
                  t))
  :hints (("Goal"
           :use ((:instance EVENPI-WITH-OTHER
                            (x x)
                            (y (sum a b))
                            (z other)))
           :in-theory (e/d ()
                           (EVENPI-WITH-OTHER)))))

(defthm sum-merge-aux-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-term-listp s-lst1)
                (rp-term-listp s-lst2))
           (equal (evenpi (sum-list-eval (s-sum-merge-aux s-lst1 s-lst2) a))
                  (evenpi (sum (sum-list-eval s-lst1 a)
                               (sum-list-eval s-lst2 a)))))
  :hints (("Goal"
           :induct (s-sum-merge-aux s-lst1 s-lst2)
           :do-not-induct t
           :in-theory (e/d (s-sum-merge-aux
                            sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper
                            sum-merge-aux-retains-evenpi-lemma
                            )
                           (sum-comm-2
                            sum-comm-1)))))

(defthm sum-merge-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp s1)
                (rp-termp s2))
           (equal (evenpi (sum-list (rp-evlt (s-sum-merge s1 s2) a)))
                  (evenpi (sum (sum-list (rp-evlt s1 a))
                               (sum-list (rp-evlt s2 a))))))
  :hints (("Goal"
           :use ((:instance s-sum-merge-aux-correct
                            (term1 (cdr s1))
                            (term2 (cdr s2))))
           :in-theory (e/d (s-sum-merge
                            sum-comm-1-loop-stopper
                            sum-comm-2-loop-stopper)
                           (SUM-MERGE-AUX-RETAINS-EVENPI
                            sum-comm-1
                            sum-comm-2)))))

(defthm pp-merge-retains-evenpi
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp s1)
                (rp-termp s2))
           (equal (evenpi (sum-list (rp-evlt (mv-nth 0 (pp-sum-merge s1 s2)) a)))
                  (evenpi (sum (sum-list (rp-evlt s1 a))
                               (sum-list (rp-evlt s2 a))))))
;:otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance pp-sum-merge-aux-correct
                            (term1 (cdr s1))
                            (cnt 0)
                            (term2 (cdr s2))))
           :in-theory (e/d (pp-sum-merge)
                           ()))))

(local
 (defthm rp-termp-of-d
   (iff (rp-termp `(d ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of---
   (iff (rp-termp `(-- ,x))
        (rp-termp x))))

(local
 (defthm rp-termp-of-list
   (iff (rp-termp `(list . ,x))
        (rp-term-listp x))))

(local
 (defthm rp-termp-of-d-sum
   (iff (rp-termp `(d-sum ,x ,y ,z))
        (and (rp-termp x)
             (rp-termp y)
             (rp-termp z)))))

(local
 (defthm rp-termp-of-of-rp-evenpi
   (iff (rp-termp `(rp 'evenpi ,x))
        (rp-termp x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(defthm c/d-merge-slow-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg1) (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (if c/d1-is-c (rp-termp extra-s-arg1) t)
                (if c/d2-is-c (rp-termp extra-s-arg2) t)
                (rp-termp c/d-arg))
           (b* (((mv s-coughed pp-coughed c/d-merged)
                 (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg1 s-arg2 s-coughed-from-arg
                                     extra-s-arg1 extra-s-arg2
                                     c/d-arg clean-flg
                                     c/d1-is-c c/d2-is-c)))
             (equal (sum (sum-list  (rp-evlt s-coughed a))
                         (sum-list (rp-evlt pp-coughed a))
                         (rp-evlt c/d-merged a))
                    (d2 (sum (rp-evlt `(sum-list ,pp-arg1) a)
                             (rp-evlt `(sum-list ,pp-arg2) a)
                             (rp-evlt `(sum-list ,pp-coughed-from-arg) a)
                             (rp-evlt `(sum-list ,s-arg1) a)
                             (rp-evlt `(sum-list ,s-arg2) a)
                             (rp-evlt `(sum-list ,s-coughed-from-arg) a)
                             (if c/d1-is-c (rp-evlt `(sum-list ,extra-s-arg1) a) 0)
                             (if c/d2-is-c (rp-evlt `(sum-list ,extra-s-arg2) a) 0)
                             (rp-evlt c/d-arg a))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (c/d-merge-slow-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2
                            (:TYPE-PRESCRIPTION RP-TERMP)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION IS-RP$INLINE)
                            (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                            falist-consistent
                            (:TYPE-PRESCRIPTION S-SUM-MERGE)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_EVENPI_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS)
                            rp-termp)))))

(defthm c/d-merge-slow-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg1) (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (if c/d1-is-c (rp-termp extra-s-arg1) t)
                (if c/d2-is-c (rp-termp extra-s-arg2) t)
                (rp-termp c/d-arg)

                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg1 a) (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc extra-s-arg1 a)
                (valid-sc extra-s-arg2 a)
                (valid-sc c/d-arg a))
           (b* (((mv s-coughed pp-coughed ?c/d-merged)
                 (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg1 s-arg2 s-coughed-from-arg
                                     extra-s-arg1 extra-s-arg2
                                     c/d-arg clean-flg
                                     c/d1-is-c c/d2-is-c)))
             (and (valid-sc s-coughed a)
                  (valid-sc pp-coughed a)
                  )))
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC ''NIL A))
           :in-theory (e/d (c/d-merge-slow-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2

                            (:TYPE-PRESCRIPTION S-SUM-MERGE)

                            (:DEFINITION RP-TERMP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            c/d-merge-slow-aux-correct)))))

(defthm c/d-merge-slow-aux-valid-sc-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg1) (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (if c/d1-is-c (rp-termp extra-s-arg1) t)
                (if c/d2-is-c (rp-termp extra-s-arg2) t)
                (rp-termp c/d-arg)

                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg1 a) (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc extra-s-arg1 a)
                (valid-sc extra-s-arg2 a)
                (valid-sc c/d-arg a))
           (b* (((mv ?s-coughed ?pp-coughed c/d-merged)
                 (c/d-merge-slow-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg1 s-arg2 s-coughed-from-arg
                                     extra-s-arg1 extra-s-arg2
                                     c/d-arg clean-flg
                                     c/d1-is-c c/d2-is-c)))
             (and (implies (evenpi (sum (rp-evlt `(sum-list ,pp-arg1) a)
                                        (rp-evlt `(sum-list ,pp-arg2) a)
                                        (rp-evlt `(sum-list ,pp-coughed-from-arg) a)
                                        (rp-evlt `(sum-list ,s-arg1) a)
                                        (rp-evlt `(sum-list ,s-arg2) a)
                                        (rp-evlt `(sum-list ,s-coughed-from-arg) a)
                                        (if c/d1-is-c (rp-evlt `(sum-list ,extra-s-arg1) a) 0)
                                        (if c/d2-is-c (rp-evlt `(sum-list ,extra-s-arg2) a) 0)
                                        (rp-evlt c/d-arg a)))
                           (valid-sc c/d-merged a))
                  )))
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (valid-sc (cons 'd x) a))
                    (:free (x) (valid-sc (cons 'd-sum x) a))
                    (:free (x) (valid-sc (cons 'rp x) a)))
           :use ((:instance c/d-merge-slow-aux-correct)
                 (:instance c/d-fix-s-args-retains-evenpi-with-other
                            (other (sum  (RP-EVL (RP-TRANS C/D-ARG) A)
                                         (SUM-LIST (RP-EVL (RP-TRANS PP-ARG1) A))
                                         (SUM-LIST (RP-EVL (RP-TRANS PP-ARG2) A))
                                         (SUM-LIST (RP-EVL (RP-TRANS PP-COUGHED-FROM-ARG)
                                                           A))))
                            (pp (S-SUM-MERGE (S-SUM-MERGE S-ARG1
                                                          (S-SUM-MERGE S-ARG2 S-COUGHED-FROM-ARG))
                                             (S-SUM-MERGE EXTRA-S-ARG1 EXTRA-S-ARG2)))))
           :in-theory (e/d (c/d-merge-slow-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:TYPE-PRESCRIPTION S-SUM-MERGE)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE RP-TRANS-WHEN-LIST)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_BIT-OF_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_BINARY-APPEND_WHEN_MULT-FORMULA-CHECKS)
                            rp-termp
                            valid-sc
                            c/d-merge-slow-aux-correct)))))

(defthm sum-of-c-args-gives-evenpi
  (evenpi (sum (-- (m2 (sum a1 b1 c1)))
               (-- (m2 (sum a2 b2 c2)))
               a1 b1 c1 a2 b2 c2))
  :hints (("Goal"
           :use ((:instance evenpi-for-3-d2-arguments
                            (a a1)
                            (b b1)
                            (c c1))
                 (:instance evenpi-for-3-d2-arguments
                            (a a2)
                            (b b2)
                            (c c2))
                 (:instance evenpi-of-sum
                            (x (SUM A1 B1 C1 (-- (M2 (SUM A1 B1 C1)))))
                            (y (SUM A2 B2 C2 (-- (M2 (SUM A2 B2 C2)))))))
           :in-theory (e/d () (evenpi-for-3-d2-arguments
                               evenpi-of-sum)))))

(defthm sum-of-c-and-d-args-gives-evenpi
  (implies (evenpi (sum a2 b2 c2))
           (and (evenpi (sum (-- (m2 (sum a1 b1 c1))) a1 b1 c1 a2 b2 c2 ))
                (evenpi (sum (-- (m2 (sum a1 b1 c1))) a2 b2 c2 a1 b1 c1  ))))
  :hints (("Goal"
           :use ((:instance evenpi-for-3-d2-arguments
                            (a a1)
                            (b b1)
                            (c c1))
                 (:instance evenpi-of-sum
                            (x (SUM A1 B1 C1 (-- (M2 (SUM A1 B1 C1)))))
                            (y (SUM A2 B2 C2))))
           :in-theory (e/d () (evenpi-for-3-d2-arguments
                               evenpi-of-sum)))))

(defthm sum-of-d-args-gives-evenpi
  (implies (and (evenpi (sum a1 b1 c1))
                (evenpi (sum a2 b2 c2)))
           (evenpi (sum a1 b1 c1 a2 b2 c2)))
  :hints (("Goal"
           :use (:instance evenpi-of-sum
                           (x (sum a1 b1 c1))
                           (y (sum a2 b2 c2)))
           :in-theory (e/d () (evenpi-of-sum)))))

(defthm m2-of-ex-from-rp/--2
  (implies
   (and (rp-evl-meta-extract-global-facts :state state)
        (mult-formula-checks state)
        (rp-termp term)
        (b* ((term (ex-from-rp/-- term))) (case-match term  (('s & &) t))))
   (and (equal (m2 (sum (sum-list (rp-evl (rp-trans (cadr (ex-from-rp/-- term)))
                                          a))
                        (rp-evl (rp-trans (caddr (ex-from-rp/-- term)))
                                a)
                        rest ))
               (m2 (sum (rp-evl (rp-trans term) a) rest)))
        (equal (m2 (sum (sum-list (rp-evl (rp-trans (cadr (ex-from-rp/-- term)))
                                          a))
                        (rp-evl (rp-trans (caddr (ex-from-rp/-- term)))
                                a)))
               (m2 (sum (rp-evl (rp-trans term) a))))
        ))
  :hints (("goal"
           :use ((:instance m2-of-ex-from-rp/--)
                 (:instance m2-of-ex-from-rp/--
                            (rest 0)))
           :in-theory (e/d () (m2-of-ex-from-rp/--
;m2-of-m2
                               s-fix-pp-args-aux-correct-dummy-lemma1)))))

(defthm m2-equals-dummy-lemma
  (implies (equal (m2 (sum x y)) (m2 (sum a b c)))
           (equal (equal (m2 (sum x y other))
                         (m2 (sum a b other c)))
                  t)))

(defthm c/d-merge-fast-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (rp-termp c/d-arg)
                (consp s-arg2)
                (equal (car s-arg2) 'list)
                (consp (cdr s-arg2))
                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc c/d-arg a))
           (b* (((mv s-coughed pp-coughed c/d-merged)
                 (c/d-merge-fast-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg2 s-coughed-from-arg
                                     c/d-arg clean-flg)))
             (and (valid-sc s-coughed a)
                  (valid-sc c/d-merged a)
                  (valid-sc pp-coughed a))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC ''NIL A)
                    (RP-TERMP (CONS 'LIST (CDDR S-ARG2)))
                    (:free (x) (valid-sc (cons 'list x) a)))
           :in-theory (e/d (c/d-merge-fast-aux
                            clean-c/d-args
                            d2-of-times2-reverse)
                           (d2-of-times2
                            (:DEFINITION RP-TERMP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            c/d-merge-slow-aux-correct)))))

(defthm c/d-merge-fast-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp-arg1) (rp-termp pp-arg2)
                (rp-termp pp-coughed-from-arg)
                (rp-termp s-arg2)
                (rp-termp s-coughed-from-arg)
                (rp-termp c/d-arg)
                (consp s-arg2)
                (equal (car s-arg2) 'list)
                (consp (cdr s-arg2))
                (valid-sc pp-arg1 a) (valid-sc pp-arg2 a)
                (valid-sc pp-coughed-from-arg a)
                (valid-sc s-arg2 a)
                (valid-sc s-coughed-from-arg a)
                (valid-sc c/d-arg a))
           (b* (((mv s-coughed pp-coughed c/d-merged)
                 (c/d-merge-fast-aux pp-arg1 pp-arg2 pp-coughed-from-arg
                                     s-arg2 s-coughed-from-arg
                                     c/d-arg clean-flg)))
             (equal (sum (sum-list (rp-evlt s-coughed a))
                         (sum-list (rp-evlt pp-coughed a))
                         (rp-evlt c/d-merged a))
                    (f2 (sum (rp-evlt `(sum-list ,pp-arg1) a)
                             (rp-evlt `(sum-list ,pp-arg2) a)
                             (rp-evlt `(sum-list ,pp-coughed-from-arg) a)
                             (rp-evlt `(sum-list (list . ,(cddr s-arg2))) a)
                             (rp-evlt `(sum-list ,s-coughed-from-arg) a)
                             (rp-evlt c/d-arg a))))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((VALID-SC ''NIL A)
                    (RP-TERMP (CONS 'LIST (CDDR S-ARG2)))
                    (:free (x) (valid-sc (cons 'list x) a)))
           :in-theory (e/d (c/d-merge-fast-aux
                            clean-c/d-args
                            f2-of-times2-reverse
                            d2-of-times2-reverse)
                           (d2-of-times2
                            f2-of-times2
                            (:DEFINITION RP-TERMP)
                            (:REWRITE IS-IF-RP-TERMP)
                            (:DEFINITION VALID-SC)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:DEFINITION TRUE-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            c/d-merge-slow-aux-correct)))))

(local
 (defthm limit-1-to-sum
   (implies (not (zp limit))
            (equal (+ -1 limit)
                   (sum limit -1)))
   :hints (("Goal"
            :in-theory (e/d (zp) ())))))

(defthm m2-of-and$
  (equal (m2 (and$ a b))
         (and$ a b))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(encapsulate
  nil

  ;; (local
  ;;  (skip-proofs
  ;;   (defthm CAN-C-MERGE-FAST-override
  ;;     (equal (CAN-C-MERGE-FAST x y)
  ;;            nil))))

  (local
   (in-theory (e/d (get-c/d-args
                    clean-c/d-args
                    remove-s-from-for-fast-merge
                    sum-of-swap-c/ds-reverse
                    f2-to-d2
                    d2-of-times2-reverse)
                   (RP-EVL-OF-VARIABLE
                    rp-termp
                    is-falist
                    d2-to-f2
                    d2-of-times2
                    D2-OF-MINUS
                    f2-of-minus
                    valid-sc
                    sum-of-swap-c/ds
                    sum-of-swap-c/ds-for-swapped-fncs
                    rp-trans-is-term-when-list-is-absent))))

  (defthm-c/d-merge
    (defthm s-of-s-fix-aux-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-term-listp s-lst)
                    (rp-termp pp)
                    (integerp limit)
                    (rp-termp c/d)
                    (valid-sc-subterms s-lst a)
                    (valid-sc pp a)
                    (valid-sc c/d a))
               (b* (((mv pp-res c/d-res)
                     (s-of-s-fix-aux s-lst pp c/d limit)))
                 (and (equal (m2 (sum (sum-list (rp-evlt pp-res a))
                                      (rp-evlt c/d-res a)))
                             (m2 (sum (sum-list-eval s-lst a)
                                      (sum-list (rp-evlt pp a))
                                      (rp-evlt c/d a))))
                      (valid-sc pp-res a)
                      (valid-sc c/d-res a))))
      :flag s-of-s-fix-aux)

    (defthm s-of-s-fix-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-termp s)
                    (rp-termp pp)
                    (integerp limit)
                    (rp-termp c/d)
                    (valid-sc s a)
                    (valid-sc pp a)
                    (valid-sc c/d a))
               (b* (((mv pp-res c/d-res)
                     (s-of-s-fix s pp c/d limit)))
                 (and (equal (m2 (sum (sum-list (rp-evlt pp-res a))
                                      (rp-evlt c/d-res a)))
                             (m2 (sum (sum-list (rp-evlt s a))
                                      (sum-list (rp-evlt pp a))
                                      (rp-evlt c/d a))))
                      (valid-sc pp-res a)
                      (valid-sc c/d-res a))))
      :flag s-of-s-fix)
    (defthm get-extra-s-arg-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-termp s-arg)
                    (integerp limit)
                    (rp-termp pp-arg)
                    (rp-termp c/d-arg)
                    (valid-sc s-arg a)
                    (valid-sc pp-arg a)
                    (valid-sc c/d-arg a))
               (b* ((extra-s-arg
                     (get-extra-s-arg s-arg pp-arg c/d-arg limit)))
                 (and (equal (rp-evlt extra-s-arg a)
                             (list (-- (m2 (sum (sum-list (rp-evlt s-arg a))
                                                (sum-list (rp-evlt pp-arg a))
                                                (rp-evlt c/d-arg a))))))
                      (valid-sc extra-s-arg a))))
      :flag get-extra-s-arg)
    (defthm c/d-merge-correct
      (implies (and (rp-evl-meta-extract-global-facts :state state)
                    (mult-formula-checks state)
                    (rp-termp c/d1)
                    (integerp limit)
                    (rp-termp c/d2)
                    (valid-sc c/d1 a)
                    (valid-sc c/d2 a))
               (b* (((mv s-coughed pp-coughed c/d-merged)
                     (c/d-merge c/d1 c/d2 clean-flg limit)))
                 (and (valid-sc s-coughed a)
                      (valid-sc pp-coughed a)
                      (valid-sc c/d-merged a)
                      (equal (sum (sum-list (rp-evlt s-coughed a))
                                  (sum-list (rp-evlt pp-coughed a))
                                  (rp-evlt c/d-merged a))
                             (sum (rp-evlt c/d1 a)
                                  (rp-evlt c/d2 a))))))
      :flag c/d-merge)
    :hints (("Subgoal *1/27"
             :use ((:instance can-c-merge-fast-correct
                              (c/d1 (ex-from-rp c/d1))
                              (c/d2 (ex-from-rp c/d2)))
                   (:instance can-c-merge-fast-and-consp
                              (c/d1 (ex-from-rp c/d1))
                              (c/d2 (ex-from-rp c/d2)))))
            ("Subgoal *1/5"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/4"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/3"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/2"
             :use ((:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest 0))))
            ("Subgoal *1/2.1"
             :use ((:instance rid-of-c/d-merge-sum
                              (other (SUM-LIST
                                      (RP-EVL (RP-TRANS (MV-NTH 0
                                                                (S-OF-S-FIX-AUX (CDR S-LST)
                                                                                PP C/D (SUM LIMIT -1))))
                                              A)))
                              (param1 (MV-NTH 1
                                              (S-OF-S-FIX-AUX (CDR S-LST)
                                                              PP C/D (SUM LIMIT -1))))
                              (param2 (CADDR (EX-FROM-RP/-- (CAR S-LST))))
                              (flg nil)
                              (limit (SUM LIMIT -1)))
                   (:instance m2-of-ex-from-rp/--
                              (term (CAR S-LST))
                              (rest (sum (SUM-LIST
                                          (RP-EVL (RP-TRANS (MV-NTH 0
                                                                    (S-OF-S-FIX-AUX (CDR S-LST)
                                                                                    PP C/D (SUM LIMIT -1))))
                                                  A))
                                         (RP-EVL (RP-TRANS (MV-NTH 1
                                                                   (S-OF-S-FIX-AUX (CDR S-LST)
                                                                                   PP C/D (SUM LIMIT -1))))
                                                 A))))))
            ("Subgoal *1/17"
             :use ((:instance c/d-cough-correct
                              (c/d (MV-NTH 1
                                           (S-OF-S-FIX-AUX (CDR S)
                                                           PP C/D (SUM -1
                                                                       LIMIT))))
                              (rest (SUM-LIST
                                     (RP-EVL (RP-TRANS (MV-NTH 0
                                                               (S-OF-S-FIX-AUX (CDR S)
                                                                               PP C/D (+ -1 LIMIT))))
                                             A)))))
             :in-theory (disable c/d-cough-correct))
            ("Goal"
             :do-not-induct t
             :expand ((C/D-MERGE C/D1 C/D2 CLEAN-FLG LIMIT)
                      (S-OF-S-FIX-AUX NIL PP C/D LIMIT)
                      (S-OF-S-FIX-AUX S-LST PP C/D LIMIT)
                      (GET-EXTRA-S-ARG S-ARG PP-ARG C/D-ARG LIMIT)
                      (S-OF-S-FIX S PP C/D LIMIT)
                      (S-OF-S-FIX ''NIL PP C/D LIMIT)
                      (:free (x) (rp-trans (cons 'quote x)))
                      (:free (x) (is-rp (cons 'rp x)))
                      (:free (x) (is-falist (cons 'rp x)))
                      (:free (x) (rp-termp (cons 'list x)))
                      (:free (x) (is-if (cons 'if x)))
                      (:free (x) (GET-C/D-ARGS$INLINE x))
                      (:free (x) (valid-sc (cons 'binary-sum x) a))
                      (:free (x) (valid-sc (cons 'd x) a))
                      (:free (x) (valid-sc (cons 'binary-append x) a))
                      (:free (x) (valid-sc (cons '-- x) a))
                      (:free (x) (valid-sc (cons 'rp x) a))
                      (:free (x) (valid-sc (cons 'd-sum x) a))
                      (:free (x) (valid-sc (cons 'cons x) a))
                      (:free (x) (valid-sc (cons 'c x) a))
                      (:free (x) (valid-sc (cons 's x) a))
                      (:free (x) (valid-sc (cons 'list x) a))
                      (:free (x y) (valid-sc-subterms (cons x y) a)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c/d-merge lemmas

(defthm sum-list-eval-of-quote-all
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval (quote-all lst) a)
                  (sum-list lst)))
  :hints (("goal"
           :induct (quote-all lst)
           :do-not-induct t
           :in-theory (e/d (quote-all
                            SUM-LIST) ()))))

(defthm quotep-valid-sc-subterms
  (valid-sc-subterms (QUOTE-ALL lst) a)
  :hints (("Goal"
           :induct (quote-all lst)
           :do-not-induct t
           :in-theory (e/d (quote-all
                            SUM-LIST) ()))))

(defthmd new-sum-merge-aux-correct-lemma1
  (implies (and (case-match term (('cons & &) t)))
           (equal (rp-evlt (ex-from-rp term) a)
                  (cons (rp-evlt (ex-from-rp (cadr term)) a)
                        (rp-evlt (ex-from-rp (caddr term)) a)))))

(defthmd new-sum-merge-aux-correct-lemma2
  (implies (and (equal (car term) 'quote)
                (RP-TERMP TERM))
           (equal (rp-evlt (ex-from-rp term) a)
                  (unquote term))))

(create-regular-eval-lemma sum-list 1 mult-formula-checks)
(create-regular-eval-lemma c-res 3 mult-formula-checks)

(defthmd
  rp-evlt-of-ex-from-rp-reverse-2
  (implies (syntaxp (or (atom term)))
           (equal (rp-evl (rp-trans term) a)
                  (rp-evl (rp-trans (ex-from-rp term))
                          a))))

(progn
  (defthm is-rp-of-bitp
    (is-rp `(rp 'bitp ,x))
    :hints (("Goal"
             :in-theory (e/d (is-rp) ()))))
  (local
   (create-regular-eval-lemma cons 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-not 1 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-xor 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-or 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-and 2 mult-formula-checks))
  (local
   (create-regular-eval-lemma binary-? 3 mult-formula-checks))

  (local
   (defthm pp-termp-is-bitp-lemma
     (implies (and (PP-HAS-BITP-RP TERM)
                   (rp-evl-meta-extract-global-facts :state state)
                   (VALID-SC TERM A)
                   (MULT-FORMULA-CHECKS STATE))
              (and (BITP (RP-EVLt TERM A))
                   (BITP (RP-EVLt (EX-FROM-RP TERM) A))))
     :hints (("Goal"
              :induct (PP-HAS-BITP-RP TERM)
              :in-theory (e/d (is-if is-rp
                                     PP-HAS-BITP-RP)
                              (bitp
                               NOT-INCLUDE-RP-MEANS-VALID-SC))))))

  (local
   (defthm pp-termp-is-bitp
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (pp-term-p term)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :expand ((PP-TERM-P TERM))
              :in-theory (e/d (pp-term-p

                               is-rp
                               rp-evlt-of-ex-from-rp-reverse-2
                               is-if)
                              (bitp
                               pp-term-p
                               RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               rp-evlt-of-ex-from-rp
                               EX-FROM-RP-LEMMA1
                               rp-evlt-of-ex-from-rp))))))

  (local
   (defthm light-pp-termp-is-bitp
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (LIGHT-PP-TERM-P term)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :expand ((LIGHT-PP-TERM-P TERM))
              :in-theory (e/d (LIGHT-PP-TERM-p
                               is-rp
                               rp-evlt-of-ex-from-rp-reverse-2
                               is-if)
                              (bitp
                               pp-term-p
                               RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               rp-evlt-of-ex-from-rp
                               EX-FROM-RP-LEMMA1
                               rp-evlt-of-ex-from-rp))))))

  (local
   (defthm PP-HAS-BITP-RP-EX-FROM-RP
     (not (PP-HAS-BITP-RP (EX-FROM-RP TERM)))
     :hints (("Goal"
              :induct (EX-FROM-RP TERM)
              :do-not-induct t
              :in-theory (e/d (EX-FROM-RP pp-has-bitp-rp
                                          is-rp) ())))))

  (local
   (defthm pp-termp-of-ex-from-rp
     (implies (pp-term-p (ex-from-rp term))
              (pp-term-p term))
     :hints (("Goal"
              :expand ((PP-TERM-P (EX-FROM-RP TERM))
                       (pp-term-p term))
              :do-not-induct t
              :in-theory (e/d (pp-term-p) ())))))

  (local
   (defthm LIGHT-PP-TERM-P-of-ex-from-rp
     (implies (LIGHT-PP-TERM-P (ex-from-rp term))
              (LIGHT-PP-TERM-P term))
     :hints (("Goal"
              :expand ((LIGHT-PP-TERM-P (EX-FROM-RP TERM))
                       (LIGHT-PP-TERM-P term))
              :do-not-induct t
              :in-theory (e/d (LIGHT-PP-TERM-P) ()))))))

(defthm 4vec->pp-term-valid-sc
  (implies (and (valid-sc term a))
           (valid-sc (4vec->pp-term term) a))
  :hints (("Goal"
           :do-not-induct t
           :induct (4vec->pp-term term)
           :in-theory (e/d (is-rp
                            is-if
                            good-4vec-term-p
                            4vec->pp-term)
                           (pp-term-p
                            (:REWRITE VALID-SC-LEMMA1)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            (:REWRITE VALID-SC-OF-EX-FROM-RP)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:REWRITE VALID-SC-SINGLE-STEP)
                            (:DEFINITION EVAL-AND-ALL)
                            (:DEFINITION EX-FROM-RP)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
;(:REWRITE VALID-SC-CADR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE ATOM-RP-TERMP-IS-SYMBOLP)
                            natp
                            rp-termp
                            include-fnc)))))

(encapsulate
  nil
  (local
   (progn
     (create-regular-eval-lemma svl::bits 3 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-bitnot$ 2 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-bitand 2 mult-formula-checks)
     (create-regular-eval-lemma sv::4vec-bitxor 2 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-bitor 2 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-? 3 mult-formula-checks)

     (create-regular-eval-lemma sv::3vec-fix 1 mult-formula-checks)
     (create-regular-eval-lemma svl::4vec-?* 3 mult-formula-checks)))

  (local
   (create-regular-eval-lemma sv::4vec-fix$inline 1 mult-formula-checks))

  (local
   (encapsulate
     nil

     (local
      (include-book "centaur/bitops/ihsext-basics" :dir :system))

     (defthmd bits-is-bit-of
       (implies (and (natp start)
                     (integerp num)
                     (equal size 1))
                (equal (svl::bits num start size)
                       (bit-of num start)))
       :hints (("Goal"
                :in-theory (e/d (svl::bits
                                 bit-of
                                 SV::4VEC-SHIFT-CORE
                                 SV::4VEC-RSH
                                 SV::4VEC->UPPER
                                 SV::4VEC->LOWER
                                 SV::4VEC-PART-SELECT
                                 SV::4VEC-ZERO-EXT)
                                (SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                                 +-IS-SUM
                                 FLOOR2-IF-F2
                                 MOD2-IS-M2)))))))

  (progn
    (local
     (defthm 4vec-bitnot$-is-not$
       (implies (bitp num)
                (equal (svl::4vec-bitnot$ 1 num)
                       (not$ num)))))
    (local
     (defthm 4vec-fix$-when-bitp
       (implies (bitp num)
                (equal (sv::4vec-fix num)
                       num))))

    (local
     (defthm 3vec-fix$-when-bitp
       (implies (bitp num)
                (equal (sv::3vec-fix num)
                       num))))

    (local
     (defthm 4vec-bitand-is-and$
       (implies (and (bitp num)
                     (bitp num2))
                (equal (svl::4vec-bitand num num2)
                       (and$ num num2)))))

    (local
     (defthm 4vec-bitor-is-or$
       (implies (and (bitp num)
                     (bitp num2))
                (equal (svl::4vec-bitor num num2)
                       (or$ num num2)))))

    (local
     (defthm 4vec-bitxor-is-binary-xor
       (implies (and (bitp num)
                     (bitp num2))
                (equal (sv::4vec-bitxor num num2)
                       (binary-xor num num2)))))

    (local
     (defthm 4vec-?-is-binary-?
       (implies (and (bitp num)
                     (bitp num2)
                     (bitp num3))
                (and (equal (svl::4vec-? num num2 num3)
                            (binary-? num num2 num3))
                     (equal (svl::4vec-?* num num2 num3)
                            (binary-? num num2 num3)))))))

  (local
   (defthm 4vec->pp-term-correct-bitp-lemma
     (implies (and (valid-sc term a)
                   (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (good-4vec-term-p term)
                   (equal (rp-evlt (4vec->pp-term term) a)
                          (rp-evlt term a)))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d () (bitp
                                  pp-term-p))))))

  (local
   (encapsulate
     nil

     (local
      (in-theory (e/d (valid-sc-single-step is-rp)
                      (bitp
                       rp-trans
                       rp-termp
                       not-include-rp-means-valid-sc
                       valid-sc
                       VALID-SC-EX-FROM-RP
                       VALID-SC-OF-EX-FROM-RP
                       rp-evl-of-variable))))

     (defthm 4vec->pp-term-correct-bitp-lemma-2
       (implies (and (valid-sc term a)
                     (rp-evl-meta-extract-global-facts :state state)
                     (mult-formula-checks state)
                     (good-4vec-term-p term)
                     (b* ((term (ex-from-rp term)))
                       (case-match term (('svl::bits & & &) t))))
                (integerp (rp-evl (rp-trans (caddr (cadr (ex-from-rp term)))) a)))
       :otf-flg t
       :hints (("Subgoal 1"
                :expand ((VALID-SC (EX-FROM-RP TERM) A)
                         (GOOD-4VEC-TERM-P TERM)))
               ("Subgoal 2"
                :in-theory (e/d (VALID-SC-EX-FROM-RP)
                                ()))
               ("goal"
                :do-not-induct t
                :expand ((good-4vec-term-p term))
                :cases ((valid-sc (ex-from-rp term) a)))))))

  (defthm 4vec->pp-term-correct
    (implies (and (valid-sc term a)
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (good-4vec-term-p term))
             (equal (rp-evlt (4vec->pp-term term) a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :do-not-induct t
             :induct (4vec->pp-term term)
             :expand ((:free (x) (nth 3 x))
                      (:free (x) (nth 2 x))
                      (:free (x) (nth 1 x)))
             :in-theory (e/d (4vec->pp-term
                              rp-evlt-of-ex-from-rp-reverse-2
                              bits-is-bit-of
                              good-4vec-term-p
                              )
                             (pp-term-p
                              rp-termp
                              (:DEFINITION VALID-SC)
                              (:DEFINITION INCLUDE-FNC)
                              (:REWRITE VALID-SC-LEMMA1)
                              (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                              (:DEFINITION ACL2::APPLY$-BADGEP)
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                              (:DEFINITION EX-FROM-RP)
                              (:REWRITE DEFAULT-CDR)
                              (:DEFINITION SUBSETP-EQUAL)
                              (:DEFINITION MEMBER-EQUAL)
                              (:REWRITE PP-TERMP-OF-EX-FROM-RP)
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                              (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                              (:REWRITE NOT-INCLUDE-RP)
                              (:REWRITE
                               ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                              (:REWRITE DEFAULT-CAR)
                              (:DEFINITION EVAL-AND-ALL)
                              (:DEFINITION RP-TERM-LISTP)
                              (:DEFINITION TRUE-LISTP)
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:DEFINITION QUOTEP)
                              natp
                              bitp
                              rp-evlt-of-ex-from-rp))))))

(defthm new-sum-merge-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (well-formed-new-sum term)
                (rp-termp term))
           (b* (((mv s pp c/d)
                 (new-sum-merge-aux term)))
             (and (equal (sum (sum-list (rp-evlt s a))
                              (sum-list (rp-evlt pp a))
                              (rp-evlt c/d a))
                         (sum-list (rp-evlt term a)))
                  (valid-sc s a)
                  (valid-sc pp a)
                  (valid-sc c/d a))))
  :hints (("Goal"
           :do-not-induct t
           :induct (new-sum-merge-aux term)
           :expand ((:free (x) (valid-sc (cons 'list x) a))
                    (well-formed-new-sum term)
                    (valid-SC ''NIL A)
                    (VALID-SC ''0 A)
                    (:free (x) (rp-termp (cons 'list x))))
           :in-theory (e/d (new-sum-merge-aux
                            c-res
                            RP-EVLT-OF-EX-FROM-RP-REVERSE-2
                            new-sum-merge-aux-correct-lemma1
                            new-sum-merge-aux-correct-lemma2
;WELL-FORMED-NEW-SUM
                            )
                           (valid-sc
                            (:REWRITE IS-IF-RP-TERMP)
                            (:TYPE-PRESCRIPTION O<)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            ;;(:DEFINITION WELL-FORMED-NEW-SUM)
                            rp-evlt-of-ex-from-rp
                            rp-termp
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:TYPE-PRESCRIPTION WELL-FORMED-NEW-SUM)
                            (:REWRITE DEFAULT-CAR)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            (:DEFINITION PP-TERM-P)
                            (:TYPE-PRESCRIPTION SUM-LIST)
                            (:TYPE-PRESCRIPTION RP-TERMP)
                            (:DEFINITION EX-FROM-RP)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION IS-RP$INLINE))))))

#|(defthm new-sum-merge-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (well-formed-new-sum term)
                (rp-termp term))
           (b* (((mv s pp c/d)
                 (new-sum-merge term)))
             (and (equal (sum (sum-list (rp-evlt s a))
                              (sum-list (rp-evlt pp a))
                              (rp-evlt c/d a))
                         (sum-list (rp-evlt term a)))
                  (valid-sc s a)
                  (valid-sc pp a)
                  (valid-sc c/d a))))
  :hints (("Goal"
:in-theory (e/d (new-sum-merge) ()))))||#

(defthm f2-of-quarternaryp
  (implies (quarternaryp sum)
           (bitp (f2 sum)))
  :hints (("Goal"
           :in-theory (e/d (quarternaryp) ()))))

(encapsulate
  nil

  (local
   (define maxp (val (max natp))
     :measure (nfix max)
     :prepwork
     ((Local
       (in-theory (e/d ()  (+-is-sum limit-1-to-sum)))))
     (if (zp max)
         (equal val 0)
       (or (equal val max)
           (maxp val (1- max))))))

  (local
   (defthm maxp-lemma1
     (implies (and (natp x)
                   (natp y)
                   (<= x y))
              (maxp x y))
     :hints (("Goal"
              :induct (maxp x y)
              :in-theory (e/d (maxp)
                              (LIMIT-1-TO-SUM
                               +-is-sum))))))

  (local
   (defthmd
     rp-evlt-of-ex-from-rp-reverse-3
     (implies (and (syntaxp (equal term '(car (cdr term))))
                   (or (not (equal (car term) 'rp))
                       (EQUAL (CAR (EX-FROM-RP term))
                              'S)))
              (equal (rp-evl (rp-trans term) a)
                     (rp-evl (rp-trans (ex-from-rp term))
                             a)))))

  (local
   (defthm lemma1
     (implies (EQUAL (EX-FROM-RP term) ''0)
              (equal (RP-EVL (RP-TRANS term) A)
                     0))
     :hints (("Goal"
              :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse)
                              (rp-evlt-of-ex-from-rp))))))

  (local
   (defthmd maxp-of-bitp-lemma
     (implies (and (not (zp max))
                   (not (zp x)))
              (equal (maxp x max)
                     (maxp (1- x) (1- max))))
     :hints (("Goal"
              :induct (maxp x max)
              :do-not-induct t
              :in-theory (e/d (maxp sum)
                              (+-is-sum
                               LIMIT-1-TO-SUM
                               natp))))))

  (local
   (defthm maxp-of-bitp
     (implies (and (bitp x)
                   (not (zp max))
                   (maxp (ifix rest) (1- max)))
              (and (maxp (sum x rest) max)
                   (maxp (sum rest x) max)))
     :hints (("Goal"
              :use ((:instance maxp-of-bitp-lemma
                               (x (sum x rest))))
              :in-theory (e/d (maxp sum)
                              (+-is-sum
                               LIMIT-1-TO-SUM
                               natp))))))

  (Local
   (defthm lemma2
     (implies (natp x)
              (NOT (ZP (SUM x 1))))
     :hints (("Goal"
              :in-theory (e/d (sum)
                              (+-is-sum))))))

  (local
   (defthm lemma3
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (case-match term (('rp ''bitp &) t)))
              (and (bitp (rp-evlt term a))
                   (bitp (rp-evlt (ex-from-rp term) a))
                   (bitp (rp-evlt (caddr term) a))))
     :hints (("Goal"
              :in-theory (e/d () (bitp))))))

  (local
   (defthm lemma4
     (implies (NAT-LISTP lst)
              (natp (sum-list lst)))
     :hints (("Goal"
              :induct (sum-list lst)
              :do-not-induct t
              :in-theory (e/d (sum-list
                               nat-listp
                               sum)
                              (+-is-sum))))
     :rule-classes (:type-prescription :rewrite)))

  (local
   (defthm quarternaryp-sum-aux-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-termp term))
              (b* (((mv res valid)
                    (quarternaryp-sum-aux term)))
                (implies valid
                         (maxp (sum-list (rp-evlt term a))
                               res))))
     :hints (("Goal"
              :do-not-induct t
              :induct (quarternaryp-sum-aux term)
              :in-theory (e/d (quarternaryp-sum-aux
                               SUM-LIST
                               rp-evlt-of-ex-from-rp-reverse-3)
                              (natp
                               REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS
                               zp
                               REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS
                               rp-evlt-of-ex-from-rp
                               ex-from-rp-lemma1
                               RP-EVL-OF-VARIABLE
                               RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               ex-from-rp
                               ex-from-rp-loose
                               valid-sc
                               rp-termp))))))

  (local
   (defthm quarternaryp-is-maxp
     (equal (quarternaryp x)
            (maxp x 3))
     :hints (("Goal"
              :in-theory (e/d (quarternaryp maxp) ())))))

  (local
   (defthm maxp-trans
     (implies (and (maxp x y)
                   (maxp y z))
              (maxp x z))
     :hints (("Goal"
              :in-theory (e/d (maxp) ())))))

  (defthm quarternaryp-sum-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc term a)
                  (rp-termp term)
                  (quarternaryp-sum term))
             (quarternaryp (sum-list (rp-evlt term a))))
    :hints (("Goal"
             :use ((:instance maxp-trans
                              (z 3)
                              (y (MV-NTH 0 (quarternaryp-sum-aux TERM)))
                              (x (SUM-LIST (RP-EVL (RP-TRANS TERM) A)))))
             :in-theory (e/d (quarternaryp-sum
                              quarternaryp-sum-aux-correct)
                             (natp
                              maxp-trans
                              quarternaryp-sum-aux
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS
                              zp
                              REGULAR-RP-EVL-OF_C-RES_WHEN_MULT-FORMULA-CHECKS
                              rp-evlt-of-ex-from-rp
                              ex-from-rp-lemma1
                              RP-EVL-OF-VARIABLE
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                              ex-from-rp
                              ex-from-rp-loose
                              valid-sc
                              rp-termp))))))

(defthm contet-from-create-c-instance
  (equal (CONTEXT-FROM-RP (CREATE-C-INSTANCE a b c) context)
         context)
  :hints (("Goal"
           :in-theory (e/d (CREATE-C-INSTANCE
                            is-rp) ()))))

(defthm c-spec-meta-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c/d a)
                (rp-termp s)
                (rp-termp pp)
                (if quarternaryp
                    (quarternaryp (sum (sum-list (rp-evlt s a))
                                       (sum-list (rp-evlt pp a))
                                       (rp-evlt c/d a)))
                  t)
                (rp-termp c/d))
           (and (equal (rp-evlt (c-spec-meta-aux s pp c/d quarternaryp) a)
                       (f2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (rp-evlt c/d a))))
                (valid-sc (c-spec-meta-aux s pp c/d quarternaryp) a)))
  :hints (("Goal"
           :use ((:instance c/d-fix-s-args-correct
                            (rest 0)
                            (pp (S-SUM-MERGE (MV-NTH 0 (C/D-COUGH C/D))
                                             S)))
                 (:instance c/d-fix-pp-args-correct
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                      PP)))
                            (rest (SUM-LIST (RP-EVL (RP-TRANS S) A)))
                            (limit (MV-NTH 1
                                           (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                         PP))))
                 (:instance c/d-fix-pp-args-correct
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                      PP)))
                            (rest 0)
                            (limit (MV-NTH 1
                                           (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                         PP))))
                 (:instance c/d-fix-pp-args-correct
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                      PP)))
                            (rest (SUM-LIST
                                   (RP-EVL
                                    (RP-TRANS
                                     (MV-NTH 1
                                             (C/D-FIX-S-ARGS (S-SUM-MERGE (MV-NTH 0 (C/D-COUGH C/D))
                                                                          S))))
                                    A)))
                            (limit (MV-NTH 1
                                           (PP-SUM-MERGE (MV-NTH 1 (C/D-COUGH C/D))
                                                         PP)))))
           :in-theory (e/d (c-spec-meta-aux
                            c-res
                            times2
                            f2-of-times2-reverse)
                           (c/d-fix-s-args-correct
                            bitp
                            c/d-fix-pp-args-correct
                            C/D-FIX-PP-ARGS
                            f2-of-times2)))))

(defthm c-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (equal (rp-evlt (mv-nth 0 (c-spec-meta term)) a)
                       (rp-evlt term a))
                (valid-sc (mv-nth 0 (c-spec-meta term)) a)))
  :hints (("Goal"
           :cases ((quarternaryp-sum (CADR TERM)))
           :in-theory (e/d (c-spec-meta
                            new-sum-merge) ()))))

(defthm m2-of-and$
  (equal (m2 (and$ a b))
         (and$ a b))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthm create-s-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc pp a))
                (force (valid-sc c/d a))
                (force (rp-termp pp))
                (force (rp-termp c/d)))
           (and (equal (rp-evlt (create-s-instance pp c/d) a)
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (rp-evlt c/d a))))
                (valid-sc (create-s-instance pp c/d) a)))
  :hints (("Goal"
           :in-theory (e/d (create-s-instance) ()))))

(defthm m2-equals-dummy-lemma2
  (implies (and (equal (m2 a) (m2 b))
                (syntaxp (> (cons-count a)
                            (cons-count b))))
           (equal (equal (m2 (sum x a)) (m2 other))
                  (equal (m2 (sum x b)) (m2 other)))))

(defthm s-spec-meta-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc c/d a)
                (rp-termp s)
                (rp-termp pp)
                (rp-termp c/d))
           (and (equal (rp-evlt (s-spec-meta-aux s pp c/d) a)
                       (m2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (rp-evlt c/d a))))
                (valid-sc (s-spec-meta-aux s pp c/d) a)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance s-of-s-fix-correct
                            (s (MV-NTH 0 (C/D-COUGH C/D)))
                            (pp (MV-NTH 0
                                        (PP-SUM-MERGE PP (MV-NTH 1 (C/D-COUGH C/D)))))
                            (c/d (MV-NTH 2 (C/D-COUGH C/D)))
                            (limit (EXPT 2 40)))
                 (:instance s-of-s-fix-correct
                            (s s)
                            (pp pp)
                            (c/d c/d)
                            (limit (EXPT 2 40)))
                 (:instance s-fix-args-correct
                            (term (MV-NTH
                                   0
                                   (S-OF-S-FIX (MV-NTH 0 (C/D-COUGH C/D))
                                               (MV-NTH 0
                                                       (PP-SUM-MERGE PP (MV-NTH 1 (C/D-COUGH C/D))))
                                               (MV-NTH 2 (C/D-COUGH C/D))
                                               1099511627776)))
                            (c/d 0))
                 (:instance s-fix-args-correct
                            (term (MV-NTH 0 (S-OF-S-FIX S PP C/D 1099511627776)))
                            (c/d 0)))

           :in-theory (e/d (s-spec-meta-aux
                            create-s-instance-correct
                            s)
                           (s-of-s-fix-correct
                            s-fix-args-correct
                            NOT-INCLUDE-RP-MEANS-VALID-SC
                            RP-EVL-OF-VARIABLE)))))

(defthm s-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (equal (rp-evlt (mv-nth 0 (s-spec-meta term)) a)
                       (rp-evlt term a))
                (valid-sc (mv-nth 0 (s-spec-meta term)) a)))
  :hints (("Goal"
           :in-theory (e/d (s-spec-meta
                            new-sum-merge) ()))))

(create-regular-eval-lemma s-c-spec 1 mult-formula-checks)
(create-regular-eval-lemma c-s-spec 1 mult-formula-checks)

(defthm context-from-rp-of-c-spec-meta-aux
  (equal (CONTEXT-FROM-RP (C-SPEC-META-AUX a b c nil) context)
         context)
  :hints (("Goal"
           :expand (C-SPEC-META-AUX a b c nil)
           :in-theory (e/d () ()))))

(defthm s-c-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (equal (rp-evlt (mv-nth 0 (s-c-spec-meta term)) a)
                       (rp-evlt term a))
                (valid-sc (mv-nth 0 (s-c-spec-meta term)) a)))
  :hints (("Goal"
           :cases ((quarternaryp-sum (CADR TERM)))
           :in-theory (e/d (s-c-spec-meta
                            new-sum-MERGE)
                           (bitp)))))

;; (defthm c-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 'c-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc
;;                             )))))

;; (defthm s-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 's-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm s-c-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 's-c-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm c-s-spec-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 's-c-spec-meta
;;                              :trig-fnc 'c-s-spec
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))

;; (defthm sort-sum-meta-valid-rp-meta-rulep
;;   (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (let ((rule (make rp-meta-rule-rec
;;                              :fnc 'sort-sum-meta
;;                              :trig-fnc 'sort-sum
;;                              :dont-rw t
;;                              :valid-syntax t)))
;;              (and (valid-rp-meta-rulep rule state)
;;                   (rp-meta-valid-syntaxp-sk rule state))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-meta-valid-syntaxp)
;;                            (rp-termp
;;                             rp-term-listp
;;                             valid-sc)))))
