; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
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

(include-book "lemmas")

(include-book "summation-tree-meta-fncs")

(include-book "pp-flatten-meta-correct")

(include-book "sum-merge-fncs-correct")

(include-book "lemmas-2")

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
(create-regular-eval-lemma s-c-res 3 mult-formula-checks)
(create-regular-eval-lemma and-list 2 mult-formula-checks)
(create-regular-eval-lemma -- 1 mult-formula-checks)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get-max-min-val

(local
 (in-theory (disable (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                     (:DEFINITION RP-TERM-LISTP)
                     (:DEFINITION RP-TERMP)
                     (:DEFINITION EX-FROM-RP)
                     (:REWRITE NOT-INCLUDE-RP)
                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1))))

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

(progn
  (defun find-common-sum-item (x y)
    (declare (ignorable x y)
             (xargs :measure (+ (acl2-count x)
                                (acl2-count y))
                    :otf-flg nil
                    :hints (("Goal"
                             :do-not-induct t
                             :in-theory (e/d (rw-dir2)
                                             (rw-dir1
                                              +-IS-SUM))))))
    (b* (((mv cur-x rest-x) (case-match x
                              (('binary-sum cur-x rest-x)
                               (mv cur-x rest-x))
                              (('ifix cur-x)
                               (mv cur-x nil))
                              (& (mv x nil))))
         ((mv cur-y rest-y) (case-match y
                              (('binary-sum cur-y rest-y)
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
                             (+-IS-SUM))))))

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

(defthm lte-implies-not-gt
  (implies (lte a b)
           (not (gt a b)))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))

(defthm when-ex-from-rp-is-1
  (implies (EQUAL (EX-FROM-RP TERM) ''1)
           (and (equal (rp-evlt term a) 1)
                (equal (rp-evl term a) 1)))
  :hints (("Goal"
           :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse
                            rp-evl-of-ex-from-rp-reverse-for-atom)
                           (RP-EVLT-OF-EX-FROM-RP
                            RP-EVL-OF-EX-FROM-RP
                            ex-from-rp)))))

(defthmd when-ex-from-rp-is-0
  (implies (EQUAL (EX-FROM-RP TERM) ''0)
           (and (equal (rp-evlt term a) 0)
                (equal (rp-evl term a) 0)))
  :hints (("Goal"
           :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse
                            rp-evl-of-ex-from-rp-reverse-for-atom)
                           (RP-EVLT-OF-EX-FROM-RP
                            RP-EVL-OF-EX-FROM-RP
                            ex-from-rp)))))

(defthm VALID-SC-SUBTERMS-CONS-fc
  (implies (and (VALID-SC-SUBTERMS LST A)
                (CONSP LST))
           (AND (VALID-SC (CAR LST) A)
                (VALID-SC-SUBTERMS (CDR LST) A)))
  :rule-classes :forward-chaining)

(defthmd bitp-implies-integerp
  (implies (bitp x)
           (integerp x)))

(create-regular-eval-lemma binary-or 2 mult-formula-checks)
(create-regular-eval-lemma binary-? 3 mult-formula-checks)
(create-regular-eval-lemma binary-and 2 mult-formula-checks)
(create-regular-eval-lemma binary-xor 2 mult-formula-checks)
(create-regular-eval-lemma binary-not 1 mult-formula-checks)

(defthmd binary-fnc-p-implies-integerp-eval
  (implies (and (or (binary-fnc-p (ex-from-rp term))
                    (binary-fnc-p term))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (integerp (rp-evlt term a))
                (integerp (rp-evlt (ex-from-rp term) a))))
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d* (binary-fnc-p
                             (:rewrite regular-rp-evl-of_binary-?_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_binary-?_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite regular-rp-evl-of_binary-and_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite regular-rp-evl-of_binary-not_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_binary-not_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite regular-rp-evl-of_binary-or_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_binary-or_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite regular-rp-evl-of_binary-xor_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_binary-xor_when_mult-formula-checks_with-ex-from-rp)
                             binary-?-p
                             binary-not-p
                             binary-or-p)
                            ()))))

(defthmd bitp-binary-fnc-p
  (implies (and (or (binary-fnc-p (ex-from-rp term))
                    (binary-fnc-p term))
                (rp-evl-meta-extract-global-facts :state state)

                (mult-formula-checks state))
           (and (bitp (rp-evlt term a))
                (bitp (rp-evlt (ex-from-rp term) a))))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d (binary-fnc-p
                            (:rewrite regular-rp-evl-of_binary-?_when_mult-formula-checks)
                            (:rewrite
                             regular-rp-evl-of_binary-?_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite regular-rp-evl-of_binary-and_when_mult-formula-checks)
                            (:rewrite
                             regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite regular-rp-evl-of_binary-not_when_mult-formula-checks)
                            (:rewrite
                             regular-rp-evl-of_binary-not_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite regular-rp-evl-of_binary-or_when_mult-formula-checks)
                            (:rewrite
                             regular-rp-evl-of_binary-or_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite regular-rp-evl-of_binary-xor_when_mult-formula-checks)
                            (:rewrite
                             regular-rp-evl-of_binary-xor_when_mult-formula-checks_with-ex-from-rp)
                            binary-?-p
                            binary-not-p
                            binary-or-p)
                           (bitp
                            rp-trans
                            rp-trans-lst
                            NOT-INCLUDE-RP-MEANS-VALID-SC)))))

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
          :in-theory (e/d* (get-max-min-val
                            RP-TRANS-LST-of-consp
                            RP-TRANS-LST
                            RP-TRANS
                            regular-eval-lemmas-with-ex-from-rp
                            ;;rp-evlt-of-ex-from-rp-reverse
                            minus-to---
                            get-max-min-val-lst
                            binary-fnc-p-implies-integerp-eval
                            bitp-binary-fnc-p
                            bitp-implies-integerp)
                           (;;RP-EVLT-OF-EX-FROM-RP
                            (:DEFINITION EQ)

                            (:DEFINITION NOT)
                            (:REWRITE VALID-SC-SUBTERMS-CONS)
                            (:REWRITE GE-CHAIN-SMART)
                            (:DEFINITION RP-TRANS)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            include-fnc
                            valid-sc
                            rp-trans
                            rp-termp
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S-C-RES_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
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
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S-C-RES_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            valid-sc
                            (:REWRITE
                             REGULAR-RP-EVL-OF_BINARY-AND_WHEN_MULT-FORMULA-CHECKS)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:REWRITE F2-OF-BIT)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            bitp)))))

(defret
  get-max-min-val-correct-with-lte
  (implies (and valid
                (rp-evl-meta-extract-global-facts :state state)
                (valid-sc term a)
                (mult-formula-checks state))
           (and (integerp (rp-evlt term a))
                (lte (rp-evlt term a)
                    max-val)
                (lte min-val
                    (rp-evlt term a))))
  :fn get-max-min-val
  :rule-classes :forward-chaining
  :hints (("Goal"
           :use ((:instance get-max-min-val-correct))
           :in-theory (e/d () ()))))

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
       (not (is-rp (cons 's-c-res rest)))
       (not (is-rp (cons '-- rest)))
       (not (is-rp (cons 'list rest)))
       (not (is-rp (cons 's rest))))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm is-if-of-s-c-list
  (and (not (is-if (cons 'c rest)))
       (not (is-if (cons 's-c-res rest)))
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

#|(defthm decompress-s-c-correct-lemma1
  (implies (valid-sc term a)
           (and (b* (((mv pp ?valid)
                      (|CASE-MATCH-('c & ''nil pp ''nil)| term)))
                  (valid-sc pp a))))
  :hints (("Goal"
           :in-theory (e/d (|CASE-MATCH-('c & ''nil pp ''nil)|)
                           ()))))||#

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

(defthm dummy-sum-lemma3
  (and (equal (equal (sum x y z a)
                     (sum p a))
              (equal (sum x y z)
                     (sum p)))))

(defret
  decompress-s-c-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a))
           (and (valid-sc res-term a)
                (valid-sc coughed-s a)
                (valid-sc coughed-pp a)
                (equal (sum (rp-evlt res-term a)
                            (sum-list (rp-evlt coughed-s a))
                            (sum-list (rp-evlt coughed-pp a)))
                       (ifix (rp-evlt term a)))
                (equal (sum (rp-evlt res-term a)
                            (sum-list (rp-evlt coughed-s a))
                            (sum-list (rp-evlt coughed-pp a))
                            other)
                       (sum (rp-evlt term a)
                            other))))
  :fn decompress-s-c
  :hints (("Goal"
           :do-not-induct t
           :induct (decompress-s-c term :limit limit)
           :in-theory (e/d (decompress-s-c
                            equivalence-of-two-f2-2
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
                           (valid-sc (cons x y) a))
                    #|(:free (x y)
                    (valid-sc-subterms (cons x y) a))||#)
           :induct (light-compress-s-c$pass-pp-lst pp1-lst pp2-lst :pp-flg pp-flg)
           :in-theory (e/d* (light-compress-s-c$pass-pp-lst
                             SUM-LIST-EVAL-when-consp
                             ;;regular-eval-lemmas
                             (:REWRITE REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
                             abs-term)

                            (rp-trans-lst
                             ;; VALID-SC-SUBTERMS-CONS
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
                              REGULAR-RP-EVL-OF_s-C-RES_WHEN_MULT-FORMULA-CHECKS)
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
           :induct (ligth-compress-s-c$fix-pp-lst$for-s pp1-lst pp2-lst :pp-flg
                                                        pp-flg)
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
                             (and (equal (car term) 'car)
                                  (not (include-fnc term 'ex-from-rp )))))
                (EQUAL (RP-EVL (RP-TRANS TERM) A)
                       (RP-EVL (RP-TRANS (EX-FROM-RP TERM))
                               A)))
       (IMPLIES (SYNTAXP (not (or (ATOM TERM)
                                  (and (equal (car term) 'car)
                                       (not (include-fnc term 'ex-from-rp ))))))
                (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)
                       (RP-EVL (RP-TRANS TERM) A)))))

(defret light-compress-s-c-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc s a)
                (valid-sc c-arg a))
           (and (valid-sc pp-res a)
                (valid-sc s-res a)
                (valid-sc c-arg-res a)
                (equal (sum (sum-list (rp-evlt pp-res a))
                            (sum-list (rp-evlt s-res a))
                            (sum-list (rp-evlt c-arg-res a)))
                       (sum (sum-list (rp-evlt pp a))
                            (sum-list (rp-evlt s a))
                            (sum-list (rp-evlt c-arg a))))))
  :fn light-compress-s-c-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (light-compress-s-c-aux pp s c-arg)
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
           :expand ((:free (rest) (VALID-SC (cons 'c rest) a))
                    (:free (rest) (VALID-SC (cons 's rest) a)))
           :use ((:instance light-compress-s-c-aux-correct
                            (pp (LIGHT-COMPRESS-S-C$FIX-PP$FOR-S
                                 (CADDR (EX-FROM-RP TERM))
                                 (CADDDR (EX-FROM-RP (CADR (CADDDR (EX-FROM-RP TERM)))))
                                 :PP-FLG T))
                            (s ''nil)
                            (c-arg (CADDDR (EX-FROM-RP TERM)))))

           :in-theory (e/d (light-compress-s-C
                            rp-trans-lst-of-consp
                            rp-evlt-of-ex-from-rp-reverse-only-atom)
                           (ex-from-rp
                            (:DEFINITION VALID-SC)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION TRANS-LIST)
                            rp-evlt-of-ex-from-rp
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-pattern1-reduce  lemmas

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

(defret negate-lst-aux-correct
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

(defret negate-lst-correct-
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (and (valid-sc-subterms negated-lst a)
                (equal (sum-list-eval negated-lst a)
                       (if enabled
                           (-- (sum-list-eval lst a))
                         (sum-list-eval lst a)))))
  :fn negate-lst
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (negate-lst
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

(defthm c-pattern1-reduce-correct-lemma
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

(defthmd when-sum-of-two-is-equal-to-0
  (equal (equal 0 (sum a b))
         (and (equal (-- a) (sum b))
              (equal (sum a) (-- b))))
  :hints (("Goal"
           :in-theory (e/d (sum --) (+-IS-SUM)))))

(defthmd dummy-f2-move-over-lemma
  (equal (equal (sum (-- a) (-- b) c) (sum x))
         (equal (sum c) (sum a b x)))
  :hints (("Goal"
           :in-theory (e/d (sum --) (+-IS-SUM)))))

(defthm f2-of-minus-2
  (EQUAL (F2 (SUM c (-- A) B))
         (SUM (-- A) (F2 (SUM c A B)))))

(defret c-pattern1-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (valid-sc-subterms s-res-lst a)
                (valid-sc-subterms pp-res-lst a)
                (valid-sc-subterms c-res-lst a)
                (equal (f2 (sum (sum-list-eval s-res-lst  a)
                                (sum-list-eval pp-res-lst  a)
                                (sum-list-eval c-res-lst  a)))
                       (f2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))))
  :fn c-pattern1-reduce
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance decompress-s-c-correct
                            (term (CADR
                                   (CAR (CDDDDR (LIGHT-COMPRESS-S-C
                                                 (LIST 'C
                                                       ''0
                                                       (CREATE-LIST-INSTANCE (NEGATE-LST S-LST T))
                                                       (CREATE-LIST-INSTANCE (NEGATE-LST PP-LST T))
                                                       (CREATE-LIST-INSTANCE C-LST)))))))
                            (limit 1073741824)
                            (other (sum (SUM-LIST-EVAL PP-LST A)
                                        (SUM-LIST-EVAL s-LST A))))
                 (:instance s-SUM-MERGE-AUX-CORRECT
                            (term1 s-lst)
                            (term2 (LIST-TO-LST
                                    (MV-NTH
                                     1
                                     (DECOMPRESS-S-C
                                      (CADR
                                       (CAR (CDDDDR (LIGHT-COMPRESS-S-C
                                                     (LIST 'C
                                                           ''0
                                                           (CREATE-LIST-INSTANCE (NEGATE-LST S-LST T))
                                                           (CREATE-LIST-INSTANCE (NEGATE-LST PP-LST T))
                                                           (CREATE-LIST-INSTANCE C-LST))))))
                                      :LIMIT 1073741824)))))
                 (:instance PP-SUM-MERGE-AUX-CORRECT
                            (term1 pp-lst)
                            (term2 (LIST-TO-LST
                                    (MV-NTH
                                     2
                                     (DECOMPRESS-S-C
                                      (CADR
                                       (CAR (CDDDDR (LIGHT-COMPRESS-S-C
                                                     (LIST 'C
                                                           ''0
                                                           (CREATE-LIST-INSTANCE (NEGATE-LST S-LST T))
                                                           (CREATE-LIST-INSTANCE (NEGATE-LST PP-LST T))
                                                           (CREATE-LIST-INSTANCE C-LST))))))
                                      :LIMIT 1073741824)))))
                 (:instance light-compress-s-c-correct
                            (term (LIST 'C
                                        ''0
                                        (CREATE-LIST-INSTANCE (NEGATE-LST S-LST T))
                                        (CREATE-LIST-INSTANCE (NEGATE-LST PP-LST T))
                                        (CREATE-LIST-INSTANCE C-LST))))
                 )
           :expand ((VALID-SC ''NIL A)
                    (VALID-SC ''0 A)
                    (:free (x) (valid-sc (cons 'c x) a))
                    (:free (x) (valid-sc (cons 's x) a)))
           ;;:case-split-limitations (10 1)
           :do-not '()
           :in-theory (e/d (c-pattern1-reduce
                            when-sum-of-two-is-equal-to-0
                            dummy-f2-move-over-lemma
                            f2-of-minus
                            rp-trans-lst-of-consp)
                           (ex-from-rp
                            ;; rp-trans
                            (:DEFINITION VALID-SC)
                            (:TYPE-PRESCRIPTION PP-LST-SUBSETP-FN)
                            (:TYPE-PRESCRIPTION LIGHT-COMPRESS-S-C)
                            (:TYPE-PRESCRIPTION F2)
                            (:TYPE-PRESCRIPTION SUM-LIST)
                            (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                            (:TYPE-PRESCRIPTION SUM-LIST-EVAL)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE RP-EVL-OF-VARIABLE)

                            s-SUM-MERGE-AUX-CORRECT
                            PP-SUM-MERGE-AUX-CORRECT

                            ;;(:DEFINITION VALID-SC)
                            ;;(:DEFINITION SUM-LIST-EVAL)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:REWRITE GET-MAX-MIN-VAL-CORRECT)
                            (:TYPE-PRESCRIPTION --)
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_s-C-RES_WHEN_MULT-FORMULA-CHECKS)
                            is-rp
                            ;;is-falist
                            ;;(:DEFINITION VALID-SC)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE DEFAULT-CDR)
                            ;;(:DEFINITION RP-TRANS)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE DEFAULT-CAR)
                            (:TYPE-PRESCRIPTION O<)
                            pp-sum-merge-correct
                            PP-SUM-MERGE-AUX-CORRECT
                            decompress-s-c-correct
                            light-compress-s-c-correct
                            )))))

(defthm rp-evlt-of-quoted
  (equal (rp-evlt (list 'quote x) a)
         x))

(defthm unquote-all-is-correct
  (implies (quoted-listp lst)
           (equal (unquote-all lst)
                  (rp-evlt-lst lst a)))
  :hints (("goal"
           :induct (unquote-all lst)
           :do-not-induct t
           :in-theory (e/d () (
                               )))))

(defthm all-quoted-list-correct
  (implies (all-quoted-list term)
           (equal (unquote-all (list-to-lst term))
                  (rp-evlt term a)))
  :hints (("Goal"
           :in-theory (e/d (all-quoted-list
                            LIST-TO-LST)
                           ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-termp-implies-bitp

(progn

  (local
   (defthmd is-rp-and-rp-evlt-dummy-lemma
     (implies (is-rp term)
              (equal (rp-evlt term a)
                     (rp-evlt (caddr term) a)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

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
   (create-regular-eval-lemma sum-list 1 mult-formula-checks))

  (local
   (defthm pp-termp-is-bitp-lemma
     (implies (and (has-bitp-rp term)
                   (rp-evl-meta-extract-global-facts :state state)
                   (valid-sc term a)
                   (mult-formula-checks state))
              (and (bitp (rp-evlt term a))
                   (bitp (rp-evlt (ex-from-rp term) a))))
     :otf-flg t
     :hints (("goal"
              :induct (has-bitp-rp term)
              :do-not-induct t
              :in-theory (e/d (is-if ;is-rp
                               valid-sc

                               is-rp-and-rp-evlt-dummy-lemma
                               is-rp-implies-fc
                               valid-sc-single-step
                               rp-trans-lst-of-consp
                               HAS-BITP-RP)
                              (bitp
                               rp-trans
                               rp-trans-lst
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
              ;;:expand ((PP-TERM-P TERM))
              :in-theory (e/d (;;pp-term-p
                               is-rp
                               pp
                               when-ex-from-rp-is-0
                               ;;rp-evlt-of-ex-from-rp-reverse-only-atom
                               is-if)
                              (bitp
                               (:DEFINITION VALID-SC)
                               (:DEFINITION EVAL-AND-ALL)
                               (:DEFINITION IS-RP$INLINE)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                               HAS-BITP-RP
                               rp-trans
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
              :in-theory (e/d* (LIGHT-PP-TERM-p
                                is-rp
                                regular-eval-lemmas-with-ex-from-rp
                                ;;rp-evlt-of-ex-from-rp-reverse-only-atom
                                is-if)
                               (bitp
                                pp-term-p
                                RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                                ;;rp-evlt-of-ex-from-rp
                                EX-FROM-RP-LEMMA1
                                rp-evlt-of-ex-from-rp))))))

  (local
   (defthm PP-HAS-BITP-RP-EX-FROM-RP
     (not (HAS-BITP-RP (EX-FROM-RP TERM)))
     :hints (("Goal"
              :induct (EX-FROM-RP TERM)
              :do-not-induct t
              :in-theory (e/d (EX-FROM-RP HAS-BITP-RP
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

(defthm rp-trans-of-quoted
  (implies (equal (car x) 'quote)
           (equal (rp-trans x)
                  x))
  :rule-classes :forward-chaining)

(defthm quotep-implies
  (implies (quotep x)
           (equal (car x) 'quote))
  :rule-classes :forward-chaining)

(value-triple (hons-clear t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-s-instance and s-pattern1-reduce lemmas

(defthmd s-pattern1-reduce-correct-lemma
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

(defret s-pattern1-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and (equal (sum (sum-list-eval reduced-pp-lst a)
                            (sum-list-eval reduced-c-lst a))
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))))
  :fn s-pattern1-reduce
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
                  s-pattern1-reduce-correct-lemma
                  (val (RP-EVLT (CADR (CADDDR (LIGHT-COMPRESS-S-C (LIST 'S ''0 PP C))))
                                A))))
           :in-theory (e/d (s-pattern1-reduce
                            rp-trans-lst-of-consp
                            s-c-res
                            is-rp)
                           (light-compress-s-c-correct
                            s-pattern1-reduce-correct-lemma
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

(defthm dummy-sum-lemma2
  (and (equal (equal (sum x y a) (sum z a))
              (equal (sum x y) (ifix z)))
       (equal (equal (sum x y z a) (sum p a))
              (equal (sum x y z) (ifix p)))))

(defret s-pattern1-reduce-correct-corollary
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and (equal (sum (sum-list-eval reduced-pp-lst a)
                            (sum-list-eval reduced-c-lst a)
                            rest)
                       (sum (m2 (sum (sum-list (rp-evlt pp a))
                                     (sum-list (rp-evlt c a))))
                            rest))))
  :fn s-pattern1-reduce)

(local
 (defthm is-rp-of-bitp
   (is-rp `(rp 'bitp ,x))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(defret s-pattern1-reduce-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and (valid-sc-subterms reduced-pp-lst a)
                (valid-sc-subterms reduced-c-lst a)))
  :fn s-pattern1-reduce
  :hints (("goal"
           :use ((:instance s-pattern1-reduce-correct))
           :expand ((:free (x) (valid-sc (cons 's-c-res x) a))
                    (:free (x) (valid-sc (cons 'list x) a))
                    (:free (x) (valid-sc (cons '-- x) a)))
           :in-theory (e/d (s-pattern1-reduce
                            valid-sc-single-step
                            is-rp)
                           (s-pattern1-reduce-correct
                            valid-sc
                            )))))

(defret s-pattern1-reduce-returns-integer-listp
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                ;;(valid-sc pp a)
                ;;(valid-sc c a)
                reducedp)
           (and ;;(integer-listp (rp-evlt-lst reduced-pp-lst a))
            (integer-listp (rp-evlt-lst reduced-c-lst a))))
  :fn s-pattern1-reduce
  :hints (("goal"
           :use ((:instance s-pattern1-reduce-correct))
           :expand ((:free (x) (valid-sc (cons 's-c-res x) a))
                    (:free (x) (valid-sc (cons 'list x) a))
                    (:free (x) (valid-sc (cons '-- x) a)))
           :in-theory (e/d (s-pattern1-reduce
                            valid-sc-single-step
                            is-rp)
                           (s-pattern1-reduce-correct
                            valid-sc
                            )))))

(defthmd m2-of-bitp
  (implies (bitp x)
           (equal (m2 x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(local
 (defthmd m2-of-three-bits
   (implies (and (bitp a)
                 (bitp b)
                 (bitp c))
            (equal (m2 (sum a b c))
                   (binary-xor a
                               (binary-xor b c))))
   :hints (("Goal"
            :in-theory (e/d (bitp) ())))))

(progn
  (defret AND-LIST-INSTANCE-TO-BINARY-AND-AUX-valid-sc
    (implies (valid-sc-subterms lst a)
             (valid-sc res a))
    :fn AND-LIST-INSTANCE-TO-BINARY-AND-AUX
    :hints (("Goal"
             :in-theory (e/d (AND-LIST-INSTANCE-TO-BINARY-AND-AUX
                              is-rp
                              is-if)
                             ()))))

  (defret and-list-instance-to-binary-and-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (equal (rp-evlt res a)
                    (and-list 0 (rp-evlt-lst lst a))))
    :fn and-list-instance-to-binary-and-aux
    :hints (("goal"
             :induct (and-list-instance-to-binary-and-aux lst)
             :expand ((and-list 0
                                (cons (rp-evlt (car lst) a)
                                      (rp-evlt-lst (cdr lst) a))))
             :in-theory (e/d (and-list-instance-to-binary-and-aux
                              is-rp
                              is-if)
                             ()))))

  (defret and-list-instance-to-binary-and-valid-sc
    (implies (valid-sc term a)
             (valid-sc res a))
    :fn and-list-instance-to-binary-and
    :hints (("goal"
             :in-theory (e/d (and-list-instance-to-binary-and) ()))))

  (defret and-list-instance-to-binary-and-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (equal (rp-evlt res a)
                    (rp-evlt term a)))
    :fn and-list-instance-to-binary-and
    :hints (("goal"
             :in-theory (e/d (and-list-instance-to-binary-and)
                             (rp-trans))))))

(defthm pp-flatten-correct-with-sum-list-eval
  (implies (and (mult-formula-checks state)
                (force (pp-term-p term))
                (booleanp sign)
                (force (valid-sc term a))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval (pp-flatten term sign :unpack-now unpack-now) a)
                  (if sign
                      (-- (rp-evlt term a))
                    (rp-evlt term a))))
  :hints (("Goal"
           :use ((:instance pp-flatten-correct))
           :in-theory (e/d () ()))))

(defret single-s-to-pp-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc pp1 a))
                (force (valid-sc pp2 a))
                (force (valid-sc pp3 a))
                success)
           (and (valid-sc-subterms res-pp-lst a)
                (equal (sum-list-eval res-pp-lst a)
                       (m2 (sum (rp-evlt pp1 a)
                                (rp-evlt pp2 a)
                                (rp-evlt pp3 a))))))
  :fn single-s-to-pp-lst
  :hints (("goal"
           :do-not-induct t
           :use ((:instance
                  and-list-instance-to-binary-and-correct
                  (term pp1))
                 (:instance
                  and-list-instance-to-binary-and-correct
                  (term pp2))
                 (:instance
                  and-list-instance-to-binary-and-correct
                  (term pp3))
                 (:instance
                  m2-of-three-bits
                  (a (rp-evlt pp1 a))
                  (b (rp-evlt pp2 a))
                  (c (rp-evlt pp3 a))))
           :expand ((:free (x y)
                           (valid-sc `(binary-xor ,x ,y) a))
                    (:free (x y)
                           (pp-term-p `(binary-xor ,x ,y))))
           :in-theory (e/d (single-s-to-pp-lst
                            ex-from-rp
                            is-rp is-if)
                           (and-list-instance-to-binary-and-correct
                            rp-trans
                            (:DEFINITION PP-TERM-P)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            valid-sc)))))

(defret s-pattern2-reduce-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and (valid-sc-subterms reduced-pp-lst a)))
  :fn s-pattern2-reduce
  :hints (("Goal"
           :expand ((:free (x)
                           (valid-sc `(sum-list ,x) a)))
           :in-theory (e/d (s-pattern2-reduce
                            is-rp if
                            valid-sc-single-step)
                           (valid-sc)))))

(defthmd m2-of-1
  (and (equal (m2 (sum a b 1))
              (sum 1 (-- (m2 (sum a b)))))
       (equal (m2 (sum a 1))
              (sum 1 (-- (m2 (sum a)))))
       (equal (m2 (sum a b c 1))
              (sum 1 (-- (m2 (sum a b c))))))
  :hints (("Goal"
           :in-theory (e/d (m2 -- sum
                               (:REWRITE ACL2::|(* a (/ a) b)|)
                               (:REWRITE ACL2::|(* x (+ y z))|)
                               (:REWRITE ACL2::|(+ x (if a b c))|)
                               (:REWRITE ACL2::|(+ y (+ x z))|)
                               (:REWRITE ACL2::|(+ y x)|)
                               (:REWRITE ACL2::|(- (if a b c))|)
                               (:REWRITE ACL2::|(mod x 2)| . 1)
                               (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                               (:REWRITE IFIX-OPENER)
                               (:REWRITE M2-OF-IFIX)
                               (:REWRITE ACL2::SUM-IS-EVEN . 1))
                           (+-IS-SUM mod2-is-m2)))))

(defret s-pattern2-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and (equal (sum-list-eval REDUCED-PP-LST a)
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))))
  :fn s-pattern2-reduce
  :hints (("Goal"
           :expand ((:free (x)
                           (valid-sc `(sum-list ,x) a)))
           :in-theory (e/d (s-pattern2-reduce
                            is-rp if
                            m2-of-1
                            valid-sc-single-step)
                           (valid-sc)))))

(defthm m2-of-1-v2
  (and (equal (m2 (sum x 1 y))
              (sum (-- (m2 (sum x y)))
                   1))
       (equal (m2 (sum x 1))
              (sum (-- (m2 x))
                   1)))
  :hints (("Goal"
           :in-theory (e/d (m2 sum f2
                               (:REWRITE ACL2::SUM-IS-EVEN . 1)
                               (:REWRITE ACL2::|(mod x 2)| . 1)
                               (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                               (:REWRITE ACL2::|(* a (/ a) b)|)
                               (:REWRITE ACL2::|(* x (+ y z))|)
                               (:REWRITE ACL2::|(+ y (+ x z))|)
                               (:REWRITE ACL2::|(+ y x)|)
                               (:REWRITE ACL2::|(equal (if a b c) x)|))
                           (+-IS-SUM
                            floor2-if-f2
                            mod2-is-m2)))))

(defthmd sum-list-eval-of-cdr
  (implies (consp lst)
           (equal (sum-list-eval (cdr lst) a)
                  (sum (sum-list-eval lst a)
                       (-- (rp-evlt (car lst) a))))))

(defthm m2-of-minus-1
  (and (equal (m2 (sum a b -1))
              (m2 (sum a b 1)))
       (equal (m2 (sum a -1))
              (m2 (sum a 1)))
       (equal (m2 (sum a b c -1))
              (m2 (sum a b c 1))))
  :hints (("Goal"
           :in-theory (e/d (m2 sum
                               --
                               (:REWRITE ACL2::|(* a (/ a) b)|)
                               (:REWRITE ACL2::|(* x (+ y z))|)
                               (:REWRITE ACL2::|(+ y (+ x z))|)
                               (:REWRITE ACL2::|(+ y x)|)
                               (:REWRITE ACL2::|(mod x 2)| . 1)
                               (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                               (:REWRITE IFIX-OPENER)
                               (:REWRITE ACL2::INTEGERP-+-REDUCE-CONSTANT)
                               (:REWRITE ACL2::SUM-IS-EVEN . 1)
                               )
                           (+-IS-SUM mod2-is-m2)))))

(defthmd VALID-SC-SUBTERMS-implies-VALID-SC-SUBTERMS-cdr
  (implies (and (consp lst)
                (valid-sc-subterms lst a))
           (VALID-SC-SUBTERMS (cdr lst) a)))

(defthm bitp-of-one-minus-m2
  (and (bitp (sum (-- (m2 x)) 1))
       (bitp (sum 1 (-- (m2 x)))))
  :hints (("Goal"
           :use ((:instance m2-of-1
                            (a x)))
           :in-theory (e/d ()
                           (m2-of-1
                            m2-of-1-v2)))))

(defret s-pattern3-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                reducedp)
           (and   (valid-sc-subterms s-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a))
                         (m2 (sum (sum-list (rp-evlt pp a))
                                  (sum-list (rp-evlt c a)))))))
  :fn S-PATTERN3-REDUCE
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (S-PATTERN3-REDUCE
                            m2-of-1
                            VALID-SC-SUBTERMS-implies-VALID-SC-SUBTERMS-cdr
                            sum-list-eval-of-cdr
                            is-rp
                            valid-sc-single-step)
                           ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pattern0-reduce lemmas


(defret pattern0-reduce-aux-pp-lst-correct
  (and (implies (valid-sc-subterms pp-lst a)
                (and (valid-sc pp1 a)
                     (valid-sc pp2 a)))
       (implies (and (mult-formula-checks state)
                     (rp-evl-meta-extract-global-facts)
                     pp-valid)
                (and (equal (sum (rp-evlt pp1 a) (rp-evlt pp2 a))
                            (sum-list-eval pp-lst a))
                     (implies (equal pp-cnt 2)
                              (and (equal pp1 (car pp-lst))
                                   (equal pp2 (cadr pp-lst))))
                     (implies (equal pp-cnt 1)
                              (and (equal pp1 (car pp-lst)))))))
  :fn pattern0-reduce-aux-pp-lst
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (pattern0-reduce-aux-pp-lst) ()))))

(defret-mutual pattern0-reduce-aux-valid-sc
  (defret pattern0-reduce-aux-s-lst-valid-sc
    (implies (valid-sc-subterms s-lst a)
             (and (valid-sc s1 a)
                  (valid-sc s2 a)))
    :fn pattern0-reduce-aux-s-lst)
  (defret pattern0-reduce-aux-c-lst-valid-sc
    (implies (valid-sc-subterms c-lst a)
             (and (valid-sc c1 a)
                  (valid-sc c2 a)))
    :fn pattern0-reduce-aux-c-lst)
  (defret pattern0-reduce-aux-valid-sc
    (implies (and (valid-sc-subterms s-lst a)
                  (valid-sc-subterms pp-lst a)
                  (valid-sc-subterms c-lst a))
             (and (valid-sc pp-term1 a)
                  (valid-sc pp-term2 a)))
    :fn pattern0-reduce-aux)
  :mutual-recursion pattern0-reduce-aux
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (valid-sc (cons 'binary-and x) a))
                    (:free (x) (valid-sc (cons 'binary-xor x) a)))
           :in-theory (e/d (is-rp is-if
                                  pattern0-reduce-aux
                                  pattern0-reduce-aux-s-lst
                                  pattern0-reduce-aux-c-lst
                                  )
                           ((:DEFINITION VALID-SC)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION RP-TRANS)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE VALID-SC-CADR)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            ;;(:REWRITE VALID-SC-CADDR)
                            ;;(:REWRITE VALID-SC-CADDDR)
                            (:DEFINITION INCLUDE-FNC))))))

(progn
  (defret pattern0-reduce-aux-pp-lst-cnt-implies-1
    (implies (and (equal pp-cnt 2)
                  pp-valid)
             (and (consp pp-lst)
                  (consp (cdr pp-lst))
                  (not (consp (cddr pp-lst)))))
    :fn pattern0-reduce-aux-pp-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (pattern0-reduce-aux-pp-lst) ()))))

  (defret pattern0-reduce-aux-pp-lst-cnt-implies-2
    (implies (and (equal pp-cnt 1)
                  pp-valid)
             (and (consp pp-lst)
                  (not (consp (cdr pp-lst)))))
    :fn pattern0-reduce-aux-pp-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (pattern0-reduce-aux-pp-lst) ()))))

  (defret pattern0-reduce-aux-pp-lst-cnt-implies-3
    (implies (and (equal pp-cnt 0)
                  pp-valid)
             (not (consp pp-lst)))
    :fn pattern0-reduce-aux-pp-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (pattern0-reduce-aux-pp-lst) ()))))

  (defret pattern0-reduce-aux-s-lst-cnt-implies-1
    (implies (and (equal s-cnt 2)
                  s-valid)
             (and (consp s-lst)
                  (consp (cdr s-lst))
                  (not (consp (cddr s-lst)))))
    :fn pattern0-reduce-aux-s-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-S-LST S-LST LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-s-lst) ()))))

  (defret pattern0-reduce-aux-s-lst-cnt-implies-2
    (implies (and (equal s-cnt 1)
                  s-valid)
             (and (consp s-lst)
                  (not (consp (cdr s-lst)))))
    :fn pattern0-reduce-aux-s-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-S-LST S-LST LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-s-lst) ()))))

  (defret pattern0-reduce-aux-s-lst-cnt-implies-3
    (implies (and (equal s-cnt 0)
                  s-valid)
             (not (consp s-lst)))
    :fn pattern0-reduce-aux-s-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-S-LST S-LST LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-s-lst) ()))))

  (defret pattern0-reduce-aux-c-lst-cnt-implies-1
    (implies (and (equal c-cnt 2)
                  c-valid)
             (and (consp c-lst)
                  (consp (cdr c-lst))
                  (not (consp (cddr c-lst)))))
    :fn pattern0-reduce-aux-c-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-C-LST C-LST LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-c-lst) ()))))

  (defret pattern0-reduce-aux-c-lst-cnt-implies-2
    (implies (and (equal c-cnt 1)
                  c-valid)
             (and (consp c-lst)
                  (not (consp (cdr c-lst)))))
    :fn pattern0-reduce-aux-c-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-C-LST C-LST LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-c-lst) ()))))

  (defret pattern0-reduce-aux-c-lst-cnt-implies-3
    (implies (and (equal c-cnt 0)
                  c-valid)
             (not (consp c-lst)))
    :fn pattern0-reduce-aux-c-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-C-LST C-LST LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-c-lst) ())))))

(defthmd sum-list-eval-consp
  (implies (consp lst)
           (equal (sum-list-eval lst a)
                  (SUM (RP-EVLT (CAR LST) A)
                       (SUM-LIST-EVAL (CDR LST) A))))
  :hints (("Goal"
           :in-theory (e/d (sum-list-eval) ()))))

(defthmd pattern0-reduce-aux-correct-sum-lemma
  (implies (and (equal (ifix x1) (ifix x2))
                (equal (ifix y1) (ifix y2)))
           (equal (equal (sum x1 y1)
                         (sum x2 y2))
                  t))
  :hints (("Goal"
           :in-theory (e/d (sum)
                           (+-IS-SUM)))))

(defthmd pattern0-reduce-aux-correct-lemma-2
  (implies (and (bitp x)
                (bitp y)
                (equal (sum x y) z))
           (equal (equal (and$ x y)
                         (f2 z))
                  t))
  :hints (("Goal"
           :in-theory (e/d (sum bitp)
                           (+-IS-SUM)))))

(defthmd pattern0-reduce-aux-correct-lemma-3
  (implies (and (bitp x)
                (bitp y)
                (equal (sum x y) z))
           (and (equal (and$ x y) (f2 z))
                (equal (equal (and$ x y)
                              (sum (f2 z) k))
                       (equal (ifix k) 0))
                (equal (equal (sum (and$ x y) k)
                              (f2 z))
                       (equal (ifix k) 0))))
  :hints (("Goal"
           :in-theory (e/d (sum bitp)
                           (+-IS-SUM)))))

(defthmd pattern0-reduce-aux-correct-lemma-4
  (implies (and (bitp x)
                (bitp y)
                (equal (sum x y) z))
           (and (equal (binary-xor x y) (m2 z))
                (equal (equal (binary-xor x y)
                              (sum (m2 z) k))
                       (equal (ifix k) 0))
                (equal (equal (sum (binary-xor x y) k)
                              (m2 z))
                       (equal (ifix k) 0))))
  :hints (("Goal"
           :in-theory (e/d (sum bitp)
                           (+-IS-SUM)))))

(defthm sum-calcel-dumm1
  (implies (integerp a)
           (equal (equal (sum a b)
                         a)
                  (equal (ifix b) 0)))
  :hints (("Goal"
           :in-theory (e/d (sum ifix)
                           (+-IS-SUM)))))

(defthm integerp-of-and$
  (integerp (and$ a b))
  :rule-classes :type-prescription)

(defthmd binary-xor-to-m2-when-bitp
  (implies (and (bitp x)
                (bitp y))
           (equal (binary-xor x y)
                  (m2 (sum x y))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defthmd binary-and-to-f2-when-bitp
  (implies (and (bitp x)
                (bitp y))
           (equal (and$ x y)
                  (f2 (sum x y))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defret-mutual pattern0-reduce-aux-correct
  (defret pattern0-reduce-aux-s-lst-correct
    (implies (and s-valid
                  (valid-sc-subterms s-lst a)
                  (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts))
             (and (implies (equal s-cnt 1)
                           (equal (sum (rp-evlt s1 a))
                                  (sum-list-eval s-lst a)))
                  (equal (sum (rp-evlt s1 a) (rp-evlt s2 a))
                         (sum-list-eval s-lst a))))
    :fn pattern0-reduce-aux-s-lst)
  (defret pattern0-reduce-aux-c-lst-correct
    (implies (and c-valid
                  (mult-formula-checks state)
                  (valid-sc-subterms c-lst a)
                  (rp-evl-meta-extract-global-facts))
             (and (implies (equal c-cnt 1)
                           (equal (sum (rp-evlt c1 a))
                                  (sum-list-eval c-lst a)))
                  (equal (sum (rp-evlt c1 a) (rp-evlt c2 a))
                         (sum-list-eval c-lst a))))
    :fn pattern0-reduce-aux-c-lst)
  (defret pattern0-reduce-aux-correct
    (implies (and valid
                  (mult-formula-checks state)
                  (valid-sc-subterms s-lst a)
                  (valid-sc-subterms pp-lst a)
                  (valid-sc-subterms c-lst a)
                  (rp-evl-meta-extract-global-facts))
             (and
              (and (equal (sum (rp-evlt pp-term1 a) (rp-evlt pp-term2 a))
                          (sum (sum-list-eval s-lst a)
                               (sum-list-eval pp-lst a)
                               (sum-list-eval c-lst a)))
                   (equal (and$ (rp-evlt pp-term1 a) (rp-evlt pp-term2 a))
                          (f2 (sum (sum-list-eval s-lst a)
                                   (sum-list-eval pp-lst a)
                                   (sum-list-eval c-lst a))))
                   (equal (binary-xor (rp-evlt pp-term1 a) (rp-evlt pp-term2 a))
                          (m2 (sum (sum-list-eval s-lst a)
                                   (sum-list-eval pp-lst a)
                                   (sum-list-eval c-lst a)))))))
    :fn pattern0-reduce-aux)
  :mutual-recursion pattern0-reduce-aux
  :hints (("Goal"

           :expand ((:free (x) (pp-term-p (cons 'binary-and x)))
                    (:free (x) (pp-term-p (cons 'binary-xor x)))
                    (:free (x) (ex-from-rp (cons 'binary-and x)))
                    (:free (x) (ex-from-rp (cons 'binary-xor x))))
           :do-not-induct t
           :in-theory (e/d* (is-rp
                             pattern0-reduce-aux-correct-lemma-2
                             pattern0-reduce-aux-correct-lemma-3
                             pattern0-reduce-aux-correct-lemma-4
                             (:REWRITE REGULAR-RP-EVL-OF_BINARY-AND_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE REGULAR-RP-EVL-OF_BINARY-XOR_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             sum-list-eval-consp
                             pattern0-reduce-aux
                             pattern0-reduce-aux-s-lst
                             pattern0-reduce-aux-c-lst
                             pattern0-reduce-aux-correct-sum-lemma
                             binary-and-to-f2-when-bitp
                             binary-xor-to-m2-when-bitp)
                            (valid-sc-subterms
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                             (:REWRITE MINUS-OF-SUM)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:DEFINITION IS-SYNP$INLINE)
                             (:REWRITE DEFAULT-CAR)
                             (:TYPE-PRESCRIPTION SUM-LIST)
                             (:TYPE-PRESCRIPTION O-FINP)
                             (:REWRITE ACL2::O-FIRST-EXPT-O-INFP)
                             (:REWRITE LTE-AND-GTE-IMPLIES)
                             (:REWRITE LT-TO-GT)
                             (:REWRITE RP-EVL-OF-ZP-CALL)
                             (:DEFINITION EX-FROM-RP)
                             (:DEFINITION IS-FALIST)
                             (:DEFINITION IS-RP$INLINE)
                             (:DEFINITION RP-TRANS)
                             (:DEFINITION RP-TRANS-LST)
                             ;;(:DEFINITION SUM-LIST-EVAL)
                             bitp
                             (:type-prescription binary-and)
                             (:type-prescription bitp)
                             SUM-OF-F2S
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:REWRITE RP-TRANS-OPENER)
                             VALID-SC-SUBTERMS-CONS
                             valid-sc
                             eval-and-all
                             include-fnc)))))

(defret c-pattern0-reduce-correct
  (implies (and (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                reduced)
           (equal (f2 (sum (sum-list-eval c-lst  a)
                           (sum-list-eval pp-lst a)
                           (sum-list-eval s-lst a)))
                  0))
  :fn c-pattern0-reduce
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x)
                           (pp-term-p (cons 'binary-and x)))
                    (:free (x)
                           (ex-from-rp (cons 'binary-and x))))
           :use ((:instance PP-FLATTEN-CORRECT
                            (term (LIST 'BINARY-AND
                                        (MV-NTH 0
                                                (PATTERN0-REDUCE-AUX S-LST PP-LST C-LST 1073741824))
                                        (MV-NTH 1
                                                (PATTERN0-REDUCE-AUX S-LST PP-LST C-LST 1073741824))))
                            (sign nil)
                            (unpack-now t)))
           ;;:use ((:instance c-pattern0-reduce-correct-lemma
           :in-theory (e/d (c-pattern0-reduce
                            is-rp)
                           (PP-FLATTEN-CORRECT)))))

(defret s-pattern0-reduce-correct
  (implies (and (valid-sc pp a)
                (valid-sc c a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                reduced)
           (equal (m2 (sum (sum-list (rp-evlt c a))
                           (sum-list (rp-evlt pp a))))
                  0))
  :fn s-pattern0-reduce
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x)
                           (pp-term-p (cons 'binary-xor x)))
                    (:free (x)
                           (ex-from-rp (cons 'binary-xor x))))
           :use ((:instance PP-FLATTEN-CORRECT
                            (term (LIST
                                   'BINARY-xor
                                   (MV-NTH 0
                                           (PATTERN0-REDUCE-AUX nil
                                                                (list-to-lst pp) (list-to-lst c) 1073741824))
                                   (MV-NTH 1
                                           (PATTERN0-REDUCE-AUX nil
                                                                (list-to-lst pp) (list-to-lst c) 1073741824))))
                            (sign nil)
                            (unpack-now t)))
           ;;:use ((:instance c-pattern0-reduce-correct-lemma
           :in-theory (e/d (s-pattern0-reduce
                            is-rp)
                           (PP-FLATTEN-CORRECT)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-s-instance lemmas

(defret create-s-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a))
           (and
            (valid-sc-subterms s-res-lst a)
            (valid-sc-subterms pp-res-lst a)
            (valid-sc-subterms c-res-lst a)
            (equal (sum (sum-list-eval s-res-lst a)
                        (sum-list-eval pp-res-lst a)
                        (sum-list-eval c-res-lst a))
                   (m2 (sum (sum-list (rp-evlt pp a))
                            (sum-list (rp-evlt c a)))))))
  :fn create-s-instance
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (create-s-instance
                            m2-of-bitp
                            bitp-implies-integerp
                            valid-sc-single-step
                            rp-trans-lst-of-consp
                            is-rp)
                           (include-fnc)))))

(defret create-s-instance-correct-corollary
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a))
           (and
            (equal (sum (sum-list-eval s-res-lst a)
                        (sum-list-eval pp-res-lst a)
                        (sum-list-eval c-res-lst a)
                        rest)
                   (sum (m2 (sum (sum-list (rp-evlt pp a))
                                 (sum-list (rp-evlt c a))))
                        rest))))
  :fn create-s-instance
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d ()
                           ()))))

#|(defret create-s-instance-returns-integer-listp
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc c a))
           (and
            (integer-listp (rp-evlt-lst s-res-lst a))
            (integer-listp (rp-evlt-lst c-res-lst a))))
  :fn create-s-instance
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (CREATE-S-INSTANCE
                            bitp-implies-integerp)
()))))||#

(create-regular-eval-lemma binary-and 2 mult-formula-checks)

(defthm and$-of-1-2
  (equal (and$ a b 1)
         (and$ a b))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defret and-list-to-binary-and-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (rp-evlt res a)
                  (and-list 0 (rp-evlt-lst lst a))))
  :fn and-list-to-binary-and-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (AND-LIST-TO-BINARY-AND-AUX LST)
           :expand ((:free (x y) (and-list 0 (cons x y)))
                    (AND-LIST-TO-BINARY-AND-AUX LST)
                    )
           :in-theory (e/d* (regular-eval-lemmas-with-ex-from-rp
                             ;;and-list
                             (:induction and-list-to-binary-and-aux)
                             regular-eval-lemmas)
                            ((:DEFINITION RP-TRANS)
                             (:REWRITE RP-TRANS-OPENER)
                             (:REWRITE CONSP-OF-RP-EVL-OF-TRANS-LIST)
                             (:REWRITE CONSP-OF-RP-TRANS-LST)
                             (:TYPE-PRESCRIPTION RP-TRANS-LST)
                             (:REWRITE RP-EVL-LST-OF-CONS)
                             (:DEFINITION RP-TRANS-LST))))))

(defret and-list-to-binary-and-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (valid-sc res a))
  :fn and-list-to-binary-and-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (AND-LIST-TO-BINARY-AND-AUX LST)
           :expand ((:free (x y) (and-list 0 (cons x y)))
                    (AND-LIST-TO-BINARY-AND-AUX LST)
                    )
           :in-theory (e/d* (valid-sc is-rp is-if
                                      ;;and-list
                                      (:induction and-list-to-binary-and-aux)
                                      )
                            ((:DEFINITION RP-TRANS)
                             (:REWRITE RP-TRANS-OPENER)
                             (:REWRITE CONSP-OF-RP-EVL-OF-TRANS-LIST)
                             (:REWRITE CONSP-OF-RP-TRANS-LST)
                             (:TYPE-PRESCRIPTION RP-TRANS-LST)
                             (:REWRITE RP-EVL-LST-OF-CONS)
                             (:DEFINITION RP-TRANS-LST))))))

(create-regular-eval-lemma and-list 2 mult-formula-checks)

(defthm remove-hash-arg-of-and-list
  (implies (syntaxp (and (not (equal hash 0))
                         (not (equal hash ''0))))
           (equal (and-list hash lst)
                  (and-list 0 lst)))
  :hints (("Goal"
           :in-theory (e/d (and-list) ()))))

(defret and-list-to-binary-and-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                valid)
           (and (equal (rp-evlt res a)
                       (rp-evlt term a))
                (integerp (rp-evlt res a))
                (integerp (rp-evlt term a))))
  :fn and-list-to-binary-and
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (and-list-to-binary-and
                             and-list
                             BINARY-FNC-P
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp)
                            ()))))

(defret and-list-to-binary-and-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                valid
                (valid-sc term a))
           (valid-sc res a))
  :fn and-list-to-binary-and
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (and-list-to-binary-and
                             and-list)
                            ()))))

(defthmd rp-evlt-ex-from-rp-of-quoted
  (implies (quotep x)
           (equal (rp-evlt (ex-from-rp x) a)
                  (cadr x)))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp is-rp) ()))))

(defret create-s-c-res-instance-correct
  (implies  (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (and #|(equal (ifix (rp-evlt res a))
             (sum (sum-list-eval s-lst a) ;
             (sum-list-eval pp-lst a) ;
             (sum-list-eval c-lst a)))||#
             #|(equal (sum (rp-evlt res a) x)
             (sum (sum-list-eval s-lst a) ;
             (sum-list-eval pp-lst a) ;
             (sum-list-eval c-lst a) ;
             x))||#
             (implies t #|(and (integer-listp (rp-evlt-lst s-lst a))
                      (integer-listp (rp-evlt-lst c-lst a)))||#
                      (equal (rp-evlt res a)
                             (sum (sum-list-eval s-lst a)
                                  (sum-list-eval pp-lst a)
                                  (sum-list-eval c-lst a))))))
  :fn create-s-c-res-instance
  :hints (("Goal"

           :in-theory (e/d* (create-s-c-res-instance
                             S-C-RES
                             rp-evlt-ex-from-rp-of-quoted
                             rp-trans-lst-of-consp
                             ;;regular-eval-lemmas-with-ex-from-rp
                             ;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             )
                            (;;rp-evlt-of-ex-from-rp
                             INCLUDE-FNC
                             INCLUDE-FNC-SUBTERMS
                             IS-FALIST
                             RP-TRANS
                             RP-TRANS-LST
                             ;;RP-EVLT-OF-QUOTED
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:DEFINITION EQ)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:DEFINITION IS-SYNP$INLINE)
                             (:REWRITE ACL2::ACL2-NUMBERP-X)
                             (:TYPE-PRESCRIPTION CREATE-LIST-INSTANCE)
                             (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                             (:TYPE-PRESCRIPTION --)
                             (:REWRITE
                              ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                             EVL-OF-EXTRACT-FROM-RP
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)))))

(defret create-s-c-res-instance-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (if bitp
                    (bitp (rp-evlt res a))
                  t))
           (valid-sc res a))
  :fn create-s-c-res-instance
  :hints (("Goal"
           :expand ((:free (rest)
                           (valid-sc (cons 's-c-res rest) a))
                    (:free (rest)
                           (valid-sc (cons 'ifix rest) a)))
           :in-theory (e/d (create-s-c-res-instance
                            valid-sc-single-step
                            is-rp is-if
                            S-C-RES)
                           (valid-sc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; single-c-to-pp-lst, c-pattern2-reduce lemmas

(value-triple (hons-clear t))

(defret single-c-to-pp-lst-valid-sc
  (implies (and (force (valid-sc pp1 a))
                (force (valid-sc pp2 a))
                (force (valid-sc pp3 a)))
           (valid-sc-subterms res-pp-lst a))
  :fn single-c-to-pp-lst
  :hints (("Goal"
           :in-theory (e/d (SINGLE-C-TO-PP-LST is-rp is-if)
                           (valid-sc))
           :expand ((:free (x y)
                           (valid-sc `(BINARY-OR ,X ,Y) a))
                    (:free (x y)
                           (valid-sc `(BINARY-and ,X ,Y) a))))))

(local
 (defthmd f2-of-three-bits
   (implies (and (bitp a)
                 (bitp b)
                 (bitp c))
            (equal (f2 (sum a b c))
                   (OR$ (AND$ a b)
                        (AND$ b c)
                        (AND$ a c))))
   :hints (("Goal"
            :in-theory (e/d (bitp) ())))))

(defret single-c-to-pp-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc pp1 a))
                (force (valid-sc pp2 a))
                (force (valid-sc pp3 a))
                success)
           (equal (sum-list-eval res-pp-lst a)
                  (f2 (sum (rp-evlt pp1 a)
                           (rp-evlt pp2 a)
                           (rp-evlt pp3 a)))))
  :fn single-c-to-pp-lst
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  and-list-instance-to-binary-and-correct
                  (term pp1))
                 (:instance
                  and-list-instance-to-binary-and-correct
                  (term pp2))
                 (:instance
                  and-list-instance-to-binary-and-correct
                  (term pp3))
                 (:instance
                  f2-of-three-bits
                  (a (RP-EVLT PP1 A))
                  (b (RP-EVLT PP2 A))
                  (c (RP-EVLT PP3 A))))
           :expand ((:free (x y)
                           (valid-sc `(BINARY-OR ,X ,Y) a))
                    (:free (x y)
                           (pp-term-p `(BINARY-OR ,X ,Y)))
                    (:free (x y)
                           (valid-sc `(BINARY-and ,X ,Y) a))
                    (:free (x y)
                           (pp-term-p `(BINARY-and ,X ,Y))))
           :in-theory (e/d (SINGLE-C-TO-PP-LST

                            EX-FROM-RP
                            is-rp is-if)
                           (valid-sc
                            (:DEFINITION PP-TERM-P)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION RP-TRANS)
                            (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                            (:DEFINITION RP-EQUAL)
                            (:REWRITE DEFAULT-CDR)
                            bitp
                            and-list-instance-to-binary-and-correct)))))

(defret c-pattern2-reduce-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (valid-sc-subterms res-pp-lst a)))
  :fn c-pattern2-reduce
  :hints (("Goal"
           :do-not-induct t
           :expand (VALID-SC ''1 A)
           :in-theory (e/d (c-pattern2-reduce) ()))))

(encapsulate
  nil
  (local
   (use-arith-5 t))
  (defthm m2-plus-f2-of-the-same-argument
    (and (equal (sum (m2 x) (f2 x) y)
                (sum (f2 (sum 1 x))  y))
         (equal (sum (m2 x) (f2 x))
                (f2 (sum 1 x))))
    :hints (("Goal"
             :in-theory (e/d (f2 m2 sum)
                             (floor2-if-f2 mod2-is-m2 +-IS-SUM))))))

(defret c-pattern2-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                reducedp)
           (equal (sum-list-eval RES-PP-LST a)
                  (f2 (sum-list-eval pp-lst a))))
  :fn c-pattern2-reduce
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (nth 3 x))
                    (:free (x) (nth 2 x))
                    (:free (x) (nth 1 x))
                    (:free (x) (nth 0 x)))
           :in-theory (e/d (c-pattern2-reduce
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-evlt-of-ex-from-rp
                            rp-trans)))))

(defret c-pattern2-reduce-correct-with-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                reducedp)
           (equal (sum (sum-list-eval RES-PP-LST a)
                       rest)
                  (sum (f2 (sum-list-eval pp-lst a))
                       rest)))
  :fn c-pattern2-reduce
  :hints (("Goal")))

(defret c-pattern2-reduce-implies-empty-c-lst-s-lst
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                reducedp)
           (and (not s-lst)
                (not c-lst)))
  :fn c-pattern2-reduce
  :rule-classes :forward-chaining
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x) (nth 3 x))
                    (:free (x) (nth 2 x))
                    (:free (x) (nth 1 x))
                    (:free (x) (nth 0 x)))
           :in-theory (e/d (c-pattern2-reduce
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-evlt-of-ex-from-rp
                            rp-trans)))))

#|(defret c-pattern2-reduce-correct-integerp
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                reducedp
                (integerp (sum-list-eval PP-LST a)))
           (and (integerp (sum-list-eval RES-PP-LST a))))
  :fn c-pattern2-reduce
  :hints (("Goal"
           :in-theory (e/d (c-pattern2-reduce) ()))))||#

(encapsulate
  nil

  (local
   (use-arith-5 t))
  (defthm f2-of-1
    (and (equal (f2 (sum a b 1))
                (sum (m2 (sum a b))
                     (f2 (sum a b))))
         (equal (f2 (sum a 1))
                (sum (m2 (sum a))
                     (f2 (sum a)))))
    :hints (("Goal"
             :in-theory (e/d (m2
                              f2
                              sum)
                             (+-IS-SUM
                              floor2-if-f2
                              mod2-is-m2))))))

#|(defret c-pattern3-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                reducedp)
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)
                (equal (sum (sum-list-eval res-s-lst a)
                            (sum-list-eval res-pp-lst a)
                            (sum-list-eval res-c-lst a))
                       (f2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))))
  :fn C-PATTERN3-REDUCE
  :hints (("Goal"
           :in-theory (e/d (C-PATTERN3-REDUCE) ()))))||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-c-instance lemmas

(defthmd lte-implies-bitp
  (implies (AND (lte 0 x)
                (integerp x)
                (lte x 1))
           (bitp x))
  :hints (("Goal"
           :in-theory (e/d (bitp
                            lte
                            rw-dir2)
                           (rw-dir1)))))

(defthmd lte-implies-0
  (implies (AND (lte 0 (f2 x))
                (lte (f2 x) 0))
           (equal (f2 x) 0))
  :hints (("Goal"
           :in-theory (e/d (bitp
                            lte
                            rw-dir2)
                           (rw-dir1)))))


(defret create-c-instance-is-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and
            (valid-sc-subterms res-s-lst a)
            (valid-sc-subterms res-pp-lst a)
            (valid-sc-subterms res-c-lst a)))
  :fn create-c-instance
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-pattern1-reduce-correct)
                 (:instance get-max-min-val-correct
                            (term (list
                                   'c
                                   (list 'quote
                                         (calculate-c-hash
                                          (create-list-instance
                                           (mv-nth 0
                                                   (c-pattern1-reduce s-lst pp-lst c-lst)))
                                          (create-list-instance
                                           (mv-nth 1
                                                   (c-pattern1-reduce s-lst pp-lst c-lst)))
                                          (create-list-instance
                                           (mv-nth 2
                                                   (c-pattern1-reduce s-lst pp-lst c-lst)))))
                                   (create-list-instance (mv-nth 0
                                                                 (c-pattern1-reduce s-lst pp-lst c-lst)))
                                   (create-list-instance (mv-nth 1
                                                                 (c-pattern1-reduce s-lst pp-lst c-lst)))
                                   (create-list-instance
                                    (mv-nth 2
                                            (c-pattern1-reduce s-lst pp-lst c-lst)))))))
           :expand ((:free (x) (valid-sc (cons 'c x) a))
                    (:free (x) (valid-sc (cons 'quote x) a)))
           :in-theory (e/d* (create-c-instance
                             valid-sc-single-step
                             sum-comm-1-loop-stopper
                             sum-comm-2-loop-stopper
                             rp-trans-lst-of-consp
                             lte-implies-bitp
                             lte-implies-0)
                            (c-pattern1-reduce-correct
                             (:DEFINITION INCLUDE-FNC-SUBTERMS)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC)
                             (:REWRITE LTE-IMPLIES-0)
                             (:REWRITE F2-OF-BIT)
                             (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                             (:REWRITE C-PATTERN0-REDUCE-CORRECT)
                             (:REWRITE EQUIVALENCE-OF-TWO-F2)
                             (:TYPE-PRESCRIPTION QUOTED-LISTP)
                             (:DEFINITION SUM-LIST-EVAL)
                             (:REWRITE VALID-SC-SUBTERMS-CONS)
                             get-max-min-val-correct
                             sum-comm-1
                             rp-trans
                             (:REWRITE LTE-AND-GTE-IMPLIES)
                             sum-comm-2
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE DEFAULT-CAR)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:DEFINITION TRANS-LIST)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:TYPE-PRESCRIPTION F2)
                             (:DEFINITION IS-SYNP$INLINE)
                             ;;TO-LIST*-SUM-EVAL
                             (:TYPE-PRESCRIPTION TRANS-LIST)
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_s-C-RES_WHEN_MULT-FORMULA-CHECKS)
                             INCLUDE-FNC
                             RP-TRANS-LST
                             VALID-SC

                             )))))

(defret create-c-instance-is-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (equal (sum (sum-list-eval res-s-lst a)
                            (sum-list-eval res-pp-lst a)
                            (sum-list-eval res-c-lst a))
                       (f2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))))
  :fn create-c-instance
  :hints (
          ("Goal"
           :do-not-induct t
           :use ((:instance c-pattern1-reduce-correct)
                 (:instance get-max-min-val-correct
                            (term (list
                                   'c
                                   (list 'quote
                                         (calculate-c-hash
                                          (create-list-instance
                                           (mv-nth 0
                                                   (c-pattern1-reduce s-lst pp-lst c-lst)))
                                          (create-list-instance
                                           (mv-nth 1
                                                   (c-pattern1-reduce s-lst pp-lst c-lst)))
                                          (create-list-instance
                                           (mv-nth 2
                                                   (c-pattern1-reduce s-lst pp-lst c-lst)))))
                                   (create-list-instance (mv-nth 0
                                                                 (c-pattern1-reduce s-lst pp-lst c-lst)))
                                   (create-list-instance (mv-nth 1
                                                                 (c-pattern1-reduce s-lst pp-lst c-lst)))
                                   (create-list-instance
                                    (mv-nth 2
                                            (c-pattern1-reduce s-lst pp-lst c-lst)))))))
           :expand (
                    (:free (x) (valid-sc (cons 'c x) a))
                    (:free (x) (valid-sc (cons 'quote x) a)))
           :in-theory (e/d* (create-c-instance
                             valid-sc-single-step
                             sum-comm-1-loop-stopper
                             sum-comm-2-loop-stopper
                             (:REWRITE REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE REGULAR-RP-EVL-OF_BITP_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                             rp-trans-lst-of-consp
                             lte-implies-bitp
                             lte-implies-0)
                            (c-pattern1-reduce-correct
                             (:DEFINITION VALID-SC-SUBTERMS)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                             get-max-min-val-correct
                             sum-comm-1
                             rp-trans
                             (:REWRITE LTE-AND-GTE-IMPLIES)
                             sum-comm-2
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE DEFAULT-CAR)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:DEFINITION TRANS-LIST)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:TYPE-PRESCRIPTION F2)
                             (:DEFINITION IS-SYNP$INLINE)
                             ;;TO-LIST*-SUM-EVAL
                             (:TYPE-PRESCRIPTION TRANS-LIST)
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_s-C-RES_WHEN_MULT-FORMULA-CHECKS)
                             INCLUDE-FNC
                             RP-TRANS-LST
                             VALID-SC

                             )))))

(defret create-c-instance-is-correct-with-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (equal (sum (sum-list-eval res-s-lst a)
                            (sum-list-eval res-pp-lst a)
                            (sum-list-eval res-c-lst a)
                            rest)
                       (sum (f2 (sum (sum-list-eval s-lst a)
                                     (sum-list-eval pp-lst a)
                                     (sum-list-eval c-lst a)))
                            rest))
                ))
  :fn create-c-instance
  :hints (("Goal"
           :do-not-induct t)))

(std::defret
 create-c-instance-is-correct-singled-out
 (implies (and (rp-evl-meta-extract-global-facts :state state)
               (mult-formula-checks state)
               (valid-sc-subterms s-lst a)
               (valid-sc-subterms pp-lst a)
               (valid-sc-subterms c-lst a))
          (and (equal (sum-list-eval res-c-lst a)
                      (sum (f2 (sum (sum-list-eval s-lst a)
                                    (sum-list-eval pp-lst a)
                                    (sum-list-eval c-lst a)))
                           (-- (sum-list-eval res-s-lst a))
                           (-- (sum-list-eval res-pp-lst a))))
               ))
 :fn create-c-instance
 :hints (("Goal"
          :use ((:instance create-c-instance-is-correct))
          :in-theory (disable create-c-instance-is-correct)
          :do-not-induct t)))

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
           :in-theory (e/d* (light-s-of-s-fix-lst
                             (:REWRITE REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
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
(local
 (defcong rp-equal-subterms equal (sum-list-eval lst a) 1
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance TO-LIST*-SUM-EVAL)
                  (:instance TO-LIST*-SUM-EVAL
                             (lst LST-EQUIV)))
            :in-theory (e/d () (TO-LIST*-SUM-EVAL))))))

(defthmd m2-of-oddp-v2
  (IMPLIES (AND (ODDP A)
                (CASE-SPLIT (INTEGERP A))
                (SYNTAXP (ATOM A)))
           (and (EQUAL (M2 (SUM B c a)) (M2 (SUM 1 B c)))
                (EQUAL (M2 (SUM B c d a)) (M2 (SUM 1 B c d)))))
  :hints (("Goal"
           :in-theory (e/d (m2-of-oddp)
                           (
                            (:REWRITE REDUCE-SAME-ARGS-OF-M2)
                            +-IS-SUM
                            floor2-if-f2
                            mod2-is-m2)))))

(defthmd sum-of-not-integerp-v2
  (implies (not (integerp x))
           (and (equal (sum y x) (sum y))
                (equal (sum x y) (sum y))))
  :hints (("Goal"
           :in-theory (e/d (sum-of-not-integerp) ()))))

(defthmd m2-of-evenp-v2
  (IMPLIES (AND (EVENP A))
           (and (EQUAL (M2 (SUM b c d A)) (M2 (sum b c d)))
                (EQUAL (M2 (SUM b c A)) (M2 (sum b c)))))
  :hints (("Goal"
           :use ((:instance m2-of-evenp
                            (b (sum b c d)))
                 (:instance m2-of-evenp
                            (b (sum b c))))
           :in-theory (e/d () ()))))

(defthm m2-of-1-v3
  (AND (EQUAL (M2 (SUM X Y 1))
              (SUM (-- (M2 (SUM X Y))) 1))
       (EQUAL (M2 (SUM X Y z 1))
              (SUM (-- (M2 (SUM X Y z))) 1)))
  :hints (("Goal"
           :use ((:instance m2-of-1-v2
                            (y (sum y z)))
                 (:instance m2-of-1-v2))
           :in-theory (e/d () (m2-of-1-v2)))))

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
           :use ((:instance rp-evlt-lst-of-rp-equal-lst
                            (subterm1 (LIST-TO-LST (CADDDR (EX-FROM-RP
                                                            CUR-S))))
                            (subterm2 (MV-NTH 1
                                              (LIGHT-S-OF-S-FIX S-ARG PP-ARG C-ARG-LST))))
                 (:instance light-s-of-s-fix-correct
                            (s s-arg)
                            (pp pp-arg)
                            (c-lst c-arg-lst)))
           :do-not-induct t
           :cases ((evenp x))
           :in-theory (e/d (single-c-try-merge-params-aux
                            m2-of-oddp-v2
                            m2-of-evenp
                            m2-of-evenp-v2

                            sum-of-not-integerp-v2
                            sum-of-not-integerp
                            ODDP
                            single-c-try-merge-params-correct-dummy-lemma
                            move-sum-over-to-the-same-side
                            single-c-try-merge-params-correct-dummy-lemma-2
                            move-sum-over-to-the-same-side
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-termp
                            rp-evlt-lst-of-rp-equal-lst

                            valid-sc
                            eval-and-all
                            evenp
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
                            SUM-CANCEL-COMMON
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-of-1-merge

(defret get-c-args-correct
  (and (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (mult-formula-checks state)
                     valid)
                (equal (f2 (sum (sum-list (rp-evlt s-args a))
                                (sum-list (rp-evlt pp-args a))
                                (sum-list-eval c-arg-lst a)))
                       (rp-evlt c a)))
       (implies (valid-sc c a)
                (and (valid-sc s-args a)
                     (valid-sc pp-args a)
                     (valid-sc-subterms c-arg-lst a))))
  :fn get-c-args
  :hints (("Goal"
           :expand (VALID-SC ''NIL A)
           :in-theory (e/d (get-c-args
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (valid-sc
                            eval-and-all
                            rp-evlt-of-ex-from-rp
                            NOT-INCLUDE-RP-MEANS-VALID-SC
                            NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                            ex-from-rp
                            (:REWRITE RP-EVL-OF-IF-CALL))))))

(defret get-c-args-correct-valid-sc
  (and (implies (valid-sc c a)
                (and (valid-sc s-args a)
                     (valid-sc pp-args a)
                     (valid-sc-subterms c-arg-lst a))))
  :fn get-c-args
  :hints (("Goal"

           :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (valid-sc
                            eval-and-all
                            rp-evlt-of-ex-from-rp
                            NOT-INCLUDE-RP-MEANS-VALID-SC
                            NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                            ex-from-rp
                            (:REWRITE RP-EVL-OF-IF-CALL))))))

(defthmd rp-term-listp-of-cons
  (implies (consp x)
           (equal (rp-term-listp x)
                  (and
                   (rp-termp (car x))
                   (rp-term-listp (cdr x)))))
  :hints (("Goal"
           :expand (rp-term-listp x)
           :in-theory (e/d () ()))))

(defthm rp-term-listp-of-cons-2
  (implies (and (rp-term-listp x)
                (consp x))
           (and
            (rp-termp (car x))
            (rp-term-listp (cdr x))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :expand (rp-term-listp x)
           :in-theory (e/d () ()))))

(defthm valid-sc-subterms-cons-2
  (implies (and (valid-sc-subterms lst a)
                (consp lst))
           (and (valid-sc (car lst) a)
                (valid-sc-subterms (cdr lst) a)))
  :rule-classes :forward-chaining)

(defthm dummy-sum-reduce-common-1
  (equal (equal (sum x y z a)
                (sum p a q))
         (equal (sum x y z)
                (sum p q))))

(defthm valid-sc-subterms-of-consed
  (equal (VALID-SC-SUBTERMS (cons x y) A)
         (and (valid-sc x a)
              (valid-sc-subterms y a))))

(defthm valid-sc-subterms-of-consed-2
  (implies (and (valid-sc x a)
                (valid-sc-subterms y a))
           (VALID-SC-SUBTERMS (cons x y) A)))

(defthm rp-term-listp-of-consed
  (equal (rp-term-listp (cons x y))
         (and (rp-termp x)
              (rp-term-listp y)))
  :hints (("Goal"
           :expand (rp-term-listp (cons x y))
           :in-theory (e/d () ()))))

(defthm rp-term-listp-of-consed-2
  (implies (and (rp-termp x)
                (rp-term-listp y))
           (rp-term-listp (cons x y)))
  :hints (("Goal"
           :expand (rp-term-listp (cons x y))
           :in-theory (e/d () ()))))

(defthm valid-sc-subterms-of-single-list
  (equal (VALID-SC-SUBTERMS (list x) A)
         (valid-sc x a)))

(defthm rp-term-listp-of-single-list
  (iff (rp-term-listp (list x))
       (rp-termp x))
  :hints (("Goal"
           :expand (rp-term-listp (list x))
           :in-theory (e/d () ()))))

(defthm valid-sc-subterms-cdr
  (implies (and (consp term)
                (or (and (valid-sc term a)
                         (not (equal (car term) 'rp))
                         (not (equal (car term) 'quote))
                         (not (equal (car term) 'if)))
                    (valid-sc-subterms term a)))
           (valid-sc-subterms (cdr term) a))
  :hints (("Goal"
           :in-theory (e/d (valid-sc is-if is-rp) ()))))

(std::defretd
 get-c-args-correct-reverse-1
 (implies (and (rp-evl-meta-extract-global-facts :state state)
               (mult-formula-checks state)
               valid)
          (equal (rp-evlt c a)
                 (f2 (sum (sum-list (rp-evlt (caddr (ex-from-rp c)) a))
                          (sum-list (rp-evlt (cadddr (ex-from-rp c)) a))
                          (sum-list-eval (list-to-lst (car (cddddr (ex-from-rp c)))) a)))))
 :fn GET-C-ARGS
 :hints (("Goal"
          :use ((:instance get-c-args-correct))
          :in-theory (e/d (GET-C-ARGS
                           rp-evlt-of-ex-from-rp-reverse-only-atom)
                          (get-c-args-correct
                           rp-trans
                           (:DEFINITION VALID-SC)
                           (:DEFINITION INCLUDE-FNC)
                           (:REWRITE VALID-SC-CADDR)
                           (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                           (:REWRITE ACL2::ACL2-NUMBERP-X)
                           (:REWRITE VALID-SC-SUBTERMS-CONS)
                           (:REWRITE
                            ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                           (:REWRITE VALID-SC-CADDDR)
                           rp-evlt-of-ex-from-rp)))))

(std::defretd
 get-c-args-correct-reverse-2
 (implies (and (rp-evl-meta-extract-global-facts :state state)
               (mult-formula-checks state)
               valid)
          (equal (rp-evlt c a)
                 (f2 (sum (sum-list (rp-evlt s-args a))
                          (sum-list (rp-evlt pp-args a))
                          (sum-list-eval c-arg-lst a)))))
 :fn GET-C-ARGS
 :hints (("Goal"
          :use ((:instance get-c-args-correct))
          :in-theory (e/d ()
                          (get-c-args-correct
                           rp-trans
                           rp-evlt-of-ex-from-rp)))))

(defthmd rp-term-listp-implies-true-listp
  (implies (rp-term-listp lst)
           (true-listp lst)))

(defthmd dummy-true-listp-lemma
  (implies (and (rp-termp single-c)
                (consp (MV-NTH 1 (GET-C-ARGS single-c)))
                (equal (car (MV-NTH 1 (GET-C-ARGS single-c)))
                       'list)
                (MV-NTH 4 (GET-C-ARGS single-c)))
           (RP-TERM-LISTP (CDR (MV-NTH 1 (GET-C-ARGS single-c)))))
  :hints (("Goal"
           :in-theory (e/d (GET-C-ARGS
;rp-termp-implies-true-listp
                            )
                           (ex-from-rp)))))

(defret c-of-1-merge-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc single-c1 a)
                (valid-sc single-c2 a))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn c-of-1-merge
  :hints (("Goal"
           :in-theory (e/d (c-of-1-merge) ()))))

(std::defretd
 GET-C-ARGS-implies-single-c-instance
 (implies (and valid
               (rp-evl-meta-extract-global-facts :state state)
               (mult-formula-checks state))
          (equal (rp-evlt c a)
                 (c 0
                    (rp-evlt s-args a)
                    (rp-evlt pp-args a)
                    (rp-evlt (create-list-instance C-ARG-LST) a))))
 :fn get-c-args
 :rule-classes :rewrite
 :hints (("Goal"
          :in-theory (e/d* (GET-C-ARGS
                            regular-eval-lemmas)
                           ()))))

#|(defthm when-car-of-LIST-TO-LST-is-1
  (implies (equal (car (LIST-TO-LST term)) ''1)
           (equal (car term) 'list))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (LIST-TO-LST) ()))))||#

(defthmd LIST-TO-LST-lemma1
  (implies (and (equal (cdr (LIST-TO-LST term))
                       (LIST-TO-LST term2))
                (equal (car (LIST-TO-LST term)) ''1)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list (rp-evlt term a))
                  (sum-list (cons '1
                                  (rp-evlt term2 a)))))

  :rule-classes :rewrite
  :hints (("Goal"
           :in-theory (e/d* (LIST-TO-LST
                             regular-eval-lemmas)
                            (rp-trans
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)))))

#|(defthm f2-plus-f2-of-1
  (equal (sum (f2 (sum a b c 1))
              (f2 (sum a b c)))
         (sum a b c))
  :hints (("Goal"
           :in-theory (e/d (SUM-OF-REPEATED-TO-TIMES2)
                           ()))))||#

(defthmd minus-of-sum-reverse
  (equal (sum (-- a) (-- b))
         (-- (sum a b)))
  :hints (("goal" :in-theory (e/d (sum --) (+-is-sum)))))

#|(defthm f2-plus-f2-of-1-corolo
  (equal (sum (-- (f2 (sum a b c 1)))
              (-- (f2 (sum a b c))))
         (-- (sum a b c)))
  :hints (("Goal"
           :use ((:instance f2-plus-f2-of-1))
           :in-theory (e/d (SUM-OF-REPEATED-TO-TIMES2
                            minus-of-sum-reverse)
                           (f2-plus-f2-of-1
                            D2-OF-MINUS
                            D2-OF-TIMES2
                            MINUS-OF-SUM)))))||#

(DEFTHMd
  M2-PLUS-F2-OF-THE-SAME-ARGUMENT-reverse
  (and (EQUAL (F2 (SUM 1 X))
              (SUM (M2 X) (F2 X)))
       (EQUAL (F2 (SUM X y z 1))
              (SUM (M2 (SUM X y z)) (F2 (SUM X y z)))))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D ()
                    ()))))

(defthm sum-of-m2-f2-f2-of-the-same-argument
  (and (equal (sum (m2 x) (f2 x) (f2 x))
              (ifix x))
       (equal (sum (-- (m2 x)) (-- (f2 x)) (-- (f2 x)))
              (-- x)))
  :hints (("Goal"
           :in-theory (e/d (m2 f2 sum rw-dir2
                               --
                               (:REWRITE ACL2::|(* a (/ a) b)|)
                               (:REWRITE ACL2::|(* x (+ y z))|)
                               (:REWRITE ACL2::|(* x (- y))|)
                               (:REWRITE ACL2::|(+ (if a b c) x)|)
                               (:REWRITE ACL2::|(+ 0 x)|)
                               (:REWRITE ACL2::|(+ c (+ d x))|)
                               (:REWRITE ACL2::|(+ x x)|)
                               (:REWRITE ACL2::|(- (* c x))|)
                               (:REWRITE ACL2::|(- (+ x y))|)
                               (:REWRITE ACL2::|(- (- x))|)
                               (:REWRITE ACL2::|(- (if a b c))|)
                               (:REWRITE ACL2::|(equal (- x) (- y))|)
                               (:REWRITE ACL2::|(equal (if a b c) x)|)
                               (:REWRITE ACL2::|(floor x 2)| . 1)
                               (:REWRITE ACL2::|(mod x 2)| . 1)
                               (:REWRITE ACL2::BUBBLE-DOWN-+-MATCH-1)
                               (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
                               (:REWRITE IFIX-OPENER)
                               (:REWRITE ACL2::INTEGERP-+-REDUCE-CONSTANT)
                               (:REWRITE ACL2::NORMALIZE-ADDENDS))
                           (+-is-sum
                            rw-dir1
                            (:DEFINITION FLOOR)
                            (:REWRITE MOD2-IS-M2)
                            floor2-if-f2)))))

(defret create-s-instance-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a))
           (equal (sum-list-eval s-res-lst a)
                  (sum (-- (sum
                            (sum-list-eval pp-res-lst a)
                            (sum-list-eval c-res-lst a)))
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))))
  :fn create-s-instance
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance create-s-instance-correct))
           :in-theory (e/d ()
                           (create-s-instance-correct)))))

(defret c-of-1-merge-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc single-c1 a)
                (valid-sc single-c2 a)
                merge-success)
           (equal (sum (sum-list-eval res-s-lst a)
                       (sum-list-eval res-pp-lst a)
                       (sum-list-eval res-c-lst a))
                  (sum (rp-evlt single-c1 a)
                       (rp-evlt single-c2 a))))
  :fn c-of-1-merge
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (c-of-1-merge
                             M2-PLUS-F2-OF-THE-SAME-ARGUMENT-reverse
                             LIST-TO-LST-lemma1
                             ;;GET-C-ARGS
                             (:REWRITE REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS)
                             GET-C-ARGS-implies-single-c-instance
                             )
                            (GET-C-ARGS-CORRECT
                             sum-of-f2s
                             M2-PLUS-F2-OF-THE-SAME-ARGUMENT
                             )))))

(defret c-of-1-merge-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc single-c1 a)
                (valid-sc single-c2 a)
                merge-success)
           (equal (sum-list-eval res-c-lst a)
                  (sum (-- (sum (sum-list-eval res-s-lst a)
                                (sum-list-eval res-pp-lst a)))
                       (rp-evlt single-c1 a)
                       (rp-evlt single-c2 a))))
  :fn c-of-1-merge
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-of-1-merge-correct))
           :in-theory (e/d* ()
                            (c-of-1-merge-correct)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-sum-merge

(defret-mutual
  c-sum-merge-correct-valid-sc
  (defret single-c-try-merge-correct-valid-sc
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc single-c1 a)
                  (valid-sc single-c2 a)
                  ;;(rp-termp single-c1)
                  ;;(rp-termp single-c2)
                  merge-success)
             (and
              (valid-sc coughed-s a)
              (valid-sc-subterms coughed-pp-lst a)
              (valid-sc-subterms produced-c-lst a)))
    :fn single-c-try-merge)
  (defret c-sum-merge-lst-aux-correct-valid-sc
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc single-c1 a)
                  (valid-sc-subterms c2-lst a)
                  ;;(rp-termp single-c1)
                  ;;(rp-term-listp c2-lst)
                  merge-success)
             (and
              (valid-sc coughed-s a)
              (valid-sc-subterms coughed-pp-lst a)
              (valid-sc-subterms produced-c-lst a)
              (valid-sc-subterms updated-c2-lst a)))
    :fn c-sum-merge-lst-aux)
  (defret c-sum-merge-lst-correct-valid-sc
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc single-c1 a)
                  (valid-sc-subterms c2-lst a)
                  ;;(rp-termp single-c1)
                  ;;(rp-term-listp c2-lst)
                  )
             (and
              (valid-sc coughed-s a)
              (valid-sc-subterms coughed-pp-lst a)
              (valid-sc-subterms new-c2-lst a)
              ))
    :fn c-sum-merge-lst)
  (defret c-sum-merge-lst-lst-correct-valid-sc
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms c1-lst a)
                  (valid-sc-subterms c2-lst a)
                  ;;(rp-term-listp c1-lst)
                  ;;(rp-term-listp c2-lst)
                  )
             (and
              (valid-sc coughed-s a)
              (valid-sc-subterms coughed-pp-lst a)
              (valid-sc-subterms updated-c2-lst a)
              ))
    :fn c-sum-merge-lst-lst)
  (defret c-sum-merge-correct-valid-sc
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms c1-lst a)
                  (valid-sc-subterms c2-lst a)
                  ;;(rp-term-listp c1-lst)
                  ;;;;(rp-term-listp c2-lst)
                  )
             (and
              (valid-sc coughed-s a)
              (valid-sc-subterms coughed-pp-lst a)
              (valid-sc-subterms c-merged-lst a)
              (valid-sc-subterms to-be-coughed-c-lst a)
              ))
    :fn c-sum-merge)
  (defret c-sum-merge-aux-correct-valid-sc
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms c1-lst a)
                  (valid-sc-subterms c2-lst a)
                  ;;(rp-term-listp c1-lst)
                  ;;(rp-term-listp c2-lst)
                  )
             (and
              (valid-sc coughed-s a)
              (valid-sc-subterms coughed-pp-lst a)
              (valid-sc-subterms c-merged-lst a)
              (valid-sc-subterms to-be-coughed-c-lst a)
              ))
    :fn c-sum-merge-aux)

  :hints (("Goal"
           :do-not-induct t
           :expand ((C-SUM-MERGE-LST SINGLE-C1 C2-LST)
                    (SINGLE-C-TRY-MERGE SINGLE-C1 SINGLE-C2)
                    (C-SUM-MERGE-LST-AUX SINGLE-C1 C2-LST)
                    (C-SUM-MERGE-AUX C1-LST C2-LST
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-LST ''0 C2-LST)
                    (C-SUM-MERGE-AUX C1-LST NIL
                                     :CLEAN-C1-LST NIL
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-AUX C1-LST NIL
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-AUX NIL C2-LST
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE C1-LST C2-LST
                                 :AUTO-SWAP AUTO-SWAP
                                 :CLEAN-C1-LST CLEAN-C1-LST
                                 :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-LST-LST C1-LST C2-LST))
           :in-theory (e/d (sum-of-repeated-to-times2
                            rp-term-listp-of-cons-2

                            valid-sc-subterms-cons-2
                            rp-term-listp-of-consed-2
                            valid-sc-subterms-of-consed-2
                            get-c-args-correct-reverse-2
                            f2-of-times2-reverse
                            c-fix-arg-aux-correct-lemma)
                           (NOT-INCLUDE-RP-MEANS-VALID-SC

                            D2-OF-MINUS
                            SUM-OF-F2S

                            f2-of-times2

                            get-c-args-correct
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            (:DEFINITION INCLUDE-FNC)
                            rp-term-listp-of-cons
                            rp-term-listp-of-consed
                            valid-sc-subterms-of-consed
                            valid-sc-subterms-cons
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            REWRITING-POSITIVE-LTE-GTE-GT-LT
                            NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                            rp-termp
                            VALID-SC-SUBTERMS
                            rp-term-listp)))))

(defthmd c-sum-merge-correct-dummy-sum-lemma
  (implies (equal (sum x1 x2 x3 x4) a)
           (equal (sum x1 x2 x3 x4 b)
                  (sum a b))))

(defthm to-sum-list-eval-for-list-instances
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (consp term)
                (equal (car term) 'list))
           (equal (sum-list (rp-evlt term a))
                  (sum-list-eval (cdr term) a))))

(value-triple (hons-clear 't))

(defret-mutual
  c-sum-merge-correct
  (defret single-c-try-merge-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc single-c1 a)
                  (valid-sc single-c2 a)
                  (rp-termp single-c1)
                  (rp-termp single-c2)
                  merge-success)
             (equal (sum (sum-list (rp-evlt coughed-s a))
                         (sum-list-eval coughed-pp-lst a)
                         (sum-list-eval produced-c-lst a))
                    (sum (rp-evlt single-c1 a)
                         (rp-evlt single-c2 a))))
    :fn single-c-try-merge)
  (defret c-sum-merge-lst-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc single-c1 a)
                  (valid-sc-subterms c2-lst a)
                  (rp-termp single-c1)
                  (rp-term-listp c2-lst)
                  merge-success)
             (equal (sum (sum-list (rp-evlt coughed-s a))
                         (sum-list-eval coughed-pp-lst a)
                         (sum-list-eval produced-c-lst a)
                         (sum-list-eval updated-c2-lst a))
                    (sum (rp-evlt single-c1 a)
                         (sum-list-eval c2-lst a))))
    :fn c-sum-merge-lst-aux)
  (defret c-sum-merge-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc single-c1 a)
                  (valid-sc-subterms c2-lst a)
                  (rp-termp single-c1)
                  (rp-term-listp c2-lst))
             (equal (sum (sum-list (rp-evlt coughed-s a))
                         (sum-list-eval coughed-pp-lst a)
                         (sum-list-eval new-c2-lst a))
                    (sum (rp-evlt single-c1 a)
                         (sum-list-eval c2-lst a))))
    :fn c-sum-merge-lst)
  (defret c-sum-merge-lst-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms c1-lst a)
                  (valid-sc-subterms c2-lst a)
                  (rp-term-listp c1-lst)
                  (rp-term-listp c2-lst))
             (equal (sum (sum-list (rp-evlt coughed-s a))
                         (sum-list-eval coughed-pp-lst a)
                         (sum-list-eval updated-c2-lst a))
                    (sum (sum-list-eval c1-lst a)
                         (sum-list-eval c2-lst a))))
    :fn c-sum-merge-lst-lst)
  (defret c-sum-merge-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms c1-lst a)
                  (valid-sc-subterms c2-lst a)
                  (rp-term-listp c1-lst)
                  (rp-term-listp c2-lst))
             (equal (sum (sum-list (rp-evlt coughed-s a))
                         (sum-list-eval coughed-pp-lst a)
                         (sum-list-eval c-merged-lst a)
                         (sum-list-eval to-be-coughed-c-lst a)
                         (sum-list-eval to-be-coughed-c-lst a))
                    (sum (sum-list-eval c1-lst a)
                         (sum-list-eval c2-lst a))))
    :fn c-sum-merge)
  (defret c-sum-merge-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms c1-lst a)
                  (valid-sc-subterms c2-lst a)
                  (rp-term-listp c1-lst)
                  (rp-term-listp c2-lst))
             (equal (sum (sum-list (rp-evlt coughed-s a))
                         (sum-list-eval coughed-pp-lst a)
                         (sum-list-eval c-merged-lst a)
                         (sum-list-eval to-be-coughed-c-lst a)
                         (sum-list-eval to-be-coughed-c-lst a))
                    (sum (sum-list-eval c1-lst a)
                         (sum-list-eval c2-lst a))))
    :fn c-sum-merge-aux)

  :hints (("Goal"
           :do-not-induct t
           :expand ((C-SUM-MERGE-LST SINGLE-C1 C2-LST)
                    (SINGLE-C-TRY-MERGE SINGLE-C1 SINGLE-C2)
                    (C-SUM-MERGE-LST-AUX SINGLE-C1 C2-LST)
                    (C-SUM-MERGE-AUX C1-LST C2-LST
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-LST ''0 C2-LST)
                    (C-SUM-MERGE-AUX C1-LST NIL
                                     :CLEAN-C1-LST NIL
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-AUX C1-LST NIL
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-AUX NIL C2-LST
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE C1-LST C2-LST
                                 :AUTO-SWAP AUTO-SWAP
                                 :CLEAN-C1-LST CLEAN-C1-LST
                                 :COUGH-C-LST COUGH-C-LST)
                    (C-SUM-MERGE-LST-LST C1-LST C2-LST))
           :in-theory (e/d (sum-of-repeated-to-times2
                            c-fix-arg-aux-with-cond
                            rp-term-listp-of-cons-2
                            c-sum-merge-correct-dummy-sum-lemma
                            valid-sc-subterms-cons-2
                            rp-term-listp-of-consed-2
                            valid-sc-subterms-of-consed-2
                            get-c-args-correct-reverse-2
                            f2-of-times2-reverse
                            dummy-true-listp-lemma
                            rp-term-listp-implies-true-listp
                            c-fix-arg-aux-correct-lemma)

                           (NOT-INCLUDE-RP-MEANS-VALID-SC
                            (:REWRITE
                             ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                            (:REWRITE ACL2::ACL2-NUMBERP-X)
                            (:DEFINITION IS-FALIST)
                            (:REWRITE ACL2::RATIONALP-X)
                            (:DEFINITION EQ)
                            (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                            ;;(:TYPE-PRESCRIPTION BINARY-SUM)
                            (:REWRITE
                             ACL2::ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)
                            D2-OF-MINUS
                            SUM-OF-F2S
                            f2-of-times2
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                            get-c-args-correct
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            (:DEFINITION INCLUDE-FNC)
                            rp-term-listp-of-cons
                            rp-term-listp-of-consed
                            valid-sc-subterms-of-consed
                            valid-sc-subterms-cons
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            REWRITING-POSITIVE-LTE-GTE-GT-LT
                            NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                            rp-termp
                            VALID-SC-SUBTERMS
                            single-c-try-merge-params-correct-2

                            c-of-1-merge-correct-singled-out

                            rp-term-listp)))
          ("Subgoal *1/5"
           :use ((:instance single-c-try-merge-params-correct-2
                            (x (sum (SUM-LIST (RP-EVLT (MV-NTH 2 (GET-C-ARGS SINGLE-C2))
                                                       A))
                                    (SUM-LIST-EVAL (MV-NTH 3 (GET-C-ARGS SINGLE-C2))
                                                   A)))
                            (C-HASH-CODE (MV-NTH 0 (GET-C-ARGS SINGLE-C1)))
                            (s-lst (CDR (MV-NTH 1 (GET-C-ARGS SINGLE-C2))))
                            (s-arg (MV-NTH 1 (GET-C-ARGS SINGLE-C1)))
                            (pp-arg (MV-NTH 2 (GET-C-ARGS SINGLE-C1)))
                            (c-arg-lst (MV-NTH 3 (GET-C-ARGS SINGLE-C1))))))))

#|(defthm dummy-sum-cancel-3
  (equal (equal (sum b c d a)
                (sum e f a))
         (equal (sum b c d)
                (sum e f))))||#

(defret c-sum-merge-lst-lst-correct-with-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                (rp-term-listp c1-lst)
                (rp-term-listp c2-lst))
           (equal (sum (sum-list (rp-evlt coughed-s a))
                       (sum-list-eval coughed-pp-lst a)
                       (sum-list-eval updated-c2-lst a)
                       rest)
                  (sum (sum-list-eval c1-lst a)
                       (sum-list-eval c2-lst a)
                       rest)))
  :fn c-sum-merge-lst-lst
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (SUM-CANCEL-COMMON) ()))))

(defret c-sum-merge-correct-with-rest-empty-c-cough-lst=nil
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                (rp-term-listp c1-lst)
                (rp-term-listp c2-lst)
                (not cough-c-lst))
           (equal (sum (sum-list (rp-evlt coughed-s a))
                       (sum-list-eval coughed-pp-lst a)
                       (sum-list-eval c-merged-lst a)
                       rest)
                  (sum (sum-list-eval c1-lst a)
                       (sum-list-eval c2-lst a)
                       rest)))
  :fn c-sum-merge
  :hints (("Goal"
           :use ((:instance c-sum-merge-correct (cough-c-lst nil)))
           :expand ((C-SUM-MERGE C1-LST C2-LST
                                 :AUTO-SWAP AUTO-SWAP
                                 :CLEAN-C1-LST CLEAN-C1-LST
                                 :COUGH-C-LST NIL)
                    (C-SUM-MERGE-AUX (MV-NTH 0 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                     (MV-NTH 1 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST NIL
                                     :LIMIT (SUM LIMIT -1)))
           :in-theory (e/d (C-SUM-MERGE
                            c-sum-merge-aux)
                           (c-sum-merge-correct
                            c-sum-merge-correct)))))

(defret c-sum-merge-when--c-cough-lst=nil
  (implies (not cough-c-lst)
           (not to-be-coughed-c-lst))
  :fn c-sum-merge
  ;;:rule-classes :forward-chaining
  :hints (("Goal"
           :expand ((C-SUM-MERGE C1-LST C2-LST
                                 :AUTO-SWAP AUTO-SWAP
                                 :CLEAN-C1-LST CLEAN-C1-LST
                                 :COUGH-C-LST NIL)
                    (C-SUM-MERGE-AUX (MV-NTH 0 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                     (MV-NTH 1 (SWAP-C-LSTS C1-LST C2-LST AUTO-SWAP))
                                     :CLEAN-C1-LST CLEAN-C1-LST
                                     :COUGH-C-LST NIL
                                     :LIMIT (SUM LIMIT -1)))
           :in-theory (e/d (C-SUM-MERGE
                            c-sum-merge-aux)
                           (c-sum-merge-correct
                            c-sum-merge-correct)))))

(defret c-sum-merge-correct-with-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                (rp-term-listp c1-lst)
                (rp-term-listp c2-lst))
           (equal (sum (sum-list (rp-evlt coughed-s a))
                       (sum-list-eval coughed-pp-lst a)
                       (sum-list-eval c-merged-lst a)
                       (sum-list-eval to-be-coughed-c-lst a)
                       (sum-list-eval to-be-coughed-c-lst a)
                       rest)
                  (sum (sum-list-eval c1-lst a)
                       (sum-list-eval c2-lst a)
                       rest)))
  :fn c-sum-merge
  :hints (("Goal"
           :use ((:instance C-SUM-MERGE-CORRECT))
           :in-theory (e/d () (C-SUM-MERGE-CORRECT)))))

(defret c-sum-merge-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                (rp-term-listp c1-lst)
                (rp-term-listp c2-lst))
           (equal (sum-list-eval c-merged-lst a)
                  (sum (sum-list-eval c1-lst a)
                       (sum-list-eval c2-lst a)
                       (-- (sum (sum-list (rp-evlt coughed-s a))
                                (sum-list-eval coughed-pp-lst a)
                                (sum-list-eval to-be-coughed-c-lst a)
                                (sum-list-eval to-be-coughed-c-lst a))))))
  :fn c-sum-merge
  :hints (("Goal"
           :use ((:instance c-sum-merge-correct))
           :do-not-induct t
           :in-theory (e/d () (c-sum-merge-correct)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-sum-merge-main

(defret c-sum-merge-main-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                (rp-term-listp c1-lst)
                (rp-term-listp c2-lst))
           (equal (sum-list-eval c-merged-lst a)
                  (sum (sum-list-eval c1-lst a)
                       (sum-list-eval c2-lst a)
                       (-- (sum (sum-list (rp-evlt coughed-s a))
                                (sum-list-eval coughed-pp-lst a)
                                (sum-list-eval to-be-coughed-c-lst a)
                                (sum-list-eval to-be-coughed-c-lst a))))))
  :fn c-sum-merge-main
  :hints (("Goal"
           :use ((:instance c-sum-merge-correct))
           :do-not-induct t
           :in-theory (e/d (C-SUM-MERGE-MAIN)
                           (c-sum-merge-correct)))))

(defret c-sum-merge-main-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                ;;(rp-term-listp c1-lst)
                  ;;;;(rp-term-listp c2-lst)
                )
           (and
            (valid-sc coughed-s a)
            (valid-sc-subterms coughed-pp-lst a)
            (valid-sc-subterms c-merged-lst a)
            (valid-sc-subterms to-be-coughed-c-lst a)
            ))
  :fn c-sum-merge-main
  :hints (("Goal"
           :in-theory (e/d (c-sum-merge-main) ()))))

(defret c-sum-merge-correct-singled-out-2
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms c1-lst a)
                (valid-sc-subterms c2-lst a)
                (c-of-s-fix-mode)
                )
           (equal (sum-list-eval c-merged-lst a)
                  (sum (sum-list-eval c1-lst a)
                       (sum-list-eval c2-lst a)
                       #|(-- (sum (sum-list (rp-evlt coughed-s a))
                       (sum-list-eval coughed-pp-lst a)
                       (sum-list-eval to-be-coughed-c-lst a)
                       (sum-list-eval to-be-coughed-c-lst a)))||#)))
  :fn c-sum-merge-main
  :hints (("Goal"
           ;;:use ((:instance c-sum-merge-correct))
           :do-not-induct t
           :in-theory (e/d (C-SUM-MERGE-MAIN) ()))))

(defret c-sum-merge-main-when--c-cough-lst=nil
  (implies (not cough-c-lst)
           (not to-be-coughed-c-lst))
  :fn c-sum-merge-main
  ;;:rule-classes :forward-chaining
  :hints (("Goal"
           :expand ()
           :in-theory (e/d (c-sum-merge-main)
                           (c-sum-merge-correct
                            c-sum-merge-correct)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-of-s-fix-lst

(defret c-of-s-fix-lst-valid-sc
  (implies (and ;;(c-of-s-fix-mode)
                (valid-sc-subterms arg-s-lst a)
                (valid-sc-subterms arg-pp-lst a)
                (valid-sc-subterms arg-c-lst a)
                (valid-sc-subterms to-be-coughed-c-lst a)
                (MULT-FORMULA-CHECKS STATE)
                (rp-evl-meta-extract-global-facts :state state))
           (and (valid-sc-subterms to-be-coughed-pp-lst a)
                (valid-sc-subterms to-be-coughed-s-lst a)
                (valid-sc-subterms res-coughed-c-lst a)
                (valid-sc-subterms res-c-lst a)
                (valid-sc-subterms res-pp-lst a)))
  :fn c-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (c-of-s-fix-lst arg-s-lst arg-pp-lst arg-c-lst TO-BE-COUGHED-C-LST)
           :in-theory (e/d (c-of-s-fix-lst
                            )
                           ((:DEFINITION VALID-SC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION IS-RP$INLINE)
                            (:DEFINITION INCLUDE-FNC))))))

(defret res-S-LST-of-CREATE-C-INSTANCE-is-always-nil
  (equal RES-S-LST nil)
  :fn CREATE-C-INSTANCE
  :hints (("Goal"
           :in-theory (e/d (CREATE-C-INSTANCE) ()))))

(encapsulate
  nil
  (local
   (use-arith-5 t))
  (defthm f2+f2+m2-is-x
    (equal (sum (m2 x)
                (f2 x)
                (f2 x))
           (ifix x))
    :hints (("Goal"
             :in-theory (e/d (m2 f2 rw-dir2 sum)
                             (mod2-is-m2
                              rw-dir1
                              +-IS-SUM
                              floor2-if-f2)))))
  (defthmd sum-of-two-negated-f2s
    (equal (sum (-- (f2 x))
                (-- (f2 x)))
           (sum (m2 x) (-- x)))
    :hints (("Goal"
             :in-theory (e/d (m2 f2 -- sum rw-dir2)
                             (mod2-is-m2
                              rw-dir1
                              +-IS-SUM
                              floor2-if-f2))))))

(defret c-of-s-fix-lst-correct-lemma
  (implies (and ;;(c-of-s-fix-mode)
                (valid-sc-subterms arg-s-lst a)
                (valid-sc-subterms arg-pp-lst a)
                (valid-sc-subterms arg-c-lst a)
                (valid-sc-subterms to-be-coughed-c-lst a)
                (MULT-FORMULA-CHECKS STATE)
                (rp-evl-meta-extract-global-facts :state state))
           (equal (sum (sum-list-eval res-pp-lst a)
                       (sum-list-eval res-c-lst a)
                       (sum-list-eval to-be-coughed-pp-lst a)
                       (sum-list-eval to-be-coughed-pp-lst a)
                       (sum-list-eval res-coughed-c-lst a)
                       (sum-list-eval res-coughed-c-lst a)
                       (sum-list-eval to-be-coughed-s-lst a)
                       (sum-list-eval to-be-coughed-s-lst a)
                       )
                  (sum (sum-list-eval arg-s-lst a)
                       (sum-list-eval to-be-coughed-c-lst a)
                       (sum-list-eval to-be-coughed-c-lst a)
                       (sum-list-eval arg-pp-lst a)
                       (sum-list-eval arg-c-lst a))))
  :fn c-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (c-of-s-fix-lst arg-s-lst arg-pp-lst arg-c-lst to-be-coughed-c-lst)
           :in-theory (e/d* (c-of-s-fix-lst
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             sum-of-two-negated-f2s
                             ;;regular-eval-lemmas
                             when-ex-from-rp-is-0

                             )
                            ((:DEFINITION VALID-SC)
                             rp-trans
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                             (:TYPE-PRESCRIPTION BINARY-SUM)
                             (:TYPE-PRESCRIPTION --)
                             (:REWRITE VALID-SC-SUBTERMS-CDR)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE DEFAULT-CAR)
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION IS-RP$INLINE)
                             (:DEFINITION INCLUDE-FNC))))))

(defret c-of-s-fix-lst-correct-singled-out
  (implies (and ;;(c-of-s-fix-mode)
                (valid-sc-subterms arg-s-lst a)
                (valid-sc-subterms arg-pp-lst a)
                (valid-sc-subterms arg-c-lst a)
                (valid-sc-subterms to-be-coughed-c-lst a)
                (MULT-FORMULA-CHECKS STATE)
                (rp-evl-meta-extract-global-facts :state state))
           (equal (sum-list-eval res-c-lst a)
                  (sum
                   (-- (sum (sum-list-eval res-pp-lst a)
                            (sum-list-eval to-be-coughed-pp-lst a)
                            (sum-list-eval to-be-coughed-pp-lst a)
                            (sum-list-eval res-coughed-c-lst a)
                            (sum-list-eval res-coughed-c-lst a)
                            (sum-list-eval to-be-coughed-s-lst a)
                            (sum-list-eval to-be-coughed-s-lst a)))
                   (sum-list-eval arg-s-lst a)
                   (sum-list-eval to-be-coughed-c-lst a)
                   (sum-list-eval to-be-coughed-c-lst a)
                   (sum-list-eval arg-pp-lst a)
                   (sum-list-eval arg-c-lst a))))
  :fn c-of-s-fix-lst
  :hints (("Goal"
           :use ((:instance c-of-s-fix-lst-correct-lemma))
           :do-not-induct t
           :in-theory (e/d* ()
                            (c-of-s-fix-lst-correct-lemma)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-of-s-fix

;;;;;;;
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
    (and (equal (m2 (sum a b))
                (m2-chain a b)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ()))))

  (defthm m2-chain-reorder
    (and (equal (m2-chain (sum a b) c)
                (m2-chain a b c))
         (equal (m2-chain a (sum b c))
                (m2-chain a b c))
         (equal (m2-chain (m2-chain a b) c)
                (m2-chain a b c)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) (m2-to-m2-chain)))))

  (defthm m2-chain-comm
    (and
     (implies (syntaxp (sum-comm-order a b))
              (equal  (m2-chain b a)
                      (m2-chain a b)))
     (implies (syntaxp (sum-comm-order a b))
              (equal  (m2-chain b a c)
                      (m2-chain a b c))))
    :rule-classes ((:rewrite :loop-stopper nil))
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

  (defthm m2-chain-of-0
    (and (equal (m2-chain 0 a)
                (m2-chain a))
         (equal (m2-chain a 0)
                (m2-chain a)))
    :hints (("Goal"
             :in-theory (e/d (m2-chain) ())))))
;;;

(defthm equivalence-of-two-m2s-with-the-same-var-1
  (implies (and (equal (m2-chain x y) (m2-chain p q)))
           (equal (equal (m2-chain x y a)
                         (m2-chain p a q))
                  t)))

(defthmd m2-of-rp-evlt-of-ex-from-rp/--reverse
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (syntaxp (equal m '(car s-lst))))
           (equal (m2-chain (rp-evlt m a) y)
                  (m2-chain (rp-evlt (ex-from-rp/-- m) a) y)))
  :hints (("Goal"
           :induct (ex-from-rp/-- m)
           :do-not-induct t
           :in-theory (e/d (ex-from-rp/--
                            m2-chain
                            is-rp
                            --.p)
                           ()))))

(defthmd s-of-s-fix-lst-correct-dummy-lemma1
  (implies (and (equal (sum a b (times2 other))
                       x))
           (equal (m2-chain a b c)
                  (m2-chain x c)))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))

#|(defthmd s-of-s-fix-lst-correct-dummy-lemma2
  (implies (and (equal (m2 big) (m2 small))
                (syntaxp (> (cons-count big)
                            (cons-count small))))
           (equal (m2-chain a big)
                  (m2-chain a small))))||#

#|(defthm
  c-sum-merge-correct-for-s
  (b* (((mv ?coughed-s ?coughed-pp-lst
            ?c-merged-lst ?to-be-coughed-c-lst ?limit-reached)
        (c-sum-merge-fn c1-lst c2-lst auto-swap clean-c1-lst COUGH-C-LST limit)))
    (implies
     (and (rp-evl-meta-extract-global-facts :state state)
          (mult-formula-checks state)
          (valid-sc-subterms c1-lst a)
          (valid-sc-subterms c2-lst a)
          (rp-term-listp c1-lst)
          (rp-term-listp c2-lst))
     (equal (m2-chain (sum-list (rp-evlt coughed-s a))
                      (sum-list-eval coughed-pp-lst a)
                      (sum-list-eval c-merged-lst a))
            (m2 (sum (sum-list-eval c1-lst a)
                     (sum-list-eval c2-lst a))))))
  :hints
  (("goal"
    :in-theory (e/d (s-of-s-fix-lst-correct-dummy-lemma1
                     m2-chain
                     sum-of-repeated-to-times2)
                    (c-sum-merge-correct))
    :use ((:instance c-sum-merge-correct)))))||#

;;(in-theory (enable c-sum-merge-main))

(defret s-of-s-fix-lst-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
           (and (valid-sc-subterms pp-res-lst a)
                (valid-sc-subterms c-res-lst a)))
  :fn s-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (s-of-s-fix-lst s-lst pp-lst c-lst :limit limit)
           :expand ((S-OF-S-FIX-LST S-LST pp-lst C-LST
                                    :LIMIT LIMIT))
           :in-theory (e/d (s-of-s-fix-lst
                            m2-to-m2-chain
                            (:induction S-OF-S-FIX-LST-FN)
                            m2-of-rp-evlt-of-ex-from-rp/--reverse
                            rp-trans-lst-of-consp
                            s-of-s-fix-lst-correct-dummy-lemma1
                            sum-of-repeated-to-times2

                            )
                           (valid-sc
                            ;;(:DEFINITION SUM-LIST-EVAL)
                            (:TYPE-PRESCRIPTION BINARY-M2-CHAIN)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE DEFAULT-CAR)
                            include-fnc
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION S-OF-S-FIX-LST-FN)
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            not-include-rp-means-valid-sc
                            not-include-rp-means-valid-sc-lst
                            include-fnc-subterms
                            ;;c-sum-merge-correct-for-s
                            c-sum-merge-correct
                            M2-OF-RP-EVLT-EX-FROM-RP/--)))))

;;;;
(defthmd SUM-LIST-EVAL-of-cons
  (implies (consp lst)
           (equal (sum-list-eval lst a)
                  (SUM (RP-EVLT (CAR LST) A)
                       (SUM-LIST-EVAL (CDR LST) A)))))

(defthmd SUM-LIST-EVAL-of-atom
  (implies (atom lst)
           (equal (sum-list-eval lst a)
                  0)))
;;;;;

(defthm dummy-m2-chain-lemma
  (and (equal (equal (m2-chain a b)
                     (m2-chain a c))
              (equal (m2-chain b)
                     (m2-chain c)))
       (equal (equal (m2-chain b c a)
                     (m2-chain x y z a))
              (equal (m2-chain b c)
                     (m2-chain x y z)))
       (equal (equal (m2-chain b c d a)
                     (m2-chain x y z a))
              (equal (m2-chain b c d)
                     (m2-chain x y z)))
       (equal (equal (m2-chain b c d e a)
                     (m2-chain x y a))
              (equal (m2-chain b c d e)
                     (m2-chain x y))))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))

(defthm m2-chain-of-m2
  (and (equal (m2-chain (m2 x) y)
              (m2-chain x y))
       (equal (m2-chain y (m2 x))
              (m2-chain x y)))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))

(defthm m2-chain-of-nil-2
  (implies (and (EQUAL (EX-FROM-RP/-- x) ''NIL)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (M2-CHAIN other (RP-EVLT x A))
                       (M2-CHAIN other))
                (equal (M2-CHAIN (RP-EVLT x A) other)
                       (M2-CHAIN other))))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))

(defthm m2-chain-of-neg-and-times2
  (and (equal (m2-chain (-- x) y)
              (m2-chain x y))
       (equal (m2-chain y (-- x))
              (m2-chain x y))
       (equal (m2-chain y (times2 x))
              (m2-chain y))
       (equal (m2-chain (times2 x) y)
              (m2-chain y)))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))

(defret s-of-s-fix-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms c-lst a)
                (valid-sc-subterms pp-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
           (and (equal (m2 (sum (sum-list-eval pp-res-lst a)
                                (sum-list-eval c-res-lst a)
                                x))
                       (m2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a)
                                x)))
                (equal (m2-chain (sum-list-eval pp-res-lst a)
                                 (sum-list-eval c-res-lst a)
                                 x)
                       (m2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a)
                                x)))))
  :fn s-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :induct (s-of-s-fix-lst s-lst pp-lst c-lst :limit limit)
           :expand ((S-OF-S-FIX-LST S-LST pp-lst C-LST
                                    :LIMIT LIMIT))
           :in-theory (e/d (
                            C-SUM-MERGE-MAIN

                            s-of-s-fix-lst
                            SUM-LIST-EVAL-of-atom
                            m2-to-m2-chain
                            SUM-LIST-EVAL-of-cons
                            (:induction S-OF-S-FIX-LST-FN)
                            m2-of-rp-evlt-of-ex-from-rp/--reverse
                            rp-trans-lst-of-consp
                            s-of-s-fix-lst-correct-dummy-lemma1
                            sum-of-repeated-to-times2)
                           (valid-sc
                            (:TYPE-PRESCRIPTION RP-TRANS-LST)
                            (:DEFINITION TRANS-LIST)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            eval-and-all
                            valid-sc
                            (:DEFINITION VALID-SC-SUBTERMS)
                            (:REWRITE VALID-SC-SUBTERMS-CONS)
                            (:DEFINITION SUM-LIST-EVAL)
                            (:TYPE-PRESCRIPTION BINARY-M2-CHAIN)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE DEFAULT-CAR)
                            include-fnc
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION S-OF-S-FIX-LST-FN)
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            not-include-rp-means-valid-sc
                            not-include-rp-means-valid-sc-lst
                            include-fnc-subterms
                            ;;c-sum-merge-correct-for-s
                            c-sum-merge-correct
                            nfix natp
                            M2-OF-RP-EVLT-EX-FROM-RP/--)))
          #|("Subgoal *1/3"
          :use ((:instance c-sum-merge-correct-for-s
          (c1-lst (LIST-TO-LST (CADDDR (EX-FROM-RP/-- (CAR
          S-LST)))))
          (c2-lst (MV-NTH 1
          (S-OF-S-FIX-LST (CDR S-LST) pp-lst
          C-LST
          :LIMIT (SUM LIMIT -1))))
          (auto-swap t)
          (limit (NFIX (C-SUM-MERGE-FN-STABLE
          (LIST-TO-LST (CADDDR (EX-FROM-RP/-- (CAR
          S-LST))))
          (MV-NTH 1
          (S-OF-S-FIX-LST (CDR S-LST) pp-lst
          C-LST
          :LIMIT (SUM LIMIT
          -1)))
          t nil t)))
          (clean-c1-lst nil)
          (COUGH-C-LST t))))||#
          #|("Subgoal *1/4"
          :use ((:instance c-sum-merge-correct-for-s
          (c1-lst (LIST-TO-LST (CADDDR (EX-FROM-RP/-- (CAR
          S-LST)))))
          (c2-lst (MV-NTH 1
          (S-OF-S-FIX-LST (CDR S-LST) pp-lst
          C-LST
          :LIMIT (SUM LIMIT -1))))
          (auto-swap t)
          (limit (NFIX (C-SUM-MERGE-FN-STABLE
          (LIST-TO-LST (CADDDR (EX-FROM-RP/-- (CAR
          S-LST))))
          (MV-NTH 1
          (S-OF-S-FIX-LST (CDR S-LST) pp-lst
          C-LST
          :LIMIT (SUM LIMIT
          -1)))
          t nil t)))
          (clean-c1-lst nil)
          (COUGH-C-LST t))))||#))

(defret s-of-s-fix-lst-correct-without-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms c-lst a)
                (valid-sc-subterms pp-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
           (and (equal (m2 (sum (sum-list-eval pp-res-lst a)
                                (sum-list-eval c-res-lst a)))
                       (m2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))
                (equal (m2-chain (sum-list-eval pp-res-lst a)
                                 (sum-list-eval c-res-lst a))
                       (m2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))))
  :fn s-of-s-fix-lst
  :hints (("Goal"
           :use ((:instance s-of-s-fix-lst-correct
                            (x 0)))
           )))

#|(defret s-of-s-fix-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc s a)
                (valid-sc pp a)
                (valid-sc-subterms c-lst a)
                (rp-termp s)
                (rp-termp pp)
                (rp-term-listp c-lst))
           (and (valid-sc pp-res a)
                (valid-sc-subterms c-res-lst a)
                (equal (m2 (sum (sum-list (rp-evlt pp-res a))
                                (sum-list-eval c-res-lst a)))
                       (m2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (sum-list-eval c-lst a))))
                (equal (m2-chain (sum-list (rp-evlt pp-res a))
                                 (sum-list-eval c-res-lst a))
                       (m2 (sum (sum-list (rp-evlt s a))
                                (sum-list (rp-evlt pp a))
                                (sum-list-eval c-lst a))))))
  :fn s-of-s-fix
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (s-of-s-fix
                            m2-to-m2-chain)
                           ()))))||#

(local
 (in-theory (disable (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC))))
(local
 (in-theory (enable is-rp-implies-fc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; extract-new-sum-element, extract-new-sum-consed

(defthm sum-list-eval-of-repeat-quoted-1
  (implies (natp amount)
           (equal (sum-list-eval (repeat amount ''1) a)
                  amount))
  :hints (("Goal"
           :in-theory (e/d (repeat
                            sum-list-eval
                            rw-dir2)
                           (rw-dir1)))))

(defthm sum-list-eval-of-repeat-quoted-minus-1
  (implies (and (natp amount)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval (repeat amount '(-- '1)) a)
                  (- amount)))
  :hints (("Goal"
           :in-theory (e/d* (repeat
                             sum-list-eval
                             regular-eval-lemmas
                             rw-dir2)
                            (rw-dir1
                             rp-trans)))))

(defthmd rp-evlt-when-quotep
  (implies (quotep term)
           (equal (rp-evlt term a)
                  (cadr term))))

(defret extract-new-sum-element-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval acc-res a)
                  (sum (rp-evlt term a)
                       (sum-list-eval acc a))))
  :fn extract-new-sum-element
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-new-sum-element term acc)
           :in-theory (e/d* (extract-new-sum-element
                             rp-evlt-when-quotep
                             regular-eval-lemmas-with-ex-from-rp
                             rp-evlt-of-ex-from-rp-reverse-only-atom
                             rw-dir2)
                            (rw-dir1
                             rp-trans
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                             rp-evlt-of-ex-from-rp
                             )))))

(defthm quote-listp-of-repeat
  (implies (natp amount)
           (and (quote-listp (repeat amount ''1))
                (quote-listp (repeat amount ''-1))))
  :hints (("Goal"
           :in-theory (e/d (repeat) ()))))

(defthmd quote-listp-implies-valid-sc-subterms
  (implies (quote-listp lst)
           (valid-sc-subterms lst a)))

(defthmd quote-listp-implies-valid-sc
  (implies (quote-listp lst)
           (valid-sc (car lst) a)))

(defthm valid-sc-subterms-of-repeat
  (implies (and (valid-sc term a))
           (valid-sc-subterms (repeat amount term) a))
  :hints (("Goal"
           :in-theory (e/d (repeat) ()))))

(defret extract-new-sum-element-correct-valid-sc
  (implies (and (valid-sc term a)
                (valid-sc-subterms acc a))
           (valid-sc-subterms acc-res a))
  :fn extract-new-sum-element
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-new-sum-element term acc)
           :in-theory (e/d (extract-new-sum-element
                            quote-listp-implies-valid-sc
                            quote-listp-implies-valid-sc-subterms
                            rp-evlt-when-quotep
                            rp-evlt-of-ex-from-rp-reverse-only-atom
                            rw-dir2)
                           (rw-dir1
                            rp-trans
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            rp-evlt-of-ex-from-rp)))))

;;;;;;

(defret extract-new-sum-consed-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval acc-res a)
                  (sum-list (rp-evlt term a))))
  :fn extract-new-sum-consed
  :hints (("Goal"
           :do-not-induct t
           :expand (EXTRACT-NEW-SUM-CONSED TERM)
           :induct (extract-new-sum-consed term)
           :in-theory (e/d (extract-new-sum-consed
                            rp-evlt-of-ex-from-rp-reverse-only-atom)
                           (rp-evlt-of-ex-from-rp
                            rp-trans
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            EVL-OF-EXTRACT-FROM-RP)))))

(defret extract-new-sum-consed-correct-valid-sc
  (implies (valid-sc term a)
           (valid-sc-subterms acc-res a))
  :fn extract-new-sum-consed
  :hints (("Goal"
           :do-not-induct t
           :expand (EXTRACT-NEW-SUM-CONSED TERM)
           :induct (extract-new-sum-consed term)
           :in-theory (e/d (extract-new-sum-consed
                            rp-evlt-of-ex-from-rp-reverse-only-atom)
                           (rp-evlt-of-ex-from-rp
                            rp-trans
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            EVL-OF-EXTRACT-FROM-RP)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; recollect-pp

#|(local
 (defthm recollectable-pp-p-implies-fc
   (implies (recollectable-pp-p pp)
            (b* ((pp (ex-from--- pp))
                 (pp (ex-from-rp pp)))
              (case-match pp
                (('and-list & ('list a1 a2 a3 a4))
                 (b* ((a1 (ex-from-rp a1))
                      (a2 (ex-from-rp a2))
                      (a3 (ex-from-rp a3))
                      (a4 (ex-from-rp a4))
                      (a1 (ex-from-rp (case-match a1 (('bit-of x &) x) (& a1))))
                      (a2 (ex-from-rp (case-match a2 (('bit-of x &) x) (& a2))))
                      (a3 (ex-from-rp (case-match a3 (('bit-of x &) x) (& a3))))
                      (a4 (ex-from-rp (case-match a4 (('bit-of x &) x) (& a4)))))
                   (or (and (equal a1 a2)
                            (equal a1 a3)
                            (not (equal a1 a4))
                            1)
                       (and (equal a4 a2)
                            (equal a4 a3)
                            (not (equal a1 a4))
                            2)))))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :expand (recollectable-pp-p pp)

            :in-theory (theory 'minimal-theory)))))||#

(defthmd recollect-pp-correct-lemma1
  (implies (and  (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state)
                 (CONSP PP)
                 (EQUAL (CAR PP) '--)
                 (CONSP (CDR PP))
                 (NOT (CDDR PP)))
           (equal (rp-evlt (EX-FROM-RP PP) a)
                  (-- (rp-evlt (ex-from-rp (cadr pp)) a))))
  :hints (("Goal"
           :in-theory (e/d* (regular-eval-lemmas-with-ex-from-rp
                             rp-evlt-of-ex-from-rp)
                            ()))))

(defthmd recollect-pp-correct-lemma2
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (equal (f2 (sum x y z))
                  (sum (-- (and$ x y z))
                       (-- (and$ x y z))
                       (binary-and x y)
                       (binary-and x z)
                       (binary-and z y))))
  :hints (("Goal"
           :in-theory (e/d (bitp)
                           (f2)))))

(defthm and$-assoc-and-comm
  (and (equal (and$ (and$ a b) c)
              (and$ a b c))
       (equal (and$ b a)
              (and$ a b))
       (equal (and$ b a c)
              (and$ a b c)))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthm and$-of-1
  (equal (and$ 1 1 a)
         (and$ 1 a))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthm and$-of-the-same
  (and (equal (and$ a a b)
              (and$ a b))
       (equal (and$ a a)
              (and$ a)))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthm and$-of-bitfix
  (and (equal (and$ a (bit-fix b))
              (and$ a b))
       (equal (and$ (bit-fix b) a)
              (and$ b a)))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(defthmd rp-trans-when-list
  (implies (and (case-match term (('list . &) t)))
           (equal (rp-trans term)
                  (TRANS-LIST (RP-TRANS-LST (CDR TERM)))))
  :hints (("Goal"
           :in-theory (e/d (rp-trans) ()))))

(defret recollect-pp-correct
  (implies (and (valid-sc pp a)
                (rp-termp pp)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and
            (equal (sum (sum-list-eval res-pp-lst a)
                        (rp-evlt c a))
                   (sum (rp-evlt pp a)
                        (rp-evlt pp a)))))
  :fn recollect-pp
  :hints (("Goal"
           :in-theory (e/d* (recollect-pp
                             rp-trans-when-list
                             and-list
                             recollect-pp-correct-lemma2
                             recollect-pp-correct-lemma1
                             ;;RECOLLECTABLE-PP-P
                             rp-evlt-when-quotep
                             (:rewrite regular-rp-evl-of_--_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_cons_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite regular-rp-evl-of_c_when_mult-formula-checks)
                             rp-evlt-of-ex-from-rp-reverse-only-atom
                             rw-dir2
                             )
                            (rw-dir1
                             ;;eval-and-all

                             rp-trans
                             NOT-INCLUDE-RP-MEANS-VALID-SC-LST
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                             rp-evlt-of-ex-from-rp
                             )))))

(defthm CREATE-AND-LIST-INSTANCE-valid-sc
  (implies (and (valid-sc-subterms lst a))
           (valid-sc (CREATE-AND-LIST-INSTANCE lst) a))
  :hints (("Goal"
           :in-theory (e/d (CREATE-AND-LIST-INSTANCE
                            is-if
                            is-rp
                            valid-sc)
                           ()))))

(defthm bitp-f2-of-three-bits
  (implies (and (bitp x)
                (bitp y)
                (bitp z))
           (bitp (f2 (sum x y z))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defret recollect-pp-valid-sc
  (implies (and (valid-sc pp a)
                (rp-termp pp)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-pp-lst a)
                (valid-sc c a)))
  :fn recollect-pp
  :hints (("Goal"
           :in-theory (e/d* (recollect-pp
                             rw-dir2
                             valid-sc
                             is-rp
                             is-if
                             valid-sc-single-step
                             )
                            (rw-dir1
                             rp-trans

                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT

                             )))))

(defret recollect-pp-lst-to-sc-correct
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum (sum-list-eval res-pp-lst a)
                       (sum-list-eval res-c-lst a))
                  (sum-list-eval pp-lst a)))
  :fn recollect-pp-lst-to-sc
  :hints (("Goal"
           :do-not-induct t
           :induct (recollect-pp-lst-to-sc pp-lst)
           :in-theory (e/d (recollect-pp-lst-to-sc)
                           ()))))

(defret recollect-pp-lst-to-sc-correct-2
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (--  (sum-list-eval res-c-lst a))
                       (sum-list-eval pp-lst a))))
  :fn recollect-pp-lst-to-sc
  :hints (("Goal"
           :use ((:instance recollect-pp-lst-to-sc-correct))
           :in-theory (e/d () (recollect-pp-lst-to-sc-correct)))))

(defret recollect-pp-lst-to-sc-valid-sc
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn recollect-pp-lst-to-sc
  :hints (("Goal"
           :do-not-induct t
           :induct (recollect-pp-lst-to-sc pp-lst)
           :in-theory (e/d (recollect-pp-lst-to-sc)
                           ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; new-sum-merge-aux

(defthm dummy-sum-cancel-lemma2
  (equal (equal (sum x1 x2 x3 x4 x5 a)
                (sum y1 y2 a))
         (equal (sum x1 x2 x3 x4 x5)
                (sum y1 y2))))

(defthm is-rp-of-cons
  (implies (and (syntaxp (quotep x))
                (not (equal x 'rp)))
           (not (is-rp (cons x y))))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm valid-sc-of-cons-instance
  (equal (valid-sc `(cons ,x ,y) a)
         (and (valid-sc x a)
              (valid-sc y a)))
  :hints (("Goal"
           :in-theory (e/d (is-rp is-if) ()))))

(defthm valid-sc-of----instance
  (equal (valid-sc `(-- ,x) a)
         (and (valid-sc x a)))
  :hints (("Goal"
           :in-theory (e/d (is-rp is-if) ()))))

(defthm valid-sc-of-nil
  (VALID-SC ''NIL A))

(value-triple (hons-clear t))

(defthm ifix-of-sum-list-eval
  (equal (ifix (sum-list-eval x a))
         (sum-list-eval x a)))

(defret new-sum-merge-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms sum-lst a)
                (rp-term-listp sum-lst))
           (and (valid-sc s a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (valid-sc-subterms to-be-coughed-c-lst a)
                (equal (sum (sum-list (rp-evlt s a))
                            (sum-list-eval pp-lst a)
                            (sum-list-eval c-lst a)
                            (sum-list-eval to-be-coughed-c-lst a)
                            (sum-list-eval to-be-coughed-c-lst a))
                       (sum-list-eval sum-lst a))))
  :fn new-sum-merge-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (new-sum-merge-aux sum-lst)
           :expand ((NEW-SUM-MERGE-AUX SUM-LST))
           :in-theory (e/d* (new-sum-merge-aux
                             s-c-res

                             c-fix-arg-aux-correct-lemma
                             ;;regular-eval-lemmas-with-ex-from-rp

                             (:REWRITE
                              REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_CONS_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S-C-RES_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_SUM-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)

                             ;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             new-sum-merge-aux-dissect-term
                             new-sum-merge-aux-add-negated-coughed
                             (:induction NEW-SUM-MERGE-AUX)
                             sum-list-eval-of-cons
                             sum-list-eval-of-atom)
                            (;;(:REWRITE RP::SUM-ASSOC)
                             sum-cancel-common
                             (:DEFINITION EQ)
                             (:TYPE-PRESCRIPTION PP-TERM-P)
                             (:DEFINITION PP-TERM-P)
                             (:TYPE-PRESCRIPTION QUOTE-P$INLINE)
                             (:TYPE-PRESCRIPTION IS-RP$INLINE)
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:DEFINITION SUM-LIST-EVAL)
                             ;;(:REWRITE MINUS-OF-SUM)
                             (:TYPE-PRESCRIPTION RP-TERMP)

                             (:TYPE-PRESCRIPTION SUM-LIST-EVAL)
                             (:TYPE-PRESCRIPTION SINGLE-C-P$INLINE)
                             (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                             (:TYPE-PRESCRIPTION SINGLE-S-P$INLINE)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                             (:TYPE-PRESCRIPTION SINGLE-s-C-RES-P$INLINE)
                             (:TYPE-PRESCRIPTION O<)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS)
                             (:TYPE-PRESCRIPTION SUM-LIST-P$INLINE)
                             (:TYPE-PRESCRIPTION AND-LIST-P$INLINE)
                             (:REWRITE DEFAULT-CDR)
                             (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                             (:TYPE-PRESCRIPTION BINARY-SUM)
                             (:REWRITE DEFAULT-CAR)

                             (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                             (:DEFINITION NEW-SUM-MERGE-AUX)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)

                             rp-trans
                             ;;rp-evlt-of-ex-from-rp
                             eval-and-all
                             rp-termp
                             rp-term-listp
                             valid-sc
                             VALID-SC-SUBTERMS
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:DEFINITION IS-FALIST))))))

(defret new-sum-merge-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (valid-sc s a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (valid-sc-subterms to-be-coughed-c-lst a)
                (equal (sum (sum-list (rp-evlt s a))
                            (sum-list-eval pp-lst a)
                            (sum-list-eval c-lst a)
                            (sum-list-eval to-be-coughed-c-lst a)
                            (sum-list-eval to-be-coughed-c-lst a))
                       (sum-list (rp-evlt term a)))))
  :fn new-sum-merge
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (new-sum-merge) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; quarternaryp lemmas

(defthm f2-of-quarternaryp
  (implies (quarternaryp sum)
           (bitp (f2 sum)))
  :hints (("Goal"
           :in-theory (e/d (quarternaryp) ()))))

(defthm lte-of-the-same
  (not (gt a a))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2)
                           (rw-dir1)))))

(defthmd quarternaryp-sum-aux-correct-dummy-lemma
  (not (LIGHT-PP-TERM-LIST-P (LIST (LIST 'SUM-LIST
                                         (CADR (EX-FROM-RP (CADR TERM)))))))
  :hints (("Goal"
           :in-theory (e/d (LIGHT-PP-TERM-LIST-P
                            HAS-BITP-RP
                            EX-FROM-RP
                            is-rp
                            LIGHT-PP-TERM-P)
                           ()))))

(defthm LIGHT-PP-TERM-P-max-val
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (LIGHT-PP-TERM-P term))
           (and (not (gt (rp-evlt term a)
                         1))
                (lte (rp-evlt term a)
                     1))))

(defthm LIGHT-PP-TERM-P-min-val
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (LIGHT-PP-TERM-P term))
           (and (not (gt 0
                         (rp-evlt term a)))
                (lte 0
                     (rp-evlt term a)))))

(defthm lte-sum-lemma-1
  (implies (and (force (integerp a))
                (force (integerp b))
                (force (integerp x))
                (force (integerp y))
                (lte a b)
                (lte x y))
           (and (not (gt (sum a x)
                         (sum y b)))
                (not (gt (sum a x)
                         (sum b y)))))
  :hints (("Goal"
           :in-theory (e/d (sum
                            rw-dir2
                            ifix-opener)
                           (rw-dir1
                            +-IS-SUM)))))

(defthm LIGHT-PP-TERM-P-integerp
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (LIGHT-PP-TERM-P term))
           (INTEGERP (RP-EVLT term A)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (LIGHT-PP-TERM-P
                            bitp-implies-integerp
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-evlt-of-ex-from-rp)))))

(defthm LIGHT-PP-TERM-LIST-P-max-val
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a)
                (LIGHT-PP-TERM-LIST-P lst))
           (and (not (gt (SUM-LIST-EVAL lst a)
                         (len lst)))
                (lte (SUM-LIST-EVAL lst a)
                     (len lst))))
  :hints (("Goal"
           :induct (LIGHT-PP-TERM-LIST-P lst)
           :do-not-induct t
           :in-theory (e/d (LIGHT-PP-TERM-LIST-P) ()))))

(defthmd lte-dummy-lemma-1
  (implies (and (lte 0 a)
                (lte 0 b))
           (not (gt 0
                    (sum a b))))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2 sum ifix)
                           (+-IS-SUM  rw-dir1)))))

(defthm LIGHT-PP-TERM-LIST-P-min-val
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a)
                (LIGHT-PP-TERM-LIST-P lst))
           (and (not (gt 0
                         (SUM-LIST-EVAL lst a)))
                (lte 0
                     (SUM-LIST-EVAL lst a))))
  :hints (("Goal"
           :induct (LIGHT-PP-TERM-LIST-P lst)
           :do-not-induct t
           :in-theory (e/d (LIGHT-PP-TERM-LIST-P
                            lte-dummy-lemma-1) ()))))

(defthm AND-LIST-P-max-val
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (AND-LIST-P term))
           (and (not (gt (rp-evlt term a)
                         1))
                (lte (rp-evlt term a)
                     1)))
  :hints (("Goal"
           :in-theory (e/d* (regular-eval-lemmas)
                            ()))))

(defthmd bitp-max-val
  (implies (bitp term)
           (and (not (gt term
                         1))
                (lte term
                     1))))

(defthmd bitp-min-val
  (implies (bitp term)
           (and (not (gt 0
                         term))
                (lte 0
                     term))))

(defthmd lte-implies-the-same
  (implies (lte a b)
           (not (gt a b)))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2) (rw-dir1)))))

(defret quarternaryp-sum-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                valid)
           (and (<= (sum-list (rp-evlt term a))
                    res)
                (<= 0
                    (sum-list (rp-evlt term a)))))
  :fn quarternaryp-sum-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (quarternaryp-sum-aux term)
           :in-theory (e/d* (quarternaryp-sum-aux
                             bitp-implies-integerp
                             lte-dummy-lemma-1
                             (:REWRITE
                              REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_CONS_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_SUM-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             lte-implies-the-same
                             bitp-max-val
                             bitp-min-val
                             quarternaryp-sum-aux-correct-dummy-lemma
                             LIST-TO-LST
                             rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                            (rp-evlt-of-ex-from-rp)))))

(defret quarternaryp-sum-aux-returns-natp
  (natp res)
  :fn quarternaryp-sum-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (quarternaryp-sum-aux term)
           :in-theory (e/d (quarternaryp-sum-aux
                            rw-dir2)
                           (rw-dir1)))))

(defret quarternaryp-sum-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (implies quarternaryp?
                         (quarternaryp (sum-list (rp-evlt term a))))
                (implies bitp?
                         (bitp (sum-list (rp-evlt term a))))))
  :fn quarternaryp-sum
  :hints (("Goal"
           :use ((:instance quarternaryp-sum-aux-correct)
                 (:instance quarternaryp-sum-aux-returns-natp))
           :in-theory (e/d (quarternaryp-sum
                            bitp
                            quarternaryp
                            rw-dir2)
                           (natp
                            rw-dir1
                            quarternaryp-sum-aux-returns-natp
                            quarternaryp-sum-aux-correct
                            quarternaryp-sum-aux
                            REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS
                            zp
                            REGULAR-RP-EVL-OF_s-C-RES_WHEN_MULT-FORMULA-CHECKS
                            rp-evlt-of-ex-from-rp
                            ex-from-rp-lemma1
                            RP-EVL-OF-VARIABLE
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            ex-from-rp
                            ex-from-rp-loose
                            valid-sc
                            rp-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-pattern3-reduce

(defret c-pattern3-reduce-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)

                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst)

                (valid-sc-subterms s-coughed-lst a)
                (valid-sc-subterms pp-coughed-lst a)
                (valid-sc-subterms c-coughed-lst a))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)
                (valid-sc-subterms res-s-coughed-lst a)
                (valid-sc-subterms res-pp-coughed-lst a)
                (valid-sc-subterms res-c-coughed-lst a)))
  :fn c-pattern3-reduce
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (c-pattern3-reduce) ()))))

(std::defretd
 create-s-instance-correct-singled-out
 (implies (and (rp-evl-meta-extract-global-facts :state state)
               (mult-formula-checks state)
               (valid-sc pp a)
               (valid-sc c a))
          (equal (sum-list-eval s-res-lst a)
                 (sum (-- (sum
                           (sum-list-eval pp-res-lst a)
                           (sum-list-eval c-res-lst a)))
                      (m2 (sum (sum-list (rp-evlt pp a))
                               (sum-list (rp-evlt c a)))))))
 :fn create-s-instance
 :hints (("Goal"
          :use ((:instance create-s-instance-correct))
          :do-not-induct t
          :in-theory (e/d ()
                          (create-s-instance-correct)))))

(defret c-pattern3-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)

                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst)

                (valid-sc-subterms s-coughed-lst a)
                (valid-sc-subterms pp-coughed-lst a)
                (valid-sc-subterms c-coughed-lst a))

           (equal (sum (f2 (sum (sum-list-eval res-s-lst a)
                                (sum-list-eval res-pp-lst a)
                                (sum-list-eval res-c-lst a)))

                       ;; (sum-list-eval res-s-coughed-lst a)
                       ;; (sum-list-eval res-pp-coughed-lst a)
                       ;; (sum-list-eval res-c-coughed-lst a)

                       (sum-list-eval res-s-coughed-lst a)
                       (sum-list-eval res-pp-coughed-lst a)
                       (sum-list-eval res-c-coughed-lst a))

                  (sum (f2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a)))
                       ;; (sum-list-eval s-coughed-lst a)
                       ;; (sum-list-eval pp-coughed-lst a)
                       ;; (sum-list-eval c-coughed-lst a)
                       (sum-list-eval s-coughed-lst a)
                       (sum-list-eval pp-coughed-lst a)
                       (sum-list-eval c-coughed-lst a))))
  :fn c-pattern3-reduce
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (c-pattern3-reduce
                            create-s-instance-correct-singled-out)
                           ((:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            ;;(:DEFINITION SUM-LIST-EVAL)
                            )))))

(defret c-pattern3-reduce-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)

                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst)

                (valid-sc-subterms s-coughed-lst a)
                (valid-sc-subterms pp-coughed-lst a)
                (valid-sc-subterms c-coughed-lst a))

           (equal (f2 (sum (sum-list-eval res-s-lst a)
                           (sum-list-eval res-pp-lst a)
                           (sum-list-eval res-c-lst a)))

                  (sum (f2 (sum (sum-list-eval s-lst a)
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a)))
                       ;; (sum-list-eval s-coughed-lst a)
                       ;; (sum-list-eval pp-coughed-lst a)
                       ;; (sum-list-eval c-coughed-lst a)
                       (sum-list-eval s-coughed-lst a)
                       (sum-list-eval pp-coughed-lst a)
                       (sum-list-eval c-coughed-lst a)
                       (-- (sum

                            ;; (sum-list-eval res-s-coughed-lst a)
                            ;; (sum-list-eval res-pp-coughed-lst a)
                            ;; (sum-list-eval res-c-coughed-lst a)

                            (sum-list-eval res-s-coughed-lst a)
                            (sum-list-eval res-pp-coughed-lst a)
                            (sum-list-eval res-c-coughed-lst a))))))
  :fn c-pattern3-reduce
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-pattern3-reduce-correct))
           :in-theory (e/d (
                            )
                           ((:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            c-pattern3-reduce-correct
                            ;;(:DEFINITION SUM-LIST-EVAL)
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-spec-meta-aux and s-spec-meta-aux

(defthm rp-evl-of-nil
  (equal (RP-EVL ''NIL A)
         nil))

(defthm CREATE-LIST-INSTANCE-equals-nil-implies
  (implies (equal (CREATE-LIST-INSTANCE lst) ''nil)
           (equal (sum-list-eval lst a)
                  0))
  :hints (("Goal"
           :in-theory (e/d (CREATE-LIST-INSTANCE) ()))))

#|(defthm
  create-s-c-res-instance-correct-bumped
  (b*((?res
        (create-s-c-res-instance$inline s-lst pp-lst c-lst bitp)))
    (implies
     (and (rp-evl-meta-extract-global-facts :state state)
          (mult-formula-checks state)
          (integer-listp (rp-evlt-lst s-lst a))
          (integer-listp (rp-evlt-lst c-lst a)))
     (equal (rp-evlt res a)
            (sum (sum-list-eval s-lst a)
                 (sum-list-eval pp-lst a)
                 (sum-list-eval c-lst a)))))
  :hints
  (("goal" :in-theory (e/d ()
                           nil))))||#

(defthm integer-listp-rp-evlt-lst
  (implies (and (integer-listp (rp-evlt-lst lst1 a))
                (integer-listp (rp-evlt-lst lst2 a)))
           (integer-listp (rp-evlt-lst (S-SUM-MERGE-AUX lst1 lst2) a)))
  :hints (("Goal"
           :induct (S-SUM-MERGE-AUX lst1 lst2)
           :in-theory (e/d (S-SUM-MERGE-AUX) ()))))

(defret integer-listp-c-fix-arg-aux
  (implies (and (integer-listp (rp-evlt-lst arg-lst a))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (integer-listp (rp-evlt-lst coughed-lst a))
                ;;(integer-listp (rp-evlt-lst cleaned-lst a))
                ))
  :fn C-FIX-ARG-AUX
  :hints (("Goal"
           :do-not-induct t
           :induct (C-FIX-ARG-AUX arg-lst neg-flag)
           :in-theory (e/d (C-FIX-ARG-AUX
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-evlt-of-ex-from-rp)))))

(defthm S-SUM-MERGE-AUX-of-nil
  (and (equal (S-SUM-MERGE-AUX nil lst)
              lst)
       (implies (true-listp lst)
                (equal (S-SUM-MERGE-AUX lst nil)
                       lst)))
  :hints (("Goal"
           :in-theory (e/d (S-SUM-MERGE-AUX) ()))))

(defret c-spec-meta-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp arg-s)
                (rp-term-listp arg-pp-lst )
                (rp-term-listp arg-c-lst )
                (rp-term-listp to-be-coughed-c-lst )
                (valid-sc arg-s a)
                (valid-sc-subterms arg-pp-lst a)
                (valid-sc-subterms arg-c-lst a)
                (valid-sc-subterms to-be-coughed-c-lst a)
                (if quarternaryp
                    (quarternaryp
                     (sum (sum-list (rp-evlt arg-s a))
                          (sum-list-eval arg-pp-lst a)
                          (sum-list-eval arg-c-lst a)
                          (sum-list-eval to-be-coughed-c-lst a)
                          (sum-list-eval to-be-coughed-c-lst a)))
                  t))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (f2 (sum (sum-list (rp-evlt arg-s a))
                                (sum-list-eval arg-pp-lst a)
                                (sum-list-eval arg-c-lst a)
                                (sum-list-eval to-be-coughed-c-lst a)
                                (sum-list-eval to-be-coughed-c-lst a))))))
  :fn c-spec-meta-aux
  ;;:otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance c-fix-s-args-correct
                            (pp ARG-S)
                            (rest (sum (SUM-LIST-EVAL ARG-C-LST A)
                                       (SUM-LIST-EVAL ARG-PP-LST A))))
                 (:instance c-fix-pp-args-correct
                            (pp (CREATE-LIST-INSTANCE ARG-PP-LST))
                            (rest (sum (SUM-LIST-EVAL ARG-C-LST A)
                                       (SUM-LIST (RP-EVLT ARG-S A))))))
           :expand ((C-SUM-MERGE-LST ''0 TO-BE-COUGHED-C-LST))
           :in-theory (e/d (c-spec-meta-aux
                            ;; c-pattern2-reduce-correct -when-res-c-is-0
                            ;;c-pattern2-reduce-correct-res-single-c-on-one-side
                            times2
                            ;;CREATE-S-C-RES-INSTANCE
                            minus-of-sum

                            C-SUM-MERGE-MAIN

                            valid-sc-single-step
                            f2-of-times2-reverse
                            rp-trans-lst-of-consp
                            s-c-res
                            sum-list-eval-of-atom
                            sum-list-eval-of-cons)
                           (f2-of-times2
                            nfix
                            F2-OF-MINUS
                            rp-trans
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            (:TYPE-PRESCRIPTION RP-TERMP)
                            (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                            (:TYPE-PRESCRIPTION O<)
                            (:DEFINITION EVAL-AND-ALL)
                            (:DEFINITION INCLUDE-FNC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION
                             INCLUDE-FNC-SUBTERMS)(:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            ;; (:REWRITE MINUS-OF-SUM)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:TYPE-PRESCRIPTION BINARY-SUM)
                            (:DEFINITION SUM-LIST-EVAL)
                            rp-trans
                            rp-trans-lst
                            rp-trans-of-quoted
                            RP-EVL-OF-QUOTE
                            F2-OF-MINUS-2
                            c-fix-s-args-correct
                            c-fix-pp-args-correct
                            c-fix-pp-args-correct-2
                            c-fix-s-args-correct-2)))))

(defret s-spec-meta-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp s)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst)
                (valid-sc s a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (m2 (sum (sum-list (rp-evlt s a))
                                (sum-list-eval pp-lst a)
                                (sum-list-eval c-lst a))))))
  :fn s-spec-meta-aux
  :hints (("Goal"
           :in-theory (e/d (s-spec-meta-aux) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-c-spec-meta correct

(create-regular-eval-lemma c-s-spec 1 mult-formula-checks)
(create-regular-eval-lemma s-c-spec 1 mult-formula-checks)
(create-regular-eval-lemma c-spec 1 mult-formula-checks)
(create-regular-eval-lemma s-spec 1 mult-formula-checks)

(defthmd dummy-m2-lemma
  (implies (equal (sum x y z a a) m)
           (equal (equal (m2 (sum x y z))
                         (m2 m))
                  t))
  :hints (("Goal"
           :in-theory (e/d (sum-of-repeated-to-times2) ()))))

(defthm m2-of-bitp-lemma
  (implies (bitp x)
           (equal (m2 x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defret s-c-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term)
                (valid-sc term a))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (rp-evlt term a))
                (dont-rw-syntaxp donw-rw)))
  :fn s-c-spec-meta
  :hints (("Goal"
           :use ((:instance new-sum-merge-correct
                            (term (CADR TERM))))
           :in-theory (e/d (s-c-spec-meta
                            dummy-m2-lemma)
                           (new-sum-merge-correct)))))
