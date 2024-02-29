; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020 Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

(local
 (set-induction-depth-limit 1))

(with-output
  :off :all
  (progn
    (create-regular-eval-lemma c 4 mult-formula-checks)
    (create-regular-eval-lemma s 3 mult-formula-checks)
    (create-regular-eval-lemma s-c-res 3 mult-formula-checks)
    (create-regular-eval-lemma and-list 2 mult-formula-checks)

    (create-regular-eval-lemma binary-or 2 mult-formula-checks)
    (create-regular-eval-lemma binary-? 3 mult-formula-checks)
    (create-regular-eval-lemma binary-and 2 mult-formula-checks)
    (create-regular-eval-lemma binary-xor 2 mult-formula-checks)
    (create-regular-eval-lemma binary-not 1 mult-formula-checks)

    (create-regular-eval-lemma cons 2 mult-formula-checks)
    (create-regular-eval-lemma binary-not 1 mult-formula-checks)
    (create-regular-eval-lemma binary-xor 2 mult-formula-checks)
    (create-regular-eval-lemma binary-or 2 mult-formula-checks)
    (create-regular-eval-lemma binary-and 2 mult-formula-checks)
    (create-regular-eval-lemma binary-? 3 mult-formula-checks)
    (create-regular-eval-lemma sum-list 1 mult-formula-checks)

    (create-regular-eval-lemma svl::bits 3 mult-formula-checks)

    (create-regular-eval-lemma equals 2 mult-formula-checks)

    (create-regular-eval-lemma -- 1 mult-formula-checks)

    (create-regular-eval-lemma c-s-spec 1 mult-formula-checks)
    (create-regular-eval-lemma s-c-spec 1 mult-formula-checks)
    (create-regular-eval-lemma c-spec 1 mult-formula-checks)
    (create-regular-eval-lemma s-spec 1 mult-formula-checks)

    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get-max-min-val

(local
 (in-theory (disable (:definition acl2::apply$-badgep)
                     (:rewrite rp-term-listp-is-true-listp)
                     (:definition rp-term-listp)
                     (:definition rp-termp)
                     (:definition ex-from-rp)
                     (:rewrite not-include-rp)
                     (:linear acl2::apply$-badgep-properties . 1))))

(local
 (defthm is-equals-of-others
   (implies (not (equal (car term) 'equals))
            (not (is-equals term )))
   :hints (("Goal"
            :in-theory (e/d (is-equals) ())))))

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

(local
 (defthmd *-is-times
   (implies (and (integerp x)
                 (integerp y))
            (equal (* x y)
                   (times x y)))
   :hints (("Goal"
            :in-theory (e/d (times) ())))))

(local
 (defthmd rp-evlt-when-quotep
   (implies (equal (car x) 'quote)
            (equal (rp-evlt x a)
                   (cadr x)))))

(progn
  (local
   (use-arith-5 t))
  (local
   (defthm gt-of-times-with-same-coef
     (implies (integerp coef)
              (equal (gt (times coef x)
                         (times coef y))
                     (cond ((> coef 0)
                            (gt (ifix x)
                                (ifix y)))
                           ((= coef 0)
                            nil)
                           (t
                            (gt (ifix y)
                                (ifix x))))))
     :hints (("Goal"
              :in-theory (e/d (ifix times rw-dir2)
                              (rw-dir1))))))
  (local
   (defthm dummy-lte-with-both-direction-lemma
     (implies (and (lte y x)
                   (lte x y)
                   (acl2-numberp y)
                   (acl2-numberp x))
              (equal x y))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (rw-dir2)
                              (rw-dir1))))))

  (local
   (defthm dummy-gt-both-direction-lemma
     (implies (and (gt x y)
                   (acl2-numberp x)
                   (acl2-numberp y))
              (not (gt y x)))
     :hints (("Goal"
              :in-theory (e/d (rw-dir2)
                              (rw-dir1))))))
  (local
   (use-arith-5 nil)))

(local
 (defthm lte-gt-lemma-with-times-and-list
   (implies (and (natp x) (natp y) (lte x y))
            (equal (GT (TIMES x (AND-LIST 0 other))
                       y)
                   nil))
   :hints (("Goal"
            :cases ((equal (AND-LIST 0 other) 1))
            :in-theory (e/d (TIMES)
                            ())))))

(local
 (defthmd when-bouth-bounds-are-positive
   (implies (and (lte num max)
                 (lte min num)
                 (lte 0 max)
                 (lte 0 min))
            (equal (gt 0 num) nil))
   :hints (("Goal"
            :in-theory (e/d (rw-dir2) (rw-dir1))))))

(create-regular-eval-lemma and-times-list 3 mult-formula-checks)

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
 :hints (("Goal"
          :do-not-induct t
          :in-theory (e/d* (or*
                            when-bouth-bounds-are-positive
                            AND-TIMES-LIST
                            rp-evlt-when-quotep
                            get-max-min-val
                            RP-TRANS-LST-of-consp
                            RP-TRANS-LST
                            RP-TRANS

                            (:rewrite
                             regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite
                             regular-rp-evl-of_and-times-list_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite
                             regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite
                             regular-rp-evl-of_logbit$inline_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite
                             regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp)
                            (:rewrite
                             regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp)

                            ;; regular-eval-lemmas-with-ex-from-rp
                            ;;rp-evlt-of-ex-from-rp-reverse
                            minus-to---
                            *-is-times
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
                            (:TYPE-PRESCRIPTION include-fnc-fn)
                            include-fnc-fn
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
                            (:DEFINITION INCLUDE-FNC-FN)
                            (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
                            (:REWRITE LTE-AND-GTE-IMPLIES)
                            (:REWRITE VALID-SC-EX-FROM-RP-2)
                            (:DEFINITION EVAL-AND-ALL)
                            (:DEFINITION NFIX)
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
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
                            bitp)))
         (and stable-under-simplificationp
              '(:cases ((equal (AND-LIST 0
                                         (RP-EVLT (CADDR (EX-FROM-RP TERM))
                                                  A))
                               0))))
         ))

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

(defthm
  valid-sc-car-cddddr
  (implies (and (consp term)
                (not (equal (car term) 'if))
                (not (equal (car term) 'rp))
                (not (equal (car term) 'quote))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term))
                (consp (cddddr term))
                (valid-sc term a))
           (valid-sc (car (cddddr term)) a))
  :hints
  (("goal" :in-theory (e/d (ex-from-rp is-if is-rp) nil))))

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


(defret-mutual decompress-s-c-correct
  (defret decompress-s-c-correct
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
    :fn decompress-s-c)
  (defret decompress-s-c-list-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms lst a))
             (and (valid-sc-subterms res-term-lst a)
                  (valid-sc coughed-s a)
                  (valid-sc coughed-pp a)
                  (equal (sum (sum-list (rp-evlt-lst res-term-lst a))
                              (sum-list (rp-evlt coughed-s a))
                              (sum-list (rp-evlt coughed-pp a)))
                         (sum-list (rp-evlt-lst lst a)))
                  (equal (sum (sum-list (rp-evlt-lst res-term-lst a))
                              (sum-list (rp-evlt coughed-s a))
                              (sum-list (rp-evlt coughed-pp a))
                              other)
                         (sum (sum-list (rp-evlt-lst lst a))
                              other))))
    :fn decompress-s-c-lst)
  :mutual-recursion decompress-s-c

  :hints (("Goal"
           :do-not-induct t
           :expand ((RP-TRANS-LST (CDR (EX-FROM-RP TERM))))
           :in-theory (e/d (decompress-s-c
                            decompress-s-c-lst
                            equivalence-of-two-f2-2
                            f2-of-times2-reverse
                            rp-trans-lst-of-consp
                            rp-evlt-of-ex-from-rp-reverse-only-atom
                            regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_c_when_mult-formula-checks
                            regular-rp-evl-of_s_when_mult-formula-checks
                            )
                           (rp-evlt-of-ex-from-rp
                            f2-of-times2
                            (:type-prescription valid-sc)
                            (:rewrite valid-sc-when-single-c-p)
                            (:rewrite evl-of-extract-from-rp-2)
                            (:rewrite ex-from-synp-lemma1)
                            (:rewrite rp-evl-of-variable)
                            (:definition eval-and-all)
                            (:rewrite sum-of-negated-elements)
                            (:rewrite default-cdr)
                            (:definition include-fnc-fn)
                            (:rewrite not-include-rp-means-valid-sc)
                            (:definition include-fnc-subterms-fn)
                            (:rewrite default-car)
                            rp-trans-lst-of-consp
                            rp-termp
                            rp-trans
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

(defretd rp-evlt-of-term-when-coef-is-known
  (implies (and (EQUAL coef free-coef)
                (integerp free-coef)
                (syntaxp (or (quotep free-coef)
                             (integerp free-coef)))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (implies (integerp (rp-evlt term a))
                         (equal (rp-evlt term a)
                                (times free-coef
                                       (rp-evlt res-term a))))
                (equal (times2 (rp-evlt term a))
                       (times2
                        (times free-coef
                               (rp-evlt res-term a))))
                (equal (sum other (rp-evlt term a))
                       (sum other
                            (times free-coef
                                   (rp-evlt res-term a))))
                (equal (sum (rp-evlt term a) other)
                       (sum other
                            (times free-coef
                                   (rp-evlt res-term a))))))
  :Fn GET-PP-AND-COEF
  :hints (("Goal"
           :in-theory (e/d (TIMES2) ()))))

(Local
 (defthm times2-and-ifix
   (and (equal (times2 (ifix x))
               (times2 x))
        (equal (ifix (times2 x))
               (times2 x))
        (equal (times2 (- (ifix x)))
               (- (times2 x))))
   :hints (("Goal"
            :in-theory (e/d (sum times2)
                            (+-IS-SUM))))))

(local
 (defthm sum-of--of-ifix
   (and (equal (sum x (- (ifix y)))
               (sum x (- y)))
        (equal (sum (- (ifix y)) x)
               (sum x (- y))))
   :hints (("Goal"
            :in-theory (e/d (ifix) ())))))

(local
 (defthm times2-cancel-substracted
   (and (equal (sum (times2 x) (- x))
               (sum x))
        (equal (sum (- (times2 x)) x)
               (sum (- x)))
        (equal (sum x (- (times2 x)))
               (sum (- x))))
   :hints (("Goal"
            :in-theory (e/d (ifix times2 sum) (+-IS-SUM))))))

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
                             or*
                             rp-evlt-of-term-when-coef-is-known


                             
                             )

                            
                            
                            (rp-trans-lst
                             ;; VALID-SC-SUBTERMS-CONS
                             (:DEFINITION SUM-LIST-EVAL)
                             (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                             ;;                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:DEFINITION VALID-SC-SUBTERMS)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION INCLUDE-FNC-FN)
                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:TYPE-PRESCRIPTION --)
                             (:TYPE-PRESCRIPTION BINARY-SUM)
                             (:TYPE-PRESCRIPTION VALID-SC-SUBTERMS)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS-FN)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS-FN)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC-FN)
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
                              REGULAR-RP-EVL-OF_LOGBIT$inline_WHEN_MULT-FORMULA-CHECKS)
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

(progn

  (local
   (in-theory (enable -to---))))

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
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
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
           :do-not '(preprocess)
           :in-theory (e/d (sum  ifix --)
                           (-TO---
                            +-IS-SUM)))))

(defthm minus-of-minus
  (equal (-- (-- a))
         (ifix a))
  :hints (("Goal"
           :in-theory (e/d (--) ()))))

(defthm --of-ifix
  (equal (-- (ifix x))
         (-- x))
  :hints (("Goal"
           :in-theory (e/d (-- ifix) ()))))

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
  (and (equal (sum (-- a) (f2 (sum a b)))
              (f2 (sum (-- a) b))))
  :hints (("Goal"
           :in-theory (e/d () ()))))

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
           :in-theory (e/d (ifix sum --)
                           (-to---
                            +-IS-SUM)))))

(defthm f2-of-minus-3
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
                            (limit *large-number*)
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
                                      :LIMIT *large-number*)))))
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
                                      :LIMIT *large-number*)))))
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
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
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
                            (:DEFINITION INCLUDE-FNC-FN)
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
                               ;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
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
                   (light-pp-term-p term)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("goal"
              :do-not-induct t
              :expand ((light-pp-term-p term))
              :in-theory (e/d* (light-pp-term-p
                                is-rp
                                regular-eval-lemmas-with-ex-from-rp
                                is-if)
                               (bitp
                                -TO---
                                pp-term-p
                                rp-trans-is-term-when-list-is-absent
                                ex-from-rp-lemma1
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
                  (limit *large-number*))
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
                            (:DEFINITION INCLUDE-FNC-FN)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
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
                            is-rp
                            CREATE-TIMES-INSTANCE)
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
             :in-theory (e/d* (regular-eval-lemmas
                               and-list-instance-to-binary-and)
                              (rp-trans))))))

(defret pp-flatten-correct-with-sum-list-eval
  (implies (and (mult-formula-checks state)
                (force (pp-term-p term))
                (or (= coef 1)
                    (= coef -1))
                (force (rp-termp term))
                (force (valid-sc term a))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval pp-lst a)
                  (times coef (rp-evlt term a))))
  :fn pp-flatten
  :hints (("Goal"
           :use ((:instance pp-flatten-correct))
           :in-theory (e/d () ()))))

(defret pp-flatten-with-binds-correct-with-sum-list-eval
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (or (= coef 1)
                    (= coef -1))
                (force (rp-termp term))
                (force (valid-sc term a))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval pp-lst a)
                  (times coef (rp-evlt term a))))
  :fn pp-flatten-with-binds
  :hints (("Goal"
           :use ((:instance pp-flatten-with-binds-correct))
           :in-theory (e/d () (pp-flatten-with-binds-correct)))))

(defret single-s-to-pp-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (rp-termp pp1))
                (force (rp-termp pp2))
                (force (rp-termp pp3))
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
                           (pp-term-p `(binary-xor ,x ,y)))
                    (:free (x y)
                           (rp-termp `(binary-xor ,x ,y))))
           :in-theory (e/d* (single-s-to-pp-lst
                             rp-term-listp
                             ex-from-rp
                             is-rp is-if
                             REGULAR-RP-EVL-OF_BINARY-XOR_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                            (rp-termp
                             and-list-instance-to-binary-and-correct
                             rp-trans
                             (:DEFINITION PP-TERM-P-fn)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                             (:REWRITE DEFAULT-CAR)
                             ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                             valid-sc)))))

(defret s-pattern2-reduce-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                (rp-termp pp)
                reducedp)
           (and (valid-sc-subterms reduced-pp-lst a)))
  :fn s-pattern2-reduce
  :hints (("Goal"
           :expand ((:free (x)
                           (valid-sc `(sum-list ,x) a)))
           :in-theory (e/d (rp-term-listp
                            s-pattern2-reduce
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
                           (+-IS-SUM
                            -to---
                            mod2-is-m2)))))

(defret s-pattern2-reduce-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (rp-termp pp)
                (valid-sc c a)
                reducedp)
           (and (equal (sum-list-eval REDUCED-PP-LST a)
                       (m2 (sum (sum-list (rp-evlt pp a))
                                (sum-list (rp-evlt c a)))))))
  :fn s-pattern2-reduce
  :hints (("Goal"
           :expand ((:free (x)
                           (valid-sc `(sum-list ,x) a)))
           :in-theory (e/d (rp-term-listp
                            s-pattern2-reduce
                            is-rp if
                            m2-of-1
                            valid-sc-single-step)
                           (-TO---
                            valid-sc)))))

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
                           (+-IS-SUM -TO--- mod2-is-m2)))))

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
                           (m2-of-1 -TO---
                                    m2-of-1-v2)))))

(defthmd sum-form-to-binary-not
  (implies (bitp x)
           (and (equal (sum (-- x) 1)
                       (binary-not x))
                (equal (sum 1 (-- x))
                       (binary-not x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(progn
  (local
   (use-arith-5 t))
  (defthmd binary-not-of-m2
    (equal (not$ (m2 x))
           (m2 (sum 1 x)))
    :hints (("Goal"
             :in-theory (e/d (binary-not sum m2 ifix bit-fix f2)
                             (-TO--- +-IS-SUM floor2-if-f2
                                     mod2-is-m2)))))
  (local
   (use-arith-5 nil)))

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
           :in-theory (e/d (binary-not-of-m2
                            sum-form-to-binary-not
                            S-PATTERN3-REDUCE
                            m2-of-1
                            VALID-SC-SUBTERMS-implies-VALID-SC-SUBTERMS-cdr
                            sum-list-eval-of-cdr
                            is-rp
                            valid-sc-single-step)
                           (M2-OF---
                            M2-OF-1-V2
                            (:e --))))))

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
           :expand ((pattern0-reduce-aux nil pp-lst nil limit)
                    (:free (x) (valid-sc (cons 'binary-and x) a))
                    (:free (x) (valid-sc (cons 'binary-xor x) a)))
           :in-theory (e/d (is-rp is-if
                                  pattern0-reduce-aux
                                  pattern0-reduce-aux-s-lst
                                  pattern0-reduce-aux-c-lst
                                  )
                           ((:DEFINITION VALID-SC)
                            (:DEFINITION EVAL-AND-ALL)
                            -to---
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION RP-TRANS)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE VALID-SC-CADR)
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            ;;(:REWRITE VALID-SC-CADDR)
                            ;;(:REWRITE VALID-SC-CADDDR)
                            (:DEFINITION INCLUDE-FNC-FN))))))

(local
 (in-theory (disable -to---)))

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
             :expand (PATTERN0-REDUCE-AUX-S-LST S-LST LIMIT SEARCH-LIMIT)
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
             :expand (PATTERN0-REDUCE-AUX-S-LST S-LST LIMIT SEARCH-LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-s-lst) ()))))

  (defret pattern0-reduce-aux-s-lst-cnt-implies-3
    (implies (and (equal s-cnt 0)
                  s-valid)
             (not (consp s-lst)))
    :fn pattern0-reduce-aux-s-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-S-LST S-LST LIMIT SEARCH-LIMIT)
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
             :expand (PATTERN0-REDUCE-AUX-C-LST C-LST LIMIT SEARCH-LIMIT)
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
             :expand (PATTERN0-REDUCE-AUX-C-LST C-LST LIMIT SEARCH-LIMIT)
             :in-theory (e/d (pattern0-reduce-aux-c-lst) ()))))

  (defret pattern0-reduce-aux-c-lst-cnt-implies-3
    (implies (and (equal c-cnt 0)
                  c-valid)
             (not (consp c-lst)))
    :fn pattern0-reduce-aux-c-lst
    :rule-classes :forward-chaining
    :hints (("Goal"
             :do-not-induct t
             :expand (PATTERN0-REDUCE-AUX-C-LST C-LST LIMIT SEARCH-LIMIT)
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

           :expand ((PATTERN0-REDUCE-AUX NIL PP-LST NIL LIMIT)
                    (:free (x) (pp-term-p (cons 'binary-and x)))
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
                             ;;                             (:REWRITE ACL2::O-FIRST-EXPT-O-INFP)
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
                             ;;(:REWRITE RP-TRANS-OPENER)
                             VALID-SC-SUBTERMS-CONS
                             valid-sc
                             eval-and-all
                             include-fnc-fn)))))

(defret c-pattern0-reduce-correct
  (implies (and (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst)
                (rp-term-listp s-lst)
                reduced)
           (equal (f2 (sum (sum-list-eval c-lst  a)
                           (sum-list-eval pp-lst a)
                           (sum-list-eval s-lst a)))
                  0))
  :fn c-pattern0-reduce
  :hints (("goal"
           :do-not-induct t
           :expand ((:free (x)
                           (pp-term-p (cons 'binary-and x)))
                    (:free (x)
                           (ex-from-rp (cons 'binary-and x))))
           :use ((:instance pp-flatten-correct
                            (term (list 'binary-and
                                        (mv-nth 0
                                                (pattern0-reduce-aux s-lst pp-lst c-lst 10))
                                        (mv-nth 1
                                                (pattern0-reduce-aux s-lst pp-lst c-lst 10))))
                            (coef 1)
                            (disabled nil)
                            (term-size-limit nil)))
           ;;:use ((:instance c-pattern0-reduce-correct-lemma
           :in-theory (e/d (RP-TERM-LISTP
                            c-pattern0-reduce
                            is-rp)
                           (pp-flatten-correct)))))

(defret s-pattern0-reduce-correct
  (implies (and (rp-termp pp)
                (rp-termp c)
                (valid-sc pp a)
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
           :use ((:instance pp-flatten-correct
                            (term (LIST
                                   'BINARY-xor
                                   (MV-NTH 0
                                           (PATTERN0-REDUCE-AUX nil
                                                                (list-to-lst pp) (list-to-lst c) 10))
                                   (MV-NTH 1
                                           (PATTERN0-REDUCE-AUX nil
                                                                (list-to-lst pp) (list-to-lst c) 10))))
                            (coef 1)
                            (disabled nil)
                            (term-size-limit nil)))
           ;;:use ((:instance c-pattern0-reduce-correct-lemma
           :in-theory (e/d (rp-term-listp
                            s-pattern0-reduce
                            is-rp)
                           (PP-FLATTEN-CORRECT)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; create-s-instance lemmas

;; m2-of-bitp
(defthm bitp-of-rp-evlt-of-binary-fnc-p/and-listp/logbit-p
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (or (binary-fnc-p term)
                    (binary-fnc-p (ex-from-rp term))
                    (logbit-p term)
                    (logbit-p (ex-from-rp term))
                    (and-list-p term)
                    (and-list-p (ex-from-rp term))))
           (and (bitp (rp-evlt term a))
                (bitp (rp-evlt (ex-from-rp term) a))))
  :hints (("Goal"
           :in-theory (e/d* (regular-eval-lemmas
                             BINARY-FNC-P
                             regular-eval-lemmas-with-ex-from-rp)
                            (ex-from-rp)))))

(defret create-s-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp pp)
                (rp-termp c)
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
           :in-theory (e/d (or* binary-fnc-p
                                create-s-instance
                                m2-of-bitp
                                bitp-implies-integerp
                                valid-sc-single-step
                                rp-trans-lst-of-consp
                                is-rp)
                           (include-fnc-fn)))))

(defret create-s-instance-correct-corollary
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                (rp-termp pp)
                (rp-termp c))
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
                             (:REWRITE CONSP-OF-RP-EVL-OF-TRANS-LIST)
                             (:REWRITE CONSP-OF-RP-TRANS-LST)
                             (:TYPE-PRESCRIPTION RP-TRANS-LST)
                             (:REWRITE RP-EVL-LST-OF-CONS)
                             (:DEFINITION RP-TRANS-LST))))))

(defret and-list-to-binary-and-aux-valid-sc
  (implies (and ;;(rp-evl-meta-extract-global-facts :state state)
            ;;(mult-formula-checks state)
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
                             (:REWRITE CONSP-OF-RP-EVL-OF-TRANS-LIST)
                             (:REWRITE CONSP-OF-RP-TRANS-LST)
                             (:TYPE-PRESCRIPTION RP-TRANS-LST)
                             (:REWRITE RP-EVL-LST-OF-CONS)
                             (:DEFINITION RP-TRANS-LST))))))

(defthm remove-hash-arg-of-and-list
  (implies (syntaxp (and (not (equal hash 0))
                         (not (equal hash ''0))))
           (equal (and-list hash lst)
                  (and-list 0 lst)))
  :hints (("Goal"
           :in-theory (e/d (and-list) ()))))

(defthmd has-bitp-rp-force-hyp-rewrite
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (bind-free (list (cons 'a 'a)) (a)) 
                (force (valid-sc term a)))
           (equal (has-bitp-rp term)
                  (and (hide (has-bitp-rp term))
                       (bitp (rp-evlt term a))
                       (bitp (rp-evlt (ex-from-rp term) a)))))
  :hints (("Goal"
           :expand (hide (has-bitp-rp term))
           :use ((:instance pp-termp-is-bitp-lemma))
           :in-theory (e/d () ()))))

(defret and-list-to-binary-and-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (rp-evlt res a)
                       (rp-evlt term a))
                (implies (and valid
                              (valid-sc term a))
                         (and (integerp (rp-evlt res a))
                              (integerp (rp-evlt term a))))
                (implies (and (valid-sc term a)
                              valid)
                         (and (bitp (rp-evlt res a))
                              (bitp (rp-evlt term a))))))
  :fn and-list-to-binary-and
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (and-list-to-binary-and
                             has-bitp-rp-force-hyp-rewrite
                             and-list
                             BINARY-FNC-P
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp)
                            (valid-sc)))))

(defret and-list-to-binary-and-valid-sc
  (implies (and ;;(rp-evl-meta-extract-global-facts :state state)
            ;;(mult-formula-checks state)
            ;;valid
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
                 (mult-formula-checks state)
                 (valid-sc-subterms pp-lst a))
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
                             (:rewrite
                              regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp)
                             regular-rp-evl-of_s-c-res_when_mult-formula-checks
                             )
                            (;;rp-evlt-of-ex-from-rp
                             INCLUDE-FNC-FN
                             INCLUDE-FNC-SUBTERMS-FN
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
                (rp-termp pp1)
                (rp-termp pp2)
                (rp-termp pp3)
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
                            rp-term-listp
                            EX-FROM-RP
                            is-rp is-if

                            REGULAR-RP-EVL-OF_binary-or_WHEN_MULT-FORMULA-CHECKS
                            REGULAR-RP-EVL-OF_binary-and_WHEN_MULT-FORMULA-CHECKS
                            )
                           (valid-sc
                            (:DEFINITION PP-TERM-P-fn)
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
                (valid-sc-subterms c-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
           (and (valid-sc-subterms res-pp-lst a)))
  :fn c-pattern2-reduce
  :hints (("Goal"
           :do-not-induct t
           :expand (VALID-SC ''1 A)
           :in-theory (e/d (RP-TERM-LISTP
                            c-pattern2-reduce)
                           ()))))

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
                (rp-term-listp pp-lst)
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
           :in-theory (e/d (rp-term-listp
                            c-pattern2-reduce
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (rp-evlt-of-ex-from-rp
                            rp-trans)))))

(defret c-pattern2-reduce-correct-with-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-pattern4-compress lemmas

(defret create-and-list-instance-valid-sc
  (implies (and (force (valid-sc-subterms lst a)))
           (valid-sc and-list-instance a))
  :fn create-and-list-instance
  :hints (("Goal"
           :in-theory (e/d (create-and-list-instance)
                           ()))))

(defthm not-equal-to-to-when-bitp
  (implies (and (bitp x)
                (not (equal x 1)))
           (equal (equal x 0) t)))

(defret create-and-list-instance-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (equal (rp-evlt and-list-instance a)
                  (and-list 0 (rp-evlt-lst lst a))))
  :fn create-and-list-instance
  :hints (("Goal"
           :use ((:instance BITP-OF-LOGBIT
                            (x (rp-evlt (EX-FROM-RP (CAR LST)) a))))
           :expand ((:free (x) (AND-LIST 0 (LIST x))))
           :in-theory (e/d (and$ ;;bitp
                            has-bitp-rp-force-hyp-rewrite
                            create-and-list-instance
                            rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (LOGBIT$INLINE
                            rp-evlt-of-ex-from-rp
                            )))))


(defthm valid-sc-subterms-SET-DIFFERENCE-EQUAL
  (implies (and (force (valid-sc-subterms x a))
                ;; (force (valid-sc-subterms y a))
                )
           (valid-sc-subterms (SET-DIFFERENCE-EQUAL x y) a)))

(defret simplify-pp-lst-from-e-lst-valid-sc
  (implies (and (valid-sc-subterms pp-lst a)
                ;;changed
                )
           (valid-sc-subterms new-pp-lst a))
  :fn simplify-pp-lst-from-e-lst
  :hints (("Goal"
           :in-theory (e/d (simplify-pp-lst-from-e-lst) ()))))

(defret-mutual simplify-s/c-from-e-lst-valid-sc
  (defret simplify-s/c-from-e-lst-main-valid-sc
    (implies (valid-sc s/c a)
             (valid-sc res a))
    :fn simplify-s/c-from-e-lst-main)
  (defret simplify-s/c-from-e-lst-valid-sc
    (implies (valid-sc s/c a)
             (valid-sc res a))
    :fn simplify-s/c-from-e-lst)
  (defret simplify-s/c-list-from-e-lst-valid-sc
    (implies (valid-sc-subterms s/c-lst a)
             (valid-sc-subterms res-lst a))
    :fn simplify-s/c-list-from-e-lst)
  :mutual-recursion simplify-s/c-from-e-lst
  :hints (("Goal"
           :in-theory (e/d (simplify-s/c-from-e-lst
                            simplify-s/c-from-e-lst-main
                            simplify-s/c-list-from-e-lst) ()))))


(defret create-and-times-list-instance-valid-sc
  (implies (and (force (valid-sc-subterms lst a))
                (force (valid-sc s/c a)))
           (valid-sc ins a))
  :fn create-and-times-list-instance
  :hints (("Goal"
           :in-theory (e/d (create-and-times-list-instance)
                           ()))))

(local
 (defthmd simplify-pp-lst-from-e-lst-correct-lemma
   (implies (and (equal (and-list 0 (rp-evlt-lst e-lst a)) 1)
                 (member-equal x e-lst)
                 (bitp (rp-evlt x a)))
            (equal (rp-evlt x a) 1))
   :hints (("Goal"
            :expand ((AND-LIST 0 (CONS 0 (RP-EVLT-LST (CDR E-LST) A)))
                     (AND-LIST 0
                               (CONS (RP-EVLT (CAR E-LST) A)
                                     (RP-EVLT-LST (CDR E-LST) A))))
            :in-theory (e/d (and$) ())))))

(local
 (defthmd simplify-pp-lst-from-e-lst-correct-lemma2
   (implies (and (equal (and-list 0 (rp-evlt-lst e-lst a)) 1)
                 (member-equal x e-lst))
            (equal (bit-fix (rp-evlt x a)) 1))
   :hints (("Goal"
            :expand ((AND-LIST 0 (CONS 0 (RP-EVLT-LST (CDR E-LST) A)))
                     (AND-LIST 0
                               (CONS (RP-EVLT (CAR E-LST) A)
                                     (RP-EVLT-LST (CDR E-LST) A))))
            :in-theory (e/d (and$) ())))))


(defthm and-list-of-SET-DIFFERENCE-EQUAL-when-lst2-is-1
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (equal (and-list 0 (rp-evlt-lst e-lst a)) 1))
           (equal (AND-LIST 0 (RP-EVLT-LST (set-difference-equal lst1 e-lst) a))
                  (and-list 0 (RP-EVLT-LST lst1 A))))
  :hints (("Goal"
           :expand ((:free (y)
                           (and-list 0 (cons (rp-evlt (car lst1) a) y))))
           :in-theory (e/d (simplify-pp-lst-from-e-lst-correct-lemma2
                            simplify-pp-lst-from-e-lst-correct-lemma
                            and$)
                           ()))))


(defthm same-sums-cancel
  (implies (and (acl2-numberp x) (acl2-numberp y))
           (equal (equal (+ a x) (+ a y))
                  (equal x y))))

(local
 (in-theory (disable set-difference-equal)))

(defret simplify-pp-lst-from-e-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                (equal (and-list 0 (rp-evlt-lst e-lst a)) 1))
           (equal (sum-list-eval new-pp-lst a)
                  (sum-list-eval pp-lst a)))
  :fn simplify-pp-lst-from-e-lst
  :hints (("goal"
           :expand ((SIMPLIFY-PP-LST-FROM-E-LST PP-LST E-LST))
           :in-theory (e/d* (sum
                             AND-TIMES-LIST
                             and$
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             simplify-pp-lst-from-e-lst)
                            (+-is-sum
                             valid-sc
                             logbit
                             rp-trans-is-term-when-list-is-absent
                             rp-trans)))
          (and stable-under-simplificationp
               '(:expand ((:free (x) (and-list 0 (list x))))
                 :use ((:instance simplify-pp-lst-from-e-lst-correct-lemma
                                  (x (car pp-lst))))))))

(defret-mutual simplify-s/c-from-e-lst-correct
  (defret simplify-s/c-from-e-lst-main-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc s/c a)
                  (case-split (equal (and-list 0 (rp-evlt-lst e-lst a)) 1)))
             (equal (rp-evlt res a)
                    (rp-evlt s/c a)))
    :fn simplify-s/c-from-e-lst-main)
  (defret simplify-s/c-from-e-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc s/c a)
                  (case-split (equal (and-list 0 (rp-evlt-lst e-lst a)) 1)))
             (equal (rp-evlt res a)
                    (rp-evlt s/c a)))
    :fn simplify-s/c-from-e-lst)
  (defret simplify-s/c-list-from-e-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms s/c-lst a)
                  (equal (and-list 0 (rp-evlt-lst e-lst a)) 1))
             (equal (rp-evlt-lst res-lst a)
                    (rp-evlt-lst s/c-lst a)))
    :fn simplify-s/c-list-from-e-lst)
  :mutual-recursion simplify-s/c-from-e-lst
  :hints (("goal"
           :in-theory (e/d* ((:rewrite regular-rp-evl-of_c_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp)

                             simplify-s/c-from-e-lst-main
                             simplify-s/c-from-e-lst
                             simplify-s/c-list-from-e-lst
                             )
                            (rp-trans)))))

(defret create-and-times-list-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (force (valid-sc-subterms lst a))
                (force (valid-sc s/c a)))
           (equal (rp-evlt ins a)
                  (and-times-list 0
                                  (rp-evlt-lst lst a)
                                  (rp-evlt s/c a))))
  :fn create-and-times-list-instance
  :hints (("Goal"
           :in-theory (e/d* (create-and-times-list-instance
                             has-bitp-rp-force-hyp-rewrite
                             and-times-list
                             regular-rp-evl-of_and-times-list_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_and-times-list_when_mult-formula-checks
                             regular-rp-evl-of_c_when_mult-formula-checks
                             regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_s_when_mult-formula-checks
                             regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp
                             rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                            (rp-evlt-of-ex-from-rp)))
          (and stable-under-simplificationp
               '(:use ((:instance simplify-s/c-from-e-lst-main-correct
                                  (limit *big-number*)
                                  (e-lst (SORT-AND$-LIST LST (SUM (LEN (CDR LST)) 1))))
                       (:instance simplify-s/c-from-e-lst-main-correct
                                  (limit *big-number*)
                                  (e-lst (SORT-AND$-LIST LST 0))))))))



(defthm valid-sc-subterms-intersection-equal
  (implies (and (force (valid-sc-subterms x a))
                (force (valid-sc-subterms y a)))
           (valid-sc-subterms (intersection-equal x y) a)))

(defret collect-common-e-lst-valid-sc
  (implies (force (valid-sc-subterms pp-lst a))
           (valid-sc-subterms commons a))
  :fn collect-common-e-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (collect-common-e-lst pp-lst)
           :in-theory (e/d (collect-common-e-lst)
                           (valid-sc-subterms-cons
                            intersection-equal)))))

(defret remove-e-lst-from-e-lst-valid-sc
  (implies (and (force (valid-sc-subterms e-lst a)))
           (and (valid-sc-subterms res-e-lst a)))
  :fn remove-e-lst-from-e-lst
  :hints (("Goal"
           :in-theory (e/d (remove-e-lst-from-e-lst) ()))))

(defret remove-e-lst-from-pp-lst-valid-sc
  (implies (and (force (valid-sc-subterms pp-lst a)))
           (and (valid-sc-subterms s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms c-lst a)))
  :fn remove-e-lst-from-pp-lst
  :hints (("Goal"
           :in-theory (e/d (remove-e-lst-from-pp-lst) ()))))

(defret break-down-two-arg-c-valid-sc
  (implies (and (force (valid-sc c-in a)))
           (and (valid-sc-subterms e-lst a)
                (valid-sc res-c a)))
  :fn break-down-two-arg-c
  :hints (("Goal"
           :in-theory (e/d (break-down-two-arg-c) ()))))

(defret c-pattern4-compress-valid-sc
  (implies (and valid
                (force (valid-sc-subterms pp-lst a)))
           (valid-sc-subterms res-pp-lst a))
  :fn c-pattern4-compress
  :hints (("Goal"
           :in-theory (e/d (c-pattern4-compress)
                           ()))))

;;;;


(local
 (include-book "std/lists/sets" :dir :system))

(defret remove-e-lst-from-e-lst-correct
  (implies valid
           (equal (* (and-list 0 (rp-evlt-lst res-e-lst a))
                     (and-list 0 (rp-evlt-lst to-remove-e-lst a)))
                  (and-list 0 (rp-evlt-lst e-lst a))))
  :fn remove-e-lst-from-e-lst
  :hints (("Goal"
           :expand ((:free ( y)
                           (and-list 0 (cons (RP-EVLT (CAR E-LST) A) y))))
           :in-theory (e/d (and$ remove-e-lst-from-e-lst)
                           ()))))

(local
 (defthmd dummy-*-lemma-1
   (implies (equal (* x y) z)
            (equal (* x other y)
                   (* other z)))
   :hints (("Goal"
            :in-theory (e/d (ACL2::|(* y (* x z))|
                                   ACL2::|(* y x)|
                                   ACL2::|arith (* c (* d x))|
                                   ACL2::|arith (* y (* x z))|)
                            ())))))

(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (defret remove-e-lst-from-pp-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms pp-lst a)
                  valid
                  (equal (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                         (and-list 0 (rp-evlt-lst to-remove-e-lst a))))
             (equal (and-times-list
                     hash
                     (rp-evlt-lst to-remove-e-lst-equiv a)
                     (sum (sum-list-eval s-lst a)
                          (sum-list-eval res-pp-lst a)
                          (sum-list-eval c-lst a)))
                    (sum-list-eval pp-lst a)))
    :fn remove-e-lst-from-pp-lst
    :hints (("Goal"
             :in-theory (e/d* (dummy-*-lemma-1
                               remove-e-lst-from-pp-lst
                               AND-TIMES-LIST
                               ;; regular-eval-lemmas
                               ;; regular-eval-lemmas-with-ex-from-rp
                               (:REWRITE REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS)
                               (:REWRITE REGULAR-RP-EVL-OF_AND-TIMES-LIST_WHEN_MULT-FORMULA-CHECKS)
                               (:REWRITE REGULAR-RP-EVL-OF_LOGBIT$INLINE_WHEN_MULT-FORMULA-CHECKS)
                               sum)
                              (valid-sc
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE EX-FROM-SYNP-LEMMA1)
                               (:DEFINITION IS-SYNP$INLINE)
                               (:REWRITE LTE-CHAIN-SMART)
                               (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                               (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                               PP-TERM-P-FN
                               PP-TERM-P-IS-BITP-STRICT=NIL
                               (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                               (:REWRITE VALID-SC-SUBTERMS-CONS)
                               rp-trans
                               rp-trans-is-term-when-list-is-absent
                               +-IS-SUM
                               remove-e-lst-from-e-lst-correct)))
            (and stable-under-simplificationp
                 '(:use ((:instance remove-e-lst-from-e-lst-correct
                                    (e-lst (LIST (CAR PP-LST))))
                         (:instance remove-e-lst-from-e-lst-correct
                                    (e-lst (CDR (CADDR (CAR PP-LST)))))))))))

(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (defret remove-e-lst-from-pp-lst-correct2
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms pp-lst a)
                  valid
                  (equal (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                         (and-list 0 (rp-evlt-lst to-remove-e-lst a)))
                  (not s-lst)
                  )
             (equal (* (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                       (f2 (sum (sum-list-eval res-pp-lst a)
                                (sum-list-eval c-lst a))))
                    (f2 (sum-list-eval pp-lst a))))
    :fn remove-e-lst-from-pp-lst
    :hints (("goal"
             :do-not-induct t
             :use ((:instance remove-e-lst-from-pp-lst-correct
                              )
                   (:instance bitp-and-list
                              (hash 0)
                              (y (rp-evlt-lst to-remove-e-lst a))))
             :in-theory (e/d* (and-times-list bitp)
                              (bitp-and-list
                               (:type-prescription and-list)
                               remove-e-lst-from-pp-lst-correct))))))

(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (defret remove-e-lst-from-pp-lst-correct3
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms pp-lst a)
                  valid

                  (not s-lst)
                  (not res-pp-lst)
                  (not c-lst)
                  )
             (equal (equal 0
                           (f2 (sum-list-eval pp-lst a)))
                    t))
    :fn remove-e-lst-from-pp-lst
    :hints (("goal"
             :do-not-induct t
             :use ((:instance remove-e-lst-from-pp-lst-correct
                              (to-remove-e-lst-equiv to-remove-e-lst))
                   (:instance bitp-and-list
                              (hash 0)
                              (y (rp-evlt-lst to-remove-e-lst a))))
             :in-theory (e/d* (and-times-list bitp)
                              (bitp-and-list
                               (:type-prescription and-list)
                               remove-e-lst-from-pp-lst-correct))))))

(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (defret remove-e-lst-from-pp-lst-correct4
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms pp-lst a)
                  valid
                  (equal (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                         (and-list 0 (rp-evlt-lst to-remove-e-lst a)))
                  (not s-lst)
                  (not c-lst)
                  )
             (equal (* (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                       (f2 (sum-list-eval res-pp-lst a)))
                    (f2 (sum-list-eval pp-lst a))))
    :fn remove-e-lst-from-pp-lst
    :hints (("goal"
             :do-not-induct t
             :use ((:instance remove-e-lst-from-pp-lst-correct
                              )
                   (:instance bitp-and-list
                              (hash 0)
                              (y (rp-evlt-lst to-remove-e-lst a))))
             :in-theory (e/d* (and-times-list bitp)
                              (bitp-and-list
                               (:type-prescription and-list)
                               remove-e-lst-from-pp-lst-correct))))))

(with-output
  :off :all
  :on (error summary)
  :gag-mode :goals
  (defret remove-e-lst-from-pp-lst-correct5
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc-subterms pp-lst a)
                  valid
                  (equal (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                         (and-list 0 (rp-evlt-lst to-remove-e-lst a)))
                  (not res-pp-lst)
                  (not s-lst)
                  )
             (equal (* (and-list 0 (rp-evlt-lst to-remove-e-lst-equiv a))
                       (f2 (sum-list-eval c-lst a)))
                    (f2 (sum-list-eval pp-lst a))))
    :fn remove-e-lst-from-pp-lst
    :hints (("goal"
             :do-not-induct t
             :use ((:instance remove-e-lst-from-pp-lst-correct
                              )
                   (:instance bitp-and-list
                              (hash 0)
                              (y (rp-evlt-lst to-remove-e-lst a))))
             :in-theory (e/d* (and-times-list bitp)
                              (bitp-and-list
                               (:type-prescription and-list)
                               remove-e-lst-from-pp-lst-correct))))))

(encapsulate nil
  (local
   (defthmd f2-of-two-bitps
     (implies (and (bitp a) (bitp b))
              (equal (f2 (sum a b))
                     (and$ a b)))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthmd dummy-bitp-lemma
     (implies (and (bitp x)
                   (not (EQUAL x 1)))
              (equal (equal (ifix x) 0) t))))


  (defthmd rp-evlt-of-list-more-general
    (implies (equal (car x) 'list)
             (equal (rp-evlt x a)
                    (rp-evlt-lst (cdr x) a))))

  (local
   (defthm f2-of-*-two-bitps
     (implies (and (bitp a) (bitp b))
              (equal (f2 (* a b)) 0))))

  (local
   (defthm ifix-of-bitp
     (implies (bitp x)
              (equal (ifix x) x))))

  (defret break-down-two-arg-c-is-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc c-in a))
             (equal (and-times-list hash
                                    (rp-evlt-lst e-lst a)
                                    (rp-evlt res-c a))
                    (ifix (rp-evlt c-in a))))
    :fn break-down-two-arg-c
    :hints (("Goal"
             :do-not-induct t
             :do-not '(generalize)
             :induct (break-down-two-arg-c c-in)
             :expand ((:free (x y)
                             (AND-LIST 0 (CONS (RP-EVLT x A) y)))
                      (:free (x1 x2 y)
                             (AND-LIST 0 (CONS (logbit x1 x2) y)))
                      (:free (x y)
                             (AND-LIST 0 (CONS (AND-LIST 0 x) y)))
                      (:free (x y)
                             (AND-LIST 0 (CONS 0 y)))
                      (:free (x y)
                             (AND-LIST 0 (CONS 1 y))))
             :in-theory (e/d* (f2-of-two-bitps

                               dummy-bitp-lemma
                               and$ ;;bitp
                               ;;regular-eval-lemmas-with-ex-from-rp
                               (:REWRITE REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS)
                               (:REWRITE REGULAR-RP-EVL-OF_AND-times-LIST_WHEN_MULT-FORMULA-CHECKS)
                               (:REWRITE regular-rp-evl-of_logbit$inline_when_mult-formula-checks)
                               (:REWRITE
                                REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)

                               has-bitp-rp-force-hyp-rewrite
                               ;;regular-eval-lemmas
                               AND-TIMES-LIST
                               break-down-two-arg-c
                               rp-evlt-of-list-more-general
                               rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                              (logbit
                               rp-evlt-of-ex-from-rp
                               M2-PLUS-F2-OF-THE-SAME-ARGUMENT
                               F2-OF-1
                               (:DEFINITION VALID-SC)
                               (:REWRITE DEFAULT-CDR)
                               (:DEFINITION EVAL-AND-ALL)
                               (:REWRITE VALID-SC-EX-FROM-RP-2)
                               (:DEFINITION PP-TERM-P-FN)
                               (:REWRITE PP-TERM-P-IS-BITP-STRICT=NIL)
                               (:TYPE-PRESCRIPTION PP-TERM-P-FN)
                               (:REWRITE DEFAULT-CAR)
                               rp-trans)))))

  (defret break-down-two-arg-c-is-correct2
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (valid-sc c-in a))
             (equal (*
                     (and-list 0 (rp-evlt-lst e-lst a))
                     (ifix (rp-evlt res-c a)))
                    (ifix (rp-evlt c-in a))))
    :fn break-down-two-arg-c
    :hints (("Goal"
             :use ((:instance break-down-two-arg-c-is-correct))
             :in-theory (e/d (and-times-list) ()))))
  )

(local
 (defthm and-times-list-of-merge-sorted-and$-lists
   (equal (AND-TIMES-LIST
           0
           (RP-EVLT-LST (MERGE-SORTED-AND$-LISTS lst1 lst2) a)
           other)
          (* (and-list 0 (rp-evlt-lst lst1 a))
             (AND-TIMES-LIST 0 (RP-EVLT-LST lst2 a)
                             other)))
   :hints (("Goal"
            :in-theory (e/d (and$ AND-TIMES-LIST) ())))))

(local
 (defthm and-times-list-of-SORT-AND$-LIST
   (equal (AND-TIMES-LIST
           0
           (RP-EVLT-LST (SORT-AND$-LIST lst len) a)
           other)
          (AND-TIMES-LIST
           0
           (RP-EVLT-LST lst a)
           other))
   :hints (("Goal"
            :in-theory (e/d (and$ AND-TIMES-LIST) ())))))

(defret c-pattern4-compress-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                valid)
           (equal (sum-list-eval res-pp-lst a)
                  (rp-evlt `(c '0
                               ,(create-list-instance s-lst)
                               ,(create-list-instance pp-lst)
                               ,(create-list-instance c-lst))
                           a)))
  :fn c-pattern4-compress
  :hints (("Goal"
           :in-theory (e/d ((:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                            (:REWRITE
                             REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS)
                            not*
                            c-pattern4-compress)
                           (rp-trans)))))

;; (defun common-e-lst-inv-valid-pp-lst (pp-lst)
;;   (if (atom pp-lst)
;;       t
;;     (and
;;      (b* (;;((when (equal (car pp-lst) ''1)) t)
;;           ((mv & valid)
;;            (let* ((e (car pp-lst)))
;;              (case-match e
;;                (('and-list & ('list . x))
;;                 (mv x t))
;;                (('and-times-list & ('list . x) &)
;;                 (mv x t))
;;                (('logbit$inline & &)
;;                 (mv (list e) t))
;;                (& (mv nil nil))))))
;;        valid)
;;      (common-e-lst-inv-valid-pp-lst (cdr pp-lst)))))

;; (defun common-e-lst-inv (commons pp-lst)
;;   (if (atom pp-lst)
;;       t
;;     (and
;;      (or ;;(equal (car pp-lst) ''1)
;;          (b* (((mv lst &)
;;                (let* ((e (car pp-lst)))
;;                  (case-match e
;;                    (('and-list & ('list . x))
;;                     (mv x t))
;;                    (('and-times-list & ('list . x) &)
;;                     (mv x t))
;;                    (('logbit$inline & &)
;;                     (mv (list e) t))
;;                    (& (mv nil nil))))))
;;            (subsetp-equal commons lst)))
;;      (common-e-lst-inv commons (cdr pp-lst)))))

;; (defthm subsetp-equal-and-intersection-equal-lemma
;;   (SUBSETP-EQUAL (INTERSECTION-EQUAL y x) x)
;;   :hints (("Goal"
;;            ;;:induct (cdr-cdr-induct x y)
;;            :in-theory (e/d () ()))))

;; (defthm SUBSETP-EQUAL-and-INTERSECTION-EQUAL-lemma2
;;   (SUBSETP-EQUAL (INTERSECTION-EQUAL x y) x)
;;   :hints (("Goal"
;;            ;;:induct (cdr-cdr-induct x y)
;;            :in-theory (e/d () ()))))

;; (defthm COMMON-E-LST-INV-lemma
;;   (implies (and (COMMON-E-LST-INV x y)
;;                 (subsetp-equal other x))
;;            (COMMON-E-LST-INV other y)))

;; (defret collect-common-e-lst-correct-lemma
;;   (common-e-lst-inv commons pp-lst)
;;   :fn collect-common-e-lst
;;   :hints (("Goal"
;;            :in-theory (e/d (collect-common-e-lst) ()))))

;; (skip-proofs
;;  (local
;;  (defthmd weird-subset-p-equal-and-member-equal-lemma
;;    (implies (and (subsetp-equal to-remove-e-lst (list x))
;;                  (member-equal x to-remove-e-lst))
;;             (equal (AND-LIST 0 (RP-EVLT-LST TO-REMOVE-E-LST A))
;;                    (AND-LIST 0 (list (RP-EVLT X A)))))
;;    :hints (("Goal"
;;             ;; :do-not-induct t
;;             :induct (len TO-REMOVE-E-LST)
;;             ;; :induct (member-equal x to-remove-e-lst)
;;             :in-theory (e/d (member-equal)
;;                             ()))))))

;; ;; (local
;; ;;  (defthm common-e-lst-inv-valid-pp-lst-lemma-for-and-lit
;; ;;    (implies (and (common-e-lst-inv-valid-pp-lst pp-lst)
;; ;;                  (rp-evl-meta-extract-global-facts :state state)
;; ;;                  (mult-formula-checks state)
;; ;;                  (valid-sc-subterms pp-lst a))
;; ;;             (equal (AND-LIST 0 (LIST (RP-EVLt (CAR PP-LST) A)))
;; ;;                    (IFIX (RP-EVLt (CAR PP-LST) A))))
;; ;;    :hints (("Goal"
;; ;;             :expand ((COMMON-E-LST-INV-VALID-PP-LST PP-LST))
;; ;;             :do-not-induct t
;; ;;             :in-theory (e/d* (AND-LIST
;; ;;                               AND$
;; ;;                               regular-eval-lemmas-with-ex-from-rp
;; ;;                               regular-eval-lemmas)
;; ;;                              (rp-trans))))))

;; (defthm and-list-evval-of-SET-DIFFERENCE-EQUAL
;;   (implies (and (SUBSETP-EQUAL small big)
;;                 (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state))
;;            (equal (* (and-list 0 (rp-evlt-lst small a))
;;                      (and-list 0 (rp-evlt (set-difference-equal big small) a)))
;;                   (and-list 0 (rp-evlt-lst big a)))))

;; (defret remove-e-lst-from-pp-lst-correct
;;   (implies (and (common-e-lst-inv to-remove-e-lst pp-lst)
;;                 (common-e-lst-inv-valid-pp-lst pp-lst)
;;                 (rp-evl-meta-extract-global-facts :state state)
;;                 (mult-formula-checks state)
;;                 (valid-sc-subterms pp-lst a))
;;            (equal (and-times-list
;;                    hash
;;                    (rp-evlt-lst to-remove-e-lst a)
;;                    (sum (sum-list-eval s-lst a)
;;                         (sum-list-eval res-pp-lst a)
;;                         (sum-list-eval c-lst a)))
;;                   (sum-list-eval pp-lst a)))
;;   :fn remove-e-lst-from-pp-lst
;;   :hints (("Goal"
;;            :expand ((COMMON-E-LST-INV-VALID-PP-LST PP-LST))
;;            :in-theory (e/d (AND-TIMES-LIST
;;                             weird-subset-p-equal-and-member-equal-lemma
;;                             sum
;;                             remove-e-lst-from-pp-lst)
;;                            (rp-trans
;;                             SET-DIFFERENCE-EQUAL
;;                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
;;                             COMMON-E-LST-INV-VALID-PP-LST
;;                             +-IS-SUM)))))

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
                (valid-sc-subterms c-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
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
                             (:DEFINITION INCLUDE-FNC-SUBTERMS-FN)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             (:TYPE-PRESCRIPTION INCLUDE-FNC-FN)
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
                             INCLUDE-FNC-FN
                             RP-TRANS-LST
                             VALID-SC

                             )))))

(defret create-c-instance-is-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
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
                             ;;                             (:REWRITE ACL2::O-P-O-INFP-CAR)
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
                             INCLUDE-FNC-FN
                             RP-TRANS-LST
                             VALID-SC

                             )))))

(defret create-c-instance-is-correct-with-rest
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (rp-term-listp s-lst)
                (rp-term-listp pp-lst)
                (rp-term-listp c-lst))
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
               (valid-sc-subterms c-lst a)
               (rp-term-listp s-lst)
               (rp-term-listp pp-lst)
               (rp-term-listp c-lst))
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

(defthm m2-sums-dummy-lemma-2
  (equal (equal (m2 (sum x y a))
                (m2 (sum k l a m)))
         (equal (m2 (sum x y))
                (m2 (sum k l m)))))

(defthmd m2-chain-val-when-m2-is-known
  (implies (and (equal (m2 x) val))
           (and (equal (m2-chain x y)
                       (m2-chain val y))
                (equal (m2-chain y x)
                       (m2-chain val y)))))

(defthm m2-sums-dummy-lemma-3
  (implies (and (equal (m2 (sum za1 za2))
                       (m2 (sum zb1 zb2 zb3)))
                (equal (m2 x)
                       (m2 y)))
           (equal (equal (m2 (sum za1 za2 x))
                         (m2 (sum zb1 zb2 y zb3)))
                  t))
  :hints (("Goal"
           :use ((:instance m2-chain-val-when-m2-is-known
                            (val (m2 y))
                            (y za2)))
           :in-theory (e/d (m2-to-m2-chain bitp)
                           (BITP-M2)))))

(defthm rp-evlt-of-ex-from-rp-when-quoted
  (implies (equal (car x) 'quote)
           (equal (rp-evlt (ex-from-rp x) a)
                  (cadr x))))

(defret pp-sum-merge-lst-for-s-correct-with-m2-chain
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2-chain (sum-list-eval merged-pp-lst a) other)
                       (m2-chain (sum (sum-list-eval pp1-lst a)
                                      (sum-list-eval pp2-lst a))
                                 other))
                (equal (m2-chain other (sum-list-eval merged-pp-lst a))
                       (m2-chain (sum (sum-list-eval pp1-lst a)
                                      (sum-list-eval pp2-lst a))
                                 other))))
  :fn pp-sum-merge-lst-for-s
  :hints (("Goal"
           :use ((:instance pp-sum-merge-lst-for-s-correct))
           :do-not-induct t
           :expand (M2-CHAIN (SUM-LIST-EVAL PP1-LST A)
                             (SUM-LIST-EVAL PP2-LST A))
           :in-theory (e/d () (pp-sum-merge-lst-for-s-correct)
                           ))))

(defret s-of-s-fix-lst-correct
  (and
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (m2 (sum (sum-list-eval pp-res-lst a)
                            (sum-list-eval c-res-lst a)))
                   (m2 (sum (sum-list-eval s-lst a)
                            (sum-list-eval pp-lst a)
                            (sum-list-eval c-lst a))))))
  :fn s-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (s-of-s-fix-lst s-lst pp-lst c-lst)
           :expand ((:free (x y) (sum-list-eval (cons x y) a))
                    (SUM-LIST-EVAL S-LST A)
                    (:free (x) (nth 3 x))
                    (:free (x) (nth 2 x))
                    (:free (x) (nth 1 x))
                    (:free (x) (nth 0 x)))
           :in-theory (e/d* (s-of-s-fix-lst

                             m2-to-m2-chain
                             
                             (:REWRITE
                              REGULAR-RP-EVL-OF_S_WHEN_MULT-FORMULA-CHECKS)
                             (:REWRITE REGULAR-RP-EVL-OF_times_WHEN_MULT-FORMULA-CHECKS)
                             is-rp
                             get-pp-and-coef
                             rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             )
                            ((:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             (:REWRITE
                              GET-PP-AND-COEF-CORRECT-WHEN-COEF-IS-0)
                             (:REWRITE WHEN-M2-OF-AN-M2-ARG-IS-ZERO)

                             (:REWRITE MINUS-OF-SUM)
                             (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                             (:DEFINITION SUM-LIST-EVAL)
                             (:REWRITE
                              GET-PP-AND-COEF-CORRECT-WHEN-RES-TERM-IS-0)
                             rp-evlt-of-ex-from-rp
                             m2-of-times-when-odd-2
                             eval-and-all
                             evenp
                             rp-trans
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                             not-include-rp-means-valid-sc
                             not-include-rp-means-valid-sc-lst)))
          (and stable-under-simplificationp
               '(:use ((:instance m2-of-times-when-even-2
                                  (coef (ifix (CADR (CADR (CAR S-LST)))))
                                  (term (RP-EVLT (CADDR (CAR S-LST)) A))
                                  (other 0))
                       (:instance m2-of-times-when-odd-2
                                  (coef (ifix (CADR (CADR (CAR S-LST)))))
                                  (term (RP-EVLT (CADDR (CAR S-LST)) A))
                                  (other (sum (SUM-LIST-EVAL C-LST A)
                                              (SUM-LIST-EVAL PP-LST A)
                                              (SUM-LIST-EVAL (CDR S-LST) A))))
                       )))))

(defret s-of-s-fix-lst-correct-valid-sc-subterms
  (implies (and (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)) ;
           (and (valid-sc-subterms pp-res-lst a) ;
                (valid-sc-subterms c-res-lst a)))
  :fn s-of-s-fix-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (s-of-s-fix-lst s-lst pp-lst c-lst)
           :expand ((:free (x) (nth 3 x))
                    (:free (x) (nth 2 x))
                    (:free (x) (nth 1 x))
                    (:free (x) (nth 0 x)))
           :in-theory (e/d (s-of-s-fix-lst
                            is-rp)
                           (eval-and-all
                            rp-trans
                            RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                            not-include-rp-means-valid-sc
                            not-include-rp-means-valid-sc-lst)))))

(defthm m2-sums-dummy-lemma-6
  (implies (and (equal (m2 (sum x y)) (m2 (sum m n))))
           (equal (equal (m2 (sum x y a))
                         (m2 (sum m a n)))
                  t))
  :hints (("Goal"
           :in-theory (e/d ( )
                           (m2-sums-equivalence)))))

(defthm s-of-s-fix-correct-lemma
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (NOT (LIST-TO-LST S))
                (mult-formula-checks state))
           (equal (SUM-LIST (RP-EVLT S A))
                  0))
  :hints (("Goal"
           :in-theory (e/d (LIST-TO-LST) ()))))

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

(defthm sum-list-eval-of-append
  (equal (sum-list-eval (append x y) a)
         (sum (sum-list-eval x a)
              (sum-list-eval y a)))
  :hints (("Goal"
           :in-theory (e/d (sum-list-eval) ()))))

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

(defthmd rp-term-listp-implies-true-listp
  (implies (rp-term-listp lst)
           (true-listp lst)))

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
  :hints (("goal" :in-theory (e/d (sum -- ifix) (+-is-sum)))))

(defthmd
  m2-plus-f2-of-the-same-argument-reverse
  (and (equal (f2 (sum 1 x))
              (sum (m2 x) (f2 x)))
       (equal (f2 (sum x y z 1))
              (sum (m2 (sum x y z)) (f2 (sum x y z)))))
  :hints
  (("goal"
    :in-theory (e/d ()
                    ()))))

;; (defthm sum-of-m2-f2-f2-of-the-same-argument
;;   (and (equal (sum (m2 x) (f2 x) (f2 x))
;;               (ifix x))
;;        (equal (sum (-- (m2 x)) (-- (f2 x)) (-- (f2 x)))
;;               (-- x)))
;;   :hints (("Goal"
;;            :in-theory (e/d (m2 f2 sum rw-dir2
;;                                -- ifix
;;                                (:REWRITE ACL2::|(* a (/ a) b)|)
;;                                (:REWRITE ACL2::|(* x (+ y z))|)
;;                                (:REWRITE ACL2::|(* x (- y))|)
;;                                (:REWRITE ACL2::|(+ (if a b c) x)|)
;;                                (:REWRITE ACL2::|(+ 0 x)|)
;;                                (:REWRITE ACL2::|(+ c (+ d x))|)
;;                                (:REWRITE ACL2::|(+ x x)|)
;;                                (:REWRITE ACL2::|(- (* c x))|)
;;                                (:REWRITE ACL2::|(- (+ x y))|)
;;                                (:REWRITE ACL2::|(- (- x))|)
;;                                (:REWRITE ACL2::|(- (if a b c))|)
;;                                (:REWRITE ACL2::|(equal (- x) (- y))|)
;;                                (:REWRITE ACL2::|(equal (if a b c) x)|)
;;                                (:REWRITE ACL2::|(floor x 2)| . 1)
;;                                (:REWRITE ACL2::|(mod x 2)| . 1)
;;                                (:REWRITE ACL2::BUBBLE-DOWN-+-MATCH-1)
;;                                (:REWRITE ACL2::EVEN-AND-ODD-ALTERNATE)
;;                                (:REWRITE IFIX-OPENER)
;;                                (:REWRITE ACL2::INTEGERP-+-REDUCE-CONSTANT)
;;                                (:REWRITE ACL2::NORMALIZE-ADDENDS))
;;                            (+-is-sum
;;                             rw-dir1
;;                             (:DEFINITION FLOOR)
;;                             (:REWRITE MOD2-IS-M2)
;;                             floor2-if-f2)))))

(defret create-s-instance-correct-singled-out
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc pp a)
                (valid-sc c a)
                (rp-termp pp)
                (rp-termp c))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-sum-merge

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; c-of-s-fix-lst

(defret APPEND-WITH-TIMES-AUX-valid-sc
  (implies (and (valid-sc-subterms term-lst a)
                (valid-sc-subterms rest a))
           (valid-sc-subterms res-lst a))
  :fn APPEND-WITH-TIMES-AUX
  :hints (("Goal"
           :in-theory (e/d (APPEND-WITH-TIMES-AUX) ()))))

(defret valid-sc-subterms-of-APPEND-WITH-TIMES
  (implies (and (valid-sc-subterms term-lst a)
                (valid-sc-subterms rest a))
           (valid-sc-subterms res-lst a))
  :fn append-with-times
  :hints (("Goal"
           :in-theory (e/d (append-with-times) ()))))

(defret c-of-s-fix-lst-valid-sc
  (implies (and ;;(c-of-s-fix-mode)
            (valid-sc-subterms arg-s-lst a)
            (valid-sc-subterms arg-pp-lst a)
            (valid-sc-subterms arg-c-lst a)
            (valid-sc-subterms to-be-coughed-c-lst a)
            (MULT-FORMULA-CHECKS STATE)
            (rp-evl-meta-extract-global-facts :state state)

            (rp-term-listp arg-s-lst)
            )
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
                           (evenp
                            (:DEFINITION VALID-SC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE DEFAULT-CAR)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:DEFINITION INCLUDE-FNC-SUBTERMS-FN)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS-FN)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-FN)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION MULT-FORMULA-CHECKS)
                            (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION IS-RP$INLINE)
                            (:DEFINITION INCLUDE-FNC-FN))))))

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
             :in-theory (e/d (m2 f2 -- sum rw-dir2 ifix)
                             (mod2-is-m2
                              rw-dir1
                              +-IS-SUM
                              floor2-if-f2)))))

  )

(defthmd times-of-sum
  (equal (times coef (sum x y))
         (sum (times coef x)
              (times coef y)))
  :hints (("Goal"
           :in-theory (e/d (sum times)
                           (+-IS-SUM)))))

(defret append-with-times-aux-correct
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state)
                )
           (equal (sum-list-eval res-lst a)
                  (sum (sum-list-eval rest a)
                       (times coef
                              (sum-list-eval term-lst a)))))
  :fn append-with-times-aux
  :hints (("Goal"
           :in-theory (e/d (times-of-sum
                            append-with-times-aux) ()))))

(defret append-with-times-correct
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state)
                )
           (equal (sum-list-eval res-lst a)
                  (sum (sum-list-eval rest a)
                       (times coef
                              (sum-list-eval term-lst a)))))
  :fn append-with-times
  :hints (("Goal"
           :in-theory (e/d (append-with-times) ()))))

(defret c-of-s-fix-lst-correct-lemma
  (implies (and ;;(c-of-s-fix-mode)
            (valid-sc-subterms arg-s-lst a)
            (valid-sc-subterms arg-pp-lst a)
            (valid-sc-subterms arg-c-lst a)
            (valid-sc-subterms to-be-coughed-c-lst a)
            (MULT-FORMULA-CHECKS STATE)
            (rp-evl-meta-extract-global-facts :state state)

            (rp-term-listp arg-s-lst))
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
           :expand ((:free (x y) (sum-list-eval (cons x y) a))
                    (rp-trans (CADR (CAR ARG-S-LST)))
                    (SUM-LIST-EVAL NIL A)
                    (SUM-LIST-EVAL ARG-S-LST A))
           :in-theory (e/d* (;;sum-of-repeated-to-times
                             times-of-sum-reverse
                             divide-by-2-is-floor2-when-even

                             
                             
                             GET-PP-AND-COEF
                             -to---
                             c-of-s-fix-lst
                             (:rewrite regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp)
                             regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_--_when_mult-formula-checks
                             regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_times_when_mult-formula-checks
                             sum-of-two-negated-f2s
                             ;;regular-eval-lemmas
                             when-ex-from-rp-is-0
                             d2-of-repeated
                             rw-dir2)
                            (TIMES-OF-SUMMED-COEF
                             rw-dir1
                             F2-OF-1
                             sum-list-eval
                             (:rewrite get-pp-and-coef-correct-when-coef-is-0)
                             (:rewrite get-pp-and-coef-correct-when-res-term-is-0)
                             (:rewrite valid-sc-subterms-of-cdr)
                             (:meta binary-or**/and**-guard-meta-correct)
                             floor
                             evenp
                             ;;(:e --)
                             (:definition valid-sc)
                             rp-trans
                             (:rewrite sum-of-negated-elements)
                             (:rewrite dummy-sum-cancel-lemma1)
                             (:type-prescription binary-sum)
                             (:type-prescription --)
                             (:rewrite valid-sc-subterms-cdr)
                             (:type-prescription include-fnc-fn)
                             (:type-prescription valid-sc)
                             (:type-prescription valid-sc-subterms)
                             (:type-prescription include-fnc-subterms-fn)
                             (:definition include-fnc-subterms-fn)
                             (:rewrite not-include-rp-means-valid-sc-lst)
                             (:rewrite ex-from-synp-lemma1)
                             (:rewrite rp-evl-of-variable)
                             (:rewrite not-include-rp-means-valid-sc)
                             (:rewrite default-car)
                             (:definition eval-and-all)
                             (:rewrite valid-sc-when-list-instance)
                             (:rewrite default-cdr)
                             (:definition is-rp$inline)
                             (:definition include-fnc-fn))))))

(defret c-of-s-fix-lst-correct-singled-out
  (implies (and ;;(c-of-s-fix-mode)
            (valid-sc-subterms arg-s-lst a)
            (valid-sc-subterms arg-pp-lst a)
            (valid-sc-subterms arg-c-lst a)
            (valid-sc-subterms to-be-coughed-c-lst a)
            (MULT-FORMULA-CHECKS STATE)
            (rp-evl-meta-extract-global-facts :state state)
            (rp-term-listp arg-s-lst))
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
                            ((:e --)
                             c-of-s-fix-lst-correct-lemma)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-of-s-fix

;;;;;;;

;;;

(defthm equivalence-of-two-m2s-with-the-same-var-1
  (implies (and (equal (m2-chain x y) (m2-chain p q)))
           (equal (equal (m2-chain x y a)
                         (m2-chain p a q))
                  t)))

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
           :do-not '(preprocess)
           :in-theory (e/d (m2-chain)
                           (M2-CHAIN-OF-M2)))))

(defthm m2-chain-of-m2
  (and (equal (m2-chain (m2 x) y)
              (m2-chain x y))
       (equal (m2-chain y (m2 x))
              (m2-chain x y)))
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

(defthm ifix-of-m2-chain
  (equal (ifix (m2-chain x y))
         (m2-chain x y))
  :hints (("Goal"
           :in-theory (e/d (m2-chain) ()))))



(defret sum-merge-lst-for-s-correct-with-m2-chain
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2-chain (sum-list-eval merged-s-lst a) other)
                       (m2-chain (sum (sum-list-eval s1-lst a)
                                      (sum-list-eval s2-lst a))
                                 other))
                (equal (m2-chain other (sum-list-eval merged-s-lst a))
                       (m2-chain (sum (sum-list-eval s1-lst a)
                                      (sum-list-eval s2-lst a))
                                 other))))
  :fn sum-merge-lst-for-s
  :hints (("Goal"
           :use ((:instance sum-merge-lst-for-s-correct))
           :do-not-induct t
           :expand (M2-CHAIN (SUM-LIST-EVAL s1-LST A)
                             (SUM-LIST-EVAL s2-LST A))
           :in-theory (e/d () (sum-merge-lst-for-s-correct)
                           ))))



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

(defthmd rp-evlt-when-ex-from-rp-is-quoted
  (implies (quotep (ex-from-rp term))
           (equal (rp-evlt term a)
                  (cadr (ex-from-rp term))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
                           (EVL-OF-EXTRACT-FROM-RP
                            RP-TRANS-OF-QUOTED
                            rp-evlt-of-ex-from-rp
                            rp-trans)))))

(defthm EX-FROM-RP-when-quoted
  (implies (equal (car x) 'quote)
           (equal (ex-from-rp x) x))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (is-rp ex-from-rp) ()))))

(defthm times-of-1-2
  (and (equal (times 1 x)
              (ifix x))
       (equal (times x 1)
              (ifix x)))
  :hints (("Goal"
           :in-theory (e/d (times) ()))))

(in-theory (disable SUM-OF-NEGATED-ELEMENTS))

(local
 (defthm ex-from-rp-of-coef-when-times-p
   (implies (times-p term)
            (equal (EX-FROM-RP (CADR TERM))
                   (cadr term)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (times-p) ())))))
   

(defret extract-new-sum-element-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval acc-res a)
                  (sum (rp-evlt term a)
                       (sum-list-eval acc a))))
  :fn extract-new-sum-element
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-new-sum-element term acc :limit limit)
           :expand ((extract-new-sum-element term acc)
                    (:free (x y) (sum-list-eval (cons x y) a)))
           :in-theory (e/d* (TIMES-OF-SUM
                             -to---
                             ;;times-p
                             *-is-times
                             rp-evlt-when-ex-from-rp-is-quoted
                             get-pp-and-coef
                             extract-new-sum-element
                             rp-evlt-when-quotep
                             regular-eval-lemmas-with-ex-from-rp
                             rp-evlt-of-ex-from-rp-reverse-only-atom
                             rw-dir2)
                            ((:e --)
                             sum-list-eval
                             (:REWRITE DEFAULT-CAR)

                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION PP-TERM-P-FN)
                             (:REWRITE
                              GET-PP-AND-COEF-CORRECT-WHEN-RES-TERM-IS-0)
                             (:REWRITE PP-TERMP-OF-EX-FROM-RP)

                             rw-dir1
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

(encapsulate
  nil
  (local
   (use-arith-5 t))
  (defthm bitp-of-loghead-1
    (bitp (loghead 1 x))))

(defthm svl::bitp-of-bits
  (implies (and (integerp (svl::bits x start 1)))
           (bitp (svl::bits x start 1)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (SV::4VEC-PART-SELECT
                            SV::4VEC-ZERO-EXT
                            SV::4VEC->LOWER

                            SV::2VEC
                            SV::4VEC-CONCAT
                            SV::4VEC->UPPER
                            SV::4VEC
                            svl::bits
                            )
                           (+-IS-SUM
                            logapp loghead )))))

(defthmd has-integerp-rp-implies
  (implies (and (has-integerp-rp x)
                (valid-sc x a))
           (integerp (rp-evlt x a)))
  :hints (("Goal"
           :in-theory (e/d (valid-sc-single-step
                            has-integerp-rp)
                           ()))))

(defthmd is-bitp-svl-bits-implies-bitp
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (is-bitp-svl-bits term))
           (and (VALID-SC (LIST 'RP ''BITP TERM) A)
                (bitp (rp-evlt term a))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance has-integerp-rp-implies
                            (x term)))
           :in-theory (e/d* (is-bitp-svl-bits
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             valid-sc-single-step)
                            (has-integerp-rp-implies)))))

(defret extract-new-sum-element-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (valid-sc-subterms acc a))
           (valid-sc-subterms acc-res a))
  :fn extract-new-sum-element
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-new-sum-element term acc :limit limit)
           :in-theory (e/d (is-bitp-svl-bits-implies-bitp
                            extract-new-sum-element
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
  :hints (("goal"
           :do-not-induct t
           :expand (extract-new-sum-consed term)
           :induct (extract-new-sum-consed term)
           :in-theory (e/d* (regular-eval-lemmas
                             extract-new-sum-consed
                             rp-evlt-of-ex-from-rp-reverse-only-atom)
                            (rp-evlt-of-ex-from-rp
                             rp-trans
                             rp-trans-is-term-when-list-is-absent
                             evl-of-extract-from-rp)))))

(defret extract-new-sum-consed-correct-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a))
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
              (and$ a))
       (equal (and$ a b a)
              (and$ a b)))
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

(defthm equal-of-times-with-same-coef
  (implies (equal (ifix x)
                  (ifix y))
           (equal (equal (times coef x)
                         (times coef y))
                  t))
  :hints (("Goal"
           :in-theory (e/d (times) ()))))

(progn
  (local
   (use-arith-5 t))
  (defthmd send-neg-of-times-to-second-term
    (equal (- (times coef x))
           (times coef (- x)))
    :hints (("Goal"
             :in-theory (e/d (times ifix) ()))))

  (defthmd unary--of-sum
    (equal (- (sum x y))
           (sum (-- x) (-- y)))
    :hints (("Goal"
             :in-theory (e/d (sum -- ifix)
                             (+-IS-SUM)))))
  (local
   (use-arith-5 nil)))

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
  :hints (("goal"
           :expand ((:free (x y) (sum-list-eval (cons x y) a)))
           :in-theory (e/d* (;;times-of-sum
                             times-of-sum-reverse
                             unary--of-sum
                             send-neg-of-times-to-second-term
                             recollect-pp
                             rp-trans-when-list
                             get-pp-and-coef
                             and-list
                             recollect-pp-correct-lemma2
                             recollect-pp-correct-lemma1
                             ;;recollectable-pp-p
                             rp-evlt-when-quotep
                             regular-rp-evl-of_times_when_mult-formula-checks
                             (:rewrite regular-rp-evl-of_--_when_mult-formula-checks)
                             (:rewrite
                              regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_cons_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite regular-rp-evl-of_c_when_mult-formula-checks)
                             rp-evlt-of-ex-from-rp-reverse-only-atom
                             rw-dir2
                             )
                            (rp-trans
                             RP-TRANS-LST
                             trans-list
                             rw-dir1
                             SUM-LIST-EVAL
                             (:DEFINITION VALID-SC)
                             ;;eval-and-all
                             rp-trans
                             not-include-rp-means-valid-sc-lst
                             rp-trans-is-term-when-list-is-absent
                             rp-evlt-of-ex-from-rp
                             )))))


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

                             regular-rp-evl-of_c_when_mult-formula-checks
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cross-product-pp

(defret extract-first-arg-of-equals-valid-sc
  (implies (valid-sc term a)
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (rp-evlt term a))))
  :fn EXTRACT-FIRST-ARG-OF-EQUALS
  :hints (("Goal"
           :in-theory (e/d (EXTRACT-FIRST-ARG-OF-EQUALS) ()))))

(defret cross-product-pp-aux-precollect-valid-sc
  (implies (valid-sc-subterms e-lst a)
           (and (valid-sc-subterms single-s/c-lst a)
                (valid-sc-subterms res-e-lst a)))
  :fn cross-product-pp-aux-precollect
  :hints (("Goal"
           :in-theory (e/d (cross-product-pp-aux-precollect
                            is-rp
                            is-if)
                           ((:DEFINITION EVAL-AND-ALL)
                            (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION RP-TRANS)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2))))))

(defret cross-product-pp-aux-precollect2-aux-valid-sc
  (implies (and (valid-sc-subterms side-pp-lst a)
                (valid-sc single-pp a))
           (valid-sc-subterms res-side-pp-lst a))
  :fn cross-product-pp-aux-precollect2-aux
  :hints (("Goal"
           :in-theory (e/d (cross-product-pp-aux-precollect2-aux
                            is-rp
                            is-if)
                           ((:DEFINITION EVAL-AND-ALL)
                            (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION RP-TRANS)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2))))))

(defret cross-product-pp-aux-precollect2-valid-sc
  (implies (valid-sc single-pp a)
           (and (valid-sc single-s/c a)
                (valid-sc res-pp a)
                (valid-sc-subterms side-pp-lst a)))
  :fn cross-product-pp-aux-precollect2
  :hints (("Goal"
           :expand ((:free (x y) (valid-sc (cons x y) a)))
           :in-theory (e/d (cross-product-pp-aux-precollect2
                            is-rp
                            is-if)
                           (VALID-SC-SUBTERMS-CONS
                            VALID-SC
                            (:REWRITE VALID-SC-EX-FROM-RP)
                            (:DEFINITION EVAL-AND-ALL)
                            rp-equal
                            (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION RP-TRANS)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2))))))

(define and-eval-for-cross-product-pp (single-s/c e-lst a)
  (if (equal (and-list 0 (rp-evlt-lst e-lst a)) 1)
      (rp-evlt single-s/c a)
    0))

(define and-eval-for-cross-product-lst-pp (single-s/c-lst e-lst a)
  (if (equal (and-list 0 (rp-evlt-lst e-lst a)) 1)
      (and-list 0 (rp-evlt-lst single-s/c-lst a))
    0))

(define and-eval-for-cross-product-pp-lst (single-s/c pp-lst a)
  :verify-guards nil
  (if (equal (rp-evlt single-s/c a) 1)
      (sum-list-eval pp-lst a) ;
    0)
  #|(if (atom pp-lst)
  0
  (sum (if (equal (rp-evlt (car pp-lst) a) 1) (rp-evlt single-s/c a) 0)
  (and-eval-for-cross-product-pp-lst single-s/c (cdr pp-lst) a)))|#)

(defthm and-list-cons-redef
  (equal (and-list hash (cons x y))
         (and$ x (and-list 0 y)))
  :hints (("Goal"
           :in-theory (e/d (and-list) ()))))

(defthm and$-of-0/1
  (and (equal (and$ 0 x) 0)
       (equal (and$ 1 x) (bit-fix x)))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

#|(defthmd and-eval-for-cross-product-pp-redef
(equal (and-eval-for-cross-product-pp single-s/c e-lst a)
(and$ (rp-evlt single-s/c a)
(and-list hash (rp-evlt-lst e-lst a))))
:hints (("Goal"
:in-theory (e/d (and-eval-for-cross-product-pp) ()))))|#

(local
 (defthmd when-of-known-value
   (implies (and (equal (bit-fix x) val)
                 (bitp other))
            (equal (and$ x other)
                   (if (equal val 1)
                       other
                     0)))
   :hints (("Goal"
            :in-theory (e/d (and$) ())))))

(defret cross-product-pp-aux-precollect-correct
  (implies (and (force (valid-sc-subterms e-lst a))
                valid
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (and-eval-for-cross-product-lst-pp
                        single-s/c-lst res-e-lst a)
                       (and-list hash (rp-evlt-lst e-lst a)))
                #|(implies (equal (len single-s/c-lst) 1)
                (equal (and-eval-for-cross-product-pp
                (car single-s/c-lst) res-e-lst a)
                (and-list hash (rp-evlt-lst e-lst a))))|#
                (bit-listp (rp-evlt-lst single-s/c-lst a))))
  :fn cross-product-pp-aux-precollect
  :hints (("Goal"
           ;;:expand ((:free (x y) (and-list 0 (cons x y))))
           :expand ((EXTRACT-FIRST-ARG-OF-EQUALS (EX-FROM-RP (CAR E-LST))))
           :in-theory (e/d* (bit-listp

                             has-bitp-rp-force-hyp-rewrite

                             ;;EXTRACT-FIRST-ARG-OF-EQUALS
                             when-of-known-value
                             regular-rp-evl-of_equals_when_mult-formula-checks
                             regular-rp-evl-of_s_when_mult-formula-checks
                             regular-rp-evl-of_logbit$inline_when_mult-formula-checks
                             and-eval-for-cross-product-pp;;-redef
                             and-eval-for-cross-product-lst-pp
                             cross-product-pp-aux-precollect
                             rp-evlt-of-ex-from-rp-reverse)
                            (rp-trans  
                             (:definition valid-sc)
                             (:rewrite valid-sc-subterms-cdr)
                             (:definition eval-and-all)
                             (:rewrite valid-sc-subterms-of-cdr)
                             (:rewrite
                              rp-trans-is-term-when-list-is-absent)
                             rp-evlt-of-ex-from-rp
                             rp-trans-lst)))
          ))

(local
 (defthm rp-evlt-ex-from-rp-with-binary-and
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (rp-evlt (ex-from-rp (list 'binary-and x y)) a)
                   (binary-and (rp-evlt x a)(rp-evlt y a))))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp is-rp) ())))))

(defret cross-product-pp-aux-precollect2-aux-correct
  (implies (and valid
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (bit-listp (rp-evlt-lst side-pp-lst a)))
           (and (equal (sum-list-eval res-side-pp-lst a)
                       (and-eval-for-cross-product-pp (list 'quote (sum-list-eval side-pp-lst a))
                                                      (list single-pp)
                                                      a))
                (bit-listp (rp-evlt-lst res-side-pp-lst a))))
  :fn cross-product-pp-aux-precollect2-aux
  :hints (("Goal"
           :in-theory (e/d* (regular-rp-evl-of_s_when_mult-formula-checks
                             regular-rp-evl-of_binary-and_when_mult-formula-checks
                             regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_logbit$inline_when_mult-formula-checks

                             and-eval-for-cross-product-pp;;-redef
                             cross-product-pp-aux-precollect2-aux
                             rp-evlt-of-ex-from-rp-reverse
                             and$
                             BIT-LISTP
                             bit-fix)
                            (rp-trans
                             ;;RP-TRANS-OPENER
                             (:definition valid-sc)
                             (:rewrite valid-sc-subterms-cdr)
                             (:definition eval-and-all)
                             (:rewrite valid-sc-subterms-of-cdr)
                             (:rewrite
                              rp-trans-is-term-when-list-is-absent)
                             rp-evlt-of-ex-from-rp
                             rp-trans-lst)))))

(local
 (defthmd BINARY-?-rw-to-sum
   (equal (binary-? x y z)
          (sum (and$ x y)
               (and$ (not$ x) z)))
   :hints (("Goal"
            :in-theory (e/d (binary-?
                             BIT-FIX
                             and$ not$)
                            ())))))

(DEFTHMd RP-EVLT-OF-EX-FROM-RP-REVERSE-with-EXTRACT-FIRST-ARG-OF-EQUALS
  (IMPLIES
   (AND (SYNTAXP (OR (ATOM TERM)
                     (AND (NOT (EQUAL (CAR TERM) 'EXTRACT-FIRST-ARG-OF-EQUALS))
                          (NOT (EQUAL (CAR TERM) 'EX-FROM-RP))
                          (NOT (EQUAL (CAR TERM) 'QUOTE)))))
        (valid-sc term a))
   (and
    (EQUAL (RP-EVL (RP-TRANS TERM) A)
           (RP-EVL (RP-TRANS (EXTRACT-FIRST-ARG-OF-EQUALS (EX-FROM-RP TERM)))
                   A))
    (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)
           (RP-EVL (RP-TRANS (EXTRACT-FIRST-ARG-OF-EQUALS (EX-FROM-RP TERM)))
                   A)))))

(DEFTHM EXTRACT-FIRST-ARG-OF-EQUALS-onlyVALID-SC
  (B* ((?RES (EXTRACT-FIRST-ARG-OF-EQUALS TERM)))
    (IMPLIES (VALID-SC TERM A)
             (AND (VALID-SC RES A))))
  :HINTS (("Goal" :IN-THEORY (E/D (EXTRACT-FIRST-ARG-OF-EQUALS)
                                  NIL))))

(defret cross-product-pp-aux-precollect2-correct
  (implies (and valid
                (valid-sc single-pp a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal
                 (sum (sum-list-eval side-pp-lst a)
                      (and-eval-for-cross-product-pp single-s/c (list res-pp) a))
                 (rp-evlt single-pp a))
                (equal
                 (sum (sum-list-eval side-pp-lst a)
                      (and-eval-for-cross-product-pp single-s/c (list res-pp) a)
                      other)
                 (sum (rp-evlt single-pp a) other))
                (equal
                 (sum (and-eval-for-cross-product-pp single-s/c (list res-pp) a)
                      (sum-list-eval side-pp-lst a))
                 (rp-evlt single-pp a))
                (equal
                 (sum (and-eval-for-cross-product-pp single-s/c (list res-pp) a)
                      (sum-list-eval side-pp-lst a)
                      other)
                 (sum (rp-evlt single-pp a) other))
                (bitp (rp-evlt single-pp a))
                (bit-listp (rp-evlt-lst side-pp-lst a))
                (bitp (rp-evlt single-s/c a))
                (bitp (rp-evlt res-pp a))))
  :fn cross-product-pp-aux-precollect2
  :hints (("Goal"
           :do-not-induct t
           :induct (cross-product-pp-aux-precollect2 SINGLE-PP)
           :expand ((:free (x y) (sum-list-eval (cons x y) a)))
           :in-theory (e/d* (bitp ;;EXTRACT-FIRST-ARG-OF-EQUALS
                             BINARY-?-rw-to-sum
                             regular-rp-evl-of_s_when_mult-formula-checks
                             regular-rp-evl-of_binary-and_when_mult-formula-checks
                             regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-?_when_mult-formula-checks
                             regular-rp-evl-of_binary-?_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-not_when_mult-formula-checks
                             regular-rp-evl-of_binary-not_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-xor_when_mult-formula-checks
                             regular-rp-evl-of_binary-xor_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-or_when_mult-formula-checks
                             regular-rp-evl-of_binary-or_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_logbit$inline_when_mult-formula-checks

                             and-eval-for-cross-product-pp;;-redef
                             cross-product-pp-aux-precollect2
                             RP-EVLT-OF-EX-FROM-RP-REVERSE
                             and$
                             BIT-LISTP
                             has-bitp-rp-force-hyp-rewrite
                             bit-fix)
                            (rp-trans
                             PP-TERM-P-IS-BITP-STRICT=NIL
                             pp-term-p
                             bitp floor logbit nfix
                             ;;sum-list-eval
                             ;;EXTRACT-FIRST-ARG-OF-EQUALS-VALID-SC
                             ;;RP-TRANS-OPENER
                             (:definition valid-sc)
                             (:rewrite valid-sc-subterms-cdr)
                             (:definition eval-and-all)
                             (:rewrite valid-sc-subterms-of-cdr)
                             (:rewrite
                              rp-trans-is-term-when-list-is-absent)
                             rp-evlt-of-ex-from-rp
                             rp-trans-lst)))))

(define sum-lst-and-eval-for-cross-product-pp (lst e-lst a)
  (if (atom lst)
      0
    (sum (and-eval-for-cross-product-pp (car lst) e-lst a)
         (sum-lst-and-eval-for-cross-product-pp (cdr lst) e-lst a))))

(defthm rp-evl-nil
  (equal (RP-EVL NIL A)
         nil))

(defthmd and-list-redef-consp
  (implies (consp x)
           (equal (and-list hash x)
                  (and$ (car x)
                        (and-list 0 (cdr x)))))
  :hints (("Goal"
           :in-theory (e/d (and-list) ()))))

(local
 (defthm and-list-of-merge-sorted-and$-lists-dummy-lemma1
   (implies (equal x (and$ a b))
            (equal (and$ a x) x))))

(defret and-list-of-merge-sorted-and$-lists
  (implies t
           (equal (and-list hash
                            (rp-evlt-lst res a))
                  (and$ (and-list 0 (rp-evlt-lst first a))
                        (and-list 0 (rp-evlt-lst second a)))))
  :fn merge-sorted-and$-lists
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (merge-sorted-and$-lists
                            and-list-redef-consp)
                           ()))))

(defthm binary-fnc-p-implies-bitp
  (implies (and (or (binary-fnc-p term)
                    (binary-fnc-p (ex-from-rp term)))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (bitp (rp-evlt term a))
                (bitp (rp-evlt (ex-from-rp term) a))
                (integerp (rp-evlt term a))
                (integerp (rp-evlt (ex-from-rp term) a))))
  :hints (("Goal"
           :in-theory (e/d* (regular-eval-lemmas
                             binary-fnc-p
                             regular-eval-lemmas-with-ex-from-rp)
                            ()))))

(defthm equal-with-zero-and-1-when-bitp
  (and (implies (and (bitp x)
                     (not (equal x 1)))
                (equal (equal x 0) t))
       (implies (and (bitp x)
                     (not (equal x 1)))
                (equal (equal (-- x) 0) t))
       (implies (and (bitp x)
                     (not (equal x 0)))
                (equal (equal x 1) t))))

(defthmd times-with-a-bitp
  (and (Implies (and (not (equal x 1))
                     (bitp x))
                (equal (times y x)
                       0))))

(defthmd rp-evlt-of-list-2
  (implies (equal (car x) 'list)
           (equal (rp-evlt x a)
                  (rp-evlt-lst (cdr x) a))))

(defret cross-product-pp-aux-for-pp-lst-aux-correct
  (implies (and valid
                (rp-evl-meta-extract-global-facts :state state)
                (valid-sc-subterms pp-lst a)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms e-lst a) )
           (equal (sum-list-eval res-pp-lst a)
                  (sum-lst-and-eval-for-cross-product-pp pp-lst e-lst a)))
  :fn cross-product-pp-aux-for-pp-lst-aux
  ;;:otf-flg t
  :hints (("goal"
           :induct (cross-product-pp-aux-for-pp-lst-aux pp-lst e-lst)
           :do-not-induct t
           :expand ((:free (x y) (sum-list-eval (cons x y) a))
                    (rp-trans (CADR (CAR PP-LST))))
           :in-theory (e/d
                       (;;binary-fnc-p
                        rp-evlt-of-list-2
                        GET-PP-AND-COEF
                        times-with-a-bitp
                        has-bitp-rp-force-hyp-rewrite

                        regular-rp-evl-of_binary-and_when_mult-formula-checks
                        regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_and-list_when_mult-formula-checks
                        regular-rp-evl-of_logbit$inline_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_logbit$inline_when_mult-formula-checks
                        regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_--_when_mult-formula-checks
                        regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_times_when_mult-formula-checks
                        cross-product-pp-aux-for-pp-lst-aux
                        and-eval-for-cross-product-pp;;-redef
                        sum-lst-and-eval-for-cross-product-pp
                        and$
                        )
                       (rp-trans

                        
                        DEFAULT-CDR
                        PP-TERM-P-FN
                        PP-TERM-P-IS-BITP-STRICT=NIL
                        GET-PP-AND-COEF-CORRECT-WHEN-RES-TERM-IS-0
                        
                        VALID-SC-SUBTERMS-CONS

                        LOGBIT$INLINE
                        floor
                        oddp nfix
                        sum-list-eval

                        ;;rp-trans-opener
                        rp-evl-of-lambda
                        rp-evl-of-variable
                        (:definition valid-sc)
                        (:rewrite valid-sc-subterms-cdr)
                        (:definition eval-and-all)
                        (:rewrite valid-sc-subterms-of-cdr)
                        (:rewrite
                         rp-trans-is-term-when-list-is-absent)
                        rp-evlt-of-ex-from-rp
                        rp-trans-lst)))))

(defret cross-product-pp-aux-for-pp-lst-correct
  (implies (and valid
                (rp-evl-meta-extract-global-facts :state state)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms e-lst a)
                (mult-formula-checks state))
           (equal (sum-list-eval res-pp-lst a)
                  (sum-lst-and-eval-for-cross-product-pp pp-lst e-lst a)))
  :fn cross-product-pp-aux-for-pp-lst
  ;;:otf-flg t
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d
                       (cross-product-pp-aux-for-pp-lst)
                       (rp-trans
                        ;;rp-trans-opener
                        rp-evl-of-lambda
                        rp-evl-of-variable
                        (:definition valid-sc)
                        (:rewrite valid-sc-subterms-cdr)
                        (:definition eval-and-all)
                        (:rewrite valid-sc-subterms-of-cdr)
                        (:rewrite
                         rp-trans-is-term-when-list-is-absent)
                        rp-evlt-of-ex-from-rp
                        rp-trans-lst)))))

(defthm valid-sc-of---
  (equal (valid-sc (list '-- x) a)
         (valid-sc x a)))

(defthm valid-sc-of-binary-and
  (equal (valid-sc (list 'binary-and x y) a)
         (and (valid-sc x a)
              (valid-sc y a)))
  :hints (("Goal"
           :in-theory (e/d (valid-sc is-rp is-if) ()))))

(defret cross-product-pp-aux-for-pp-lst-aux-valid-sc
  (implies (and (valid-sc-subterms pp-lst a)
                (valid-sc-subterms e-lst a))
           (valid-sc-subterms res-pp-lst a))
  :fn cross-product-pp-aux-for-pp-lst-aux
  ;;:otf-flg t
  :hints (("goal"
           :induct (cross-product-pp-aux-for-pp-lst-aux pp-lst e-lst)
           :do-not-induct t
           :in-theory (e/d
                       (regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_and-list_when_mult-formula-checks

                        cross-product-pp-aux-for-pp-lst-aux
                        and-eval-for-cross-product-pp;;-redef
                        )
                       (rp-trans
                        ;;rp-trans-opener
                        rp-evl-of-lambda
                        rp-evl-of-variable
                        (:definition valid-sc)
                        (:rewrite valid-sc-subterms-cdr)
                        (:definition eval-and-all)
                        (:rewrite valid-sc-subterms-of-cdr)
                        (:rewrite
                         rp-trans-is-term-when-list-is-absent)
                        rp-evlt-of-ex-from-rp
                        rp-trans-lst)))))

(defret cross-product-pp-aux-for-pp-lst-valid-sc
  (implies (and (valid-sc-subterms pp-lst a)
                (valid-sc-subterms e-lst a))
           (valid-sc-subterms res-pp-lst a))
  :fn cross-product-pp-aux-for-pp-lst
  ;;:otf-flg t
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d
                       (cross-product-pp-aux-for-pp-lst
                        ;;-redef
                        )
                       (rp-trans
                        ;;rp-trans-opener
                        rp-evl-of-lambda
                        rp-evl-of-variable
                        (:definition valid-sc)
                        (:rewrite valid-sc-subterms-cdr)
                        (:definition eval-and-all)
                        (:rewrite valid-sc-subterms-of-cdr)
                        (:rewrite
                         rp-trans-is-term-when-list-is-absent)
                        rp-evlt-of-ex-from-rp
                        rp-trans-lst)))))

(defret-mutual cross-product-pp-aux-for-s/c-valid-sc-subterms
  (defret cross-product-pp-aux-for-s/c-valid-sc-subterms
    (implies (and (valid-sc single-s/c a)
                  (valid-sc-subterms e-lst a)
                  (rp-termp single-s/c)
                  (rp-term-listp e-lst)
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (and (valid-sc-subterms res-s-lst a)
                  (valid-sc-subterms res-pp-lst a)
                  (valid-sc-subterms res-c-lst a)))
    :fn cross-product-pp-aux-for-s/c)

  (defret cross-product-pp-aux-for-s/c-lst-valid-sc-subterms
    (implies (and (valid-sc-subterms s/c-lst a)
                  (valid-sc-subterms e-lst a)
                  (rp-term-listp s/c-lst)
                  (rp-term-listp e-lst)
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (and (valid-sc-subterms res-s-lst a)
                  (valid-sc-subterms res-pp-lst a)
                  (valid-sc-subterms res-c-lst a)))
    :fn cross-product-pp-aux-for-s/c-lst)
  :mutual-recursion cross-product-pp-aux-for-s/c
  :hints (("goal"
           :in-theory (e/d (cross-product-pp-aux-for-s/c
                            cross-product-pp-aux-for-s/c-lst
                            and-eval-for-cross-product-pp ;;-redef
                            )
                           (rp-trans
                            (:rewrite valid-sc-subterms-of-cdr)
                            ;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:rewrite acl2::fn-check-def-not-quote)
                            (:rewrite valid-sc-when-list-instance)
                            (:rewrite ex-from-synp-lemma1)
                            ;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:definition valid-sc)
                            (:rewrite evl-of-extract-from-rp-2)
                            (:rewrite default-car)
                            (:rewrite valid-sc-subterms-cons)
                            (:rewrite default-cdr)
                            (:definition is-rp$inline)
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition eval-and-all)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

(defret cross-product-pp-aux-for-s/c-main-valid-sc-subterms
  (implies (and (valid-sc single-s/c a)
                (valid-sc-subterms e-lst a)
                (rp-termp single-s/c)
                (rp-term-listp e-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn cross-product-pp-aux-for-s/c-main
  :hints (("goal"
           :in-theory (e/d (cross-product-pp-aux-for-s/c-main
                            and-eval-for-cross-product-pp;;-redef
                            )
                           (rp-trans
                            (:rewrite valid-sc-subterms-of-cdr)
                            ;;                            (:rewrite acl2::o-p-o-infp-car)
                            (:rewrite acl2::fn-check-def-not-quote)
                            (:rewrite valid-sc-when-list-instance)
                            (:rewrite ex-from-synp-lemma1)
                            ;;                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:definition valid-sc)
                            (:rewrite evl-of-extract-from-rp-2)
                            (:rewrite default-car)
                            (:rewrite valid-sc-subterms-cons)
                            (:rewrite default-cdr)
                            (:definition is-rp$inline)
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition eval-and-all)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

(local
 (defthm dummy-sum-lemma
   (implies (equal (sum a b) x)
            (equal (sum a b other)
                   (sum x other)))))

(local
 (defthm AND-LST-EVAL-FOR-CROSS-PRODUCT-PP-when-atom
   (implies (atom pp-lst)
            (equal (sum-lst-and-eval-for-cross-product-pp pp-lst e-lst a)
                   0))
   :hints (("Goal"
            :in-theory (e/d (sum-lst-and-eval-for-cross-product-pp) ())))))

(defthm AND-LST-EVAL-FOR-CROSS-PRODUCT-PP-opener-when-e-lst-evs-to-1
  (implies (EQUAL (AND-LIST 0 (RP-EVLT-LST E-LST A))
                  1)
           (equal (sum-lst-and-eval-for-cross-product-pp lst
                                                         E-LST A)
                  (sum-list-eval lst a)))
  :hints (("Goal"
           :in-theory (e/d (sum-lst-and-eval-for-cross-product-pp
                            BIT-FIX-LST
                            AND-EVAL-FOR-CROSS-PRODUCT-PP;;-REDEF
                            )
                           ()))))

(defthm AND-LST-EVAL-FOR-CROSS-PRODUCT-PP-opener-when-e-lst-evs-to-0
  (implies (EQUAL (AND-LIST 0 (RP-EVLT-LST E-LST A))
                  0)
           (equal (sum-lst-and-eval-for-cross-product-pp lst
                                                         E-LST A)
                  0))
  :hints (("Goal"
           :in-theory (e/d (sum-lst-and-eval-for-cross-product-pp
                            BIT-FIX-LST
                            AND-EVAL-FOR-CROSS-PRODUCT-PP;;-REDEF
                            )
                           ()))))

(defthm equiv-of---
  (implies (and (integerp x)
                (integerp y))
           (equal (equal (-- x) (-- y))
                  (equal x y)))
  :hints (("Goal"
           :in-theory (e/d (--) ()))))

(defret-mutual cross-product-pp-aux-for-s/c-correct
  (defret cross-product-pp-aux-for-s/c-correct
    (implies (and valid
                  (valid-sc single-s/c a)
                  (valid-sc-subterms e-lst a)
                  (rp-termp single-s/c)
                  (rp-term-listp e-lst)
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (and (equal (sum (sum-list-eval res-s-lst a)
                              (sum-list-eval res-pp-lst a)
                              (sum-list-eval res-c-lst a))
                         (and-eval-for-cross-product-pp single-s/c e-lst a))
                  (Integerp (rp-evlt single-s/c a))
                  ;;(bitp (rp-evlt single-s/c a))
                  ))
    :fn cross-product-pp-aux-for-s/c)

  (defret cross-product-pp-aux-for-s/c-lst-correct
    (implies (and valid
                  (valid-sc-subterms s/c-lst a)
                  (valid-sc-subterms e-lst a)
                  (rp-term-listp s/c-lst)
                  (rp-term-listp e-lst)
                  (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (and (equal (sum (sum-list-eval res-s-lst a)
                              (sum-list-eval res-pp-lst a)
                              (sum-list-eval res-c-lst a))
                         (and-eval-for-cross-product-pp
                          (list 'quote (sum-list-eval s/c-lst a))
                          e-lst a))
                  ;;(bitp (rp-evlt single-s/c a))
                  ))
    :fn cross-product-pp-aux-for-s/c-lst)
  :mutual-recursion cross-product-pp-aux-for-s/c

  :hints (("goal"
           :expand ((GET-PP-AND-COEF SINGLE-S/C)
                    (SUM-LIST-EVAL NIL A)
                    (rp-trans (CADR SINGLE-S/C))
                    (SUM-LIST-EVAL S/C-LST A)
                    (:free (x y) (sum-list-eval (cons x y) a)))
           :in-theory (e/d
                       (;;GET-PP-AND-COEF

                        AND-TIMES-LIST
                        TIMES-OF-SUM-REVERSE
                        c-fix-arg-aux-correct-singled-out
                        bit-listp
                        has-bitp-rp-force-hyp-rewrite
                        regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_--_when_mult-formula-checks
                        regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_times_when_mult-formula-checks
                        regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_s_when_mult-formula-checks
                        regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_c_when_mult-formula-checks
                        cross-product-pp-aux-for-s/c
                        cross-product-pp-aux-for-s/c-lst
                        and-eval-for-cross-product-pp)
                       ((:REWRITE ACL2::ZP-OPEN)
                        (:REWRITE RW->-TO-GT)
                        (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
                        (:REWRITE LTE-CHAIN-SMART)
                        WHEN-M2-OF-AN-M2-ARG-IS-ZERO
                        (:DEFINITION EQ)

                        sum-list-eval

                        (:TYPE-PRESCRIPTION RP-TERMP)
                        (:TYPE-PRESCRIPTION LEN)
                        (:DEFINITION FLOOR)
                        (:REWRITE PP-TERM-P-IS-BITP-STRICT=NIL)
                        (:DEFINITION PP-TERM-P-FN)
                        
                        rp-trans
                        (:REWRITE DEFAULT-CDR)
                        ;;(:DEFINITION SUM-LIST-EVAL)
                        rp-evl-lst-of-cons
                        rp-evlt-lst-of-cons
                        rp-trans-lst-is-lst-when-list-is-absent
                        ;;rp-trans-opener
                        rp-evl-of-lambda
                        rp-evl-of-variable
                        (:definition valid-sc)
                        (:rewrite valid-sc-subterms-cdr)
                        (:definition eval-and-all)
                        (:rewrite valid-sc-subterms-of-cdr)
                        (:rewrite
                         rp-trans-is-term-when-list-is-absent)
                        rp-evlt-of-ex-from-rp
                        rp-trans-lst)))))

(defret cross-product-pp-aux-for-s/c-correct-singled-out
  (implies (and valid
                (valid-sc single-s/c a)
                (valid-sc-subterms e-lst a)
                (rp-termp single-s/c)
                (rp-term-listp e-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (and-eval-for-cross-product-pp single-s/c e-lst a)
                       (-- (sum-list-eval res-s-lst a))
                       (-- (sum-list-eval res-c-lst a)))))
  :fn cross-product-pp-aux-for-s/c

  :hints (("goal"
           :use ((:instance cross-product-pp-aux-for-s/c-correct))
           :in-theory (e/d () (cross-product-pp-aux-for-s/c-correct)))))

(defret cross-product-pp-aux-for-s/c-main-correct
  (implies (and valid
                (force (valid-sc single-s/c a))
                (force (valid-sc-subterms e-lst a))
                (rp-termp single-s/c)
                (rp-term-listp e-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (sum (sum-list-eval res-s-lst a)
                            (sum-list-eval res-pp-lst a)
                            (sum-list-eval res-c-lst a))
                       (and-eval-for-cross-product-pp single-s/c e-lst a))
                ;;(bitp (rp-evlt single-s/c a))
                ))
  :fn cross-product-pp-aux-for-s/c-main

  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d
                       (cross-product-pp-aux-for-s/c-main
                        regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_s-c-res_when_mult-formula-checks
                        s-c-res
                        AND-EVAL-FOR-CROSS-PRODUCT-PP)
                       (rp-trans
                        cross-product-pp-aux-for-s/c-correct-singled-out
                        VALID-SC-SINGLE-STEP-3
                        ;;RP-TRANS-OPENER-WHEN-LIST
                        EX-FROM-RP
                        RP-EVL-OF-TRANS-LIST-LEMMA
                        ENDP
                        rp-evl-lst-of-cons
                        rp-evlt-lst-of-cons
                        rp-trans-lst-is-lst-when-list-is-absent
                        ;;rp-trans-opener
                        rp-evl-of-lambda
                        rp-evl-of-variable
                        (:definition valid-sc)
                        (:rewrite valid-sc-subterms-cdr)
                        (:definition eval-and-all)
                        (:rewrite valid-sc-subterms-of-cdr)
                        (:rewrite
                         rp-trans-is-term-when-list-is-absent)
                        rp-evlt-of-ex-from-rp
                        rp-trans-lst)))))

(defret cross-product-pp-aux-for-s/c-main-correct-singled-out
  (implies (and valid
                (valid-sc single-s/c a)
                (valid-sc-subterms e-lst a)
                (force (rp-termp single-s/c))
                (force (rp-term-listp e-lst))
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (and-eval-for-cross-product-pp single-s/c e-lst a)
                       (-- (sum-list-eval res-s-lst a))
                       (-- (sum-list-eval res-c-lst a)))))
  :fn cross-product-pp-aux-for-s/c-main
  :hints (("goal"
           :use ((:instance cross-product-pp-aux-for-s/c-main-correct))
           :in-theory (e/d () (cross-product-pp-aux-for-s/c-main-correct)))))

(local
 (defthm dummy-sum-lemma4
   (implies (equal (sum x y z) other)
            (equal (equal (sum x y z k)
                          (sum other m))
                   (equal (ifix k)
                          (ifix m))))))

#|(local
(defthm dummy-sum-lemma4-v2
(implies (equal (sum x y z) other)
(equal (equal (sum x y z k)
(sum other m))
(equal (ifix k)
(ifix m))))))|#

;; (local
;;  (defthm AND-EVAL-FOR-CROSS-PRODUCT-PP-when-e-lst-is-1
;;    (implie

(defret cross-product-two-larges-aux-pp-lst-correct
  (implies (and valid
                (force (valid-sc single-s/c2 a))
                (force (valid-sc-subterms pp-lst a))
                (rp-termp single-s/c2)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (bitp (rp-evlt single-s/c2 a)))
           (equal (sum (sum-list-eval res-s-lst a)
                       (sum-list-eval res-pp-lst a)
                       (sum-list-eval res-c-lst a))
                  (and-eval-for-cross-product-pp-lst single-s/c2 pp-lst a)))
  :fn cross-product-two-larges-aux-pp-lst
  :hints (("goal"
           :expand ((SUM-LIST-EVAL PP-LST A)
                    (SUM-LIST-EVAL NIL A))
           :in-theory (e/d
                       (regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_binary-and_when_mult-formula-checks
                        regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_and-list_when_mult-formula-checks
                        and-eval-for-cross-product-pp
                        and-eval-for-cross-product-pp-lst
                        cross-product-two-larges-aux-pp-lst)
                       (VALID-SC
                        (:REWRITE DEFAULT-CDR)
                        sum-list-eval
                        (:REWRITE VALID-SC-SUBTERMS-CDR)
                        (:DEFINITION PP-TERM-P-FN)
                       ;;AND-EVAL-FOR-CROSS-PRODUCT-PP
                        rp-trans)))))

(defret cross-product-two-larges-aux-pp-lst-correct-singled-out
  (implies (and valid
                (force (valid-sc single-s/c2 a))
                (force (valid-sc-subterms pp-lst a))
                (rp-termp single-s/c2)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (bitp (rp-evlt single-s/c2 a)))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (-- (sum-list-eval res-s-lst a))
                       (-- (sum-list-eval res-c-lst a))
                       (and-eval-for-cross-product-pp-lst single-s/c2 pp-lst a))))
  :fn cross-product-two-larges-aux-pp-lst
  :hints (("Goal"
           :in-theory (e/d ()
                           (cross-product-two-larges-aux-pp-lst-correct))
           :use ((:instance cross-product-two-larges-aux-pp-lst-correct)))))

(defret cross-product-two-larges-aux-pp-lst-correct-valid-sc-subterms
  (implies (and (force (valid-sc single-s/c2 a))
                (force (valid-sc-subterms pp-lst a))
                (rp-termp single-s/c2)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn cross-product-two-larges-aux-pp-lst
  :hints (("Goal"
           :in-theory (e/d (cross-product-two-larges-aux-pp-lst)
                           ((:REWRITE VALID-SC-SUBTERMS-CDR)
                            valid-sc
                            (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                            (:DEFINITION EVAL-AND-ALL)
                            (:DEFINITION RP-TRANS))))))

(local
 (defthm valid-sc-of-SINGLE-S-P
   (implies (and (VALID-SC term A)
                 (SINGLE-S-P term))
            (and (VALID-SC (CADDdR term) A)
                 (VALID-SC (CADDR term) A)
                 (VALID-SC (CADR term) A)))
   :hints (("Goal"
            :in-theory (e/d (valid-sc is-rp is-if single-s-p) ())))))

(defret cross-product-two-larges-aux-valid-sc-subterms
  (implies (and (force (valid-sc single-s/c1 a))
                (force (valid-sc single-s/c2 a))
                (rp-termp single-s/c1)
                (rp-termp single-s/c2)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn cross-product-two-larges-aux
  :hints (("goal"
           :in-theory (e/d (cross-product-two-larges-aux)
                           (rp-trans
                            ;;rp-evlt-of-ex-from-rp
                            )))))

(defthm cross-product-two-larges-aux-correct-lemma
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (m2 (sum x y z (sum-list-eval (s-fix-pp-args-aux lst) a)))
                       (m2 (sum x y z (sum-list-eval lst a))))
                (equal (m2 (sum x y (sum-list-eval (s-fix-pp-args-aux lst) a)))
                       (m2 (sum x y (sum-list-eval lst a))))
                (equal (m2 (sum x y z (sum-list-eval (s-fix-pp-args-aux lst) a)
                                m))
                       (m2 (sum x y z m (sum-list-eval lst a))))
                (equal (m2 (sum x y z m (sum-list-eval (s-fix-pp-args-aux lst) a)))
                       (m2 (sum x y z m (sum-list-eval lst a))))
                (equal (m2 (sum x y z m (sum-list-eval (PP-SUM-MERGE-LST-FOR-S lst1 lst2) a)))
                       (m2 (sum x y z m (sum-list-eval lst1 a) (sum-list-eval lst2 a)))))))

(defret cross-product-two-larges-aux-correct
  (implies (and valid
                (force (valid-sc single-s/c1 a))
                (force (valid-sc single-s/c2 a))
                (rp-termp single-s/c1)
                (rp-termp single-s/c2)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                ;;(bitp (rp-evlt single-s/c1 a))
                (bitp (rp-evlt single-s/c2 a)))
           (and (equal (sum (sum-list-eval res-s-lst a)
                            (sum-list-eval res-pp-lst a)
                            (sum-list-eval res-c-lst a))
                       (if* (equal  (rp-evlt single-s/c2 a) 1)
                            (rp-evlt single-s/c1 a)
                            0))))
  :fn cross-product-two-larges-aux
  :hints (("goal"
           :induct (CROSS-PRODUCT-TWO-LARGES-AUX SINGLE-S/C1 SINGLE-S/C2)
           :do-not-induct t
           :expand ((CROSS-PRODUCT-TWO-LARGES-AUX SINGLE-S/C1 SINGLE-S/C2))
           :in-theory (e/d (c-fix-arg-aux-correct-singled-out
                            (:induction cross-product-two-larges-aux)
                            AND-EVAL-FOR-CROSS-PRODUCT-PP-LST
                            ;;rp-evlt-of-ex-from-rp-reverse
                            regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_c_when_mult-formula-checks
                            regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_s_when_mult-formula-checks
                            )
                           (rp-trans
                            (:REWRITE DEFAULT-CDR)
                            
                            valid-sc
                            ;;rp-evlt-of-ex-from-rp
                            )))))

(local
 (defthm cross-product-pp-aux-correct-dummy-lemma1
   (equal (equal (sum (-- x) (-- y)) (-- z))
          (equal (sum x y) (ifix z)))
   :hints (("Goal"
            :in-theory (e/d (sum -- ifix)
                            (+-IS-SUM))))))

(local
 (defthm cross-product-pp-aux-correct-dummy-lemma2
   (equal (equal (sum (-- x) (-- y) (-- z)) (-- k))
          (equal (sum x y z) (ifix k)))
   :hints (("Goal"
            :in-theory (e/d (sum -- ifix)
                            (+-IS-SUM))))))

(local
 (defthm cross-product-pp-pattern-check-implies-and-list-with-elements
   (implies (cross-product-pp-pattern-check single-pp)
            (and (equal (list-to-lst (caddr single-pp))
                        (cdr (caddr single-pp)))
                 (equal (car (caddr single-pp))
                        'list)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (list-to-lst
                             cross-product-pp-pattern-check) ())))))

(local
 (defthm cross-product-pp-pattern-check-implies-valid-sc
   (implies (and (cross-product-pp-pattern-check single-pp)
                 (valid-sc single-pp a))
            (and (VALID-SC-SUBTERMS (CDR (CADDR SINGLE-PP))
                                    A)))
   :rule-classes (:forward-chaining :rewrite)
   :hints (("Goal"
            :in-theory (e/d (list-to-lst
                             valid-sc is-rp is-if
                             cross-product-pp-pattern-check)
                            ())))))

(local
 (defthmd rp-evlt-of-list-in-hyp
   (implies (equal (car x) 'list)
            (equal (rp-evlt x a)
                   (rp-evlt-lst (cdr x) a)))))

(defthmd CROSS-PRODUCT-PP-PATTERN-CHECK3-implies
  (implies (and (cross-product-pp-pattern-check3 term)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (bitp (rp-evlt (car (cdr (caddr term))) a))
                (bitp (rp-evlt (cadr (cdr (caddr term))) a))))
  :hints (("Goal"
           :in-theory (e/d (CROSS-PRODUCT-PP-PATTERN-CHECK3
                            regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_s_when_mult-formula-checks)
                           ()))))

#|(defthm cross-product-pp-pattern-check3-implies-fc
(implies (and (cross-product-pp-pattern-check3 term))
(case-match term
(('and-list & ('list & &)) t)))
:rule-classes :forward-chaining
:hints (("Goal"
:in-theory (e/d (CROSS-PRODUCT-PP-PATTERN-CHECK3
regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp
regular-rp-evl-of_s_when_mult-formula-checks)
()))))|#

(defthm if*-of-bitp-and-bitp--lemma
  (implies (and (bitp x)
                (bitp y))
           (equal (if* (equal x 1) y 0)
                  (and-list 0 (list x y)))))

(defthmd rp-evlt-lst-of-two-elemets
  (implies (and (consp x)
                (consp (cdr x))
                (atom (cddr x)))
           (equal (rp-evlt-lst x a)
                  (list (rp-evlt (car x) a)
                        (rp-evlt (cadr x) a))))
  :hints (("Goal"
           :in-theory (e/d (rp-trans-lst)
                           ()))))

(defthm and-list-p-and-rp-termp-lemma
  (implies (and (rp-termp term)
                (and-list-p term)
                (CROSS-PRODUCT-PP-PATTERN-CHECK term))
           (RP-TERM-LISTP (CDR (CADDR term))))
  :hints (("Goal"

           :expand ((RP-TERM-LISTP (CDR TERM))
                    (RP-TERM-LISTP (CDDR TERM))
                    (RP-TERMP (CADDR TERM))
                    (RP-TERMP TERM))
           :in-theory (e/d (CROSS-PRODUCT-PP-PATTERN-CHECK
                            AND-LIST-P
                            RP-TERM-LISTP
                            rp-termp
                            rp-termp-single-step)
                           ()))))

(defthmd valid-sc-caddr-when-times
  (implies (and (case-match term (('times & &) t))
                (valid-sc term a))
           (valid-sc (caddr term) a)))

(local
 (defthmd valid-sc-of-car-when-validlistp
   (implies (and (valid-sc-subterms lst a)
                 (consp lst))
            (valid-sc (car lst) a))
   :rule-classes :rewrite))
(local
 (defthmd rp-termp-of-car-when-rp-term-listp
   (implies (and (rp-term-listp lst)
                 (consp lst))
            (rp-termp (car lst)))
   :rule-classes :rewrite))

(defret cross-product-pp-aux--mid-large-merge-correct
  (implies (and valid
                (valid-sc-subterms single-s-lst a)
                (rp-term-listp single-s-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (bit-listp (rp-evlt-lst single-s-lst a)))
           (and
            (equal (rp-evlt res a)
                   (and-list 0
                             (rp-evlt-lst single-s-lst a)))
            (equal (and-eval-for-cross-product-pp res e-lst a)
                   (and-eval-for-cross-product-lst-pp single-s-lst e-lst a))))
  :Fn cross-product-pp-aux--mid-large-merge
  :hints (("Goal"
           :expand ((LEN (CDDR SINGLE-S-LST))
                    (LEN (CDR SINGLE-S-LST))
                    (LEN SINGLE-S-LST))
           :in-theory (e/d (BIT-LISTP
                            AND-EVAL-FOR-CROSS-PRODUCT-LST-PP
                            AND-EVAL-FOR-CROSS-PRODUCT-PP
                            len
                            cross-product-pp-aux--mid-large-merge)
                           (+-IS-SUM)))))

(defret cross-product-pp-aux--mid-large-merge-valid-sc
  (implies (and valid
                (valid-sc-subterms single-s-lst a)
                (rp-term-listp single-s-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (bit-listp (rp-evlt-lst single-s-lst a)))
           (valid-sc res a))
  :Fn cross-product-pp-aux--mid-large-merge
  :hints (("Goal"
           :expand ((LEN (CDDR SINGLE-S-LST))
                    (LEN (CDR SINGLE-S-LST))
                    (LEN SINGLE-S-LST))
           :in-theory (e/d (BIT-LISTP
                            AND-EVAL-FOR-CROSS-PRODUCT-LST-PP
                            AND-EVAL-FOR-CROSS-PRODUCT-PP
                            len
                            cross-product-pp-aux--mid-large-merge)
                           (+-IS-SUM)))))

(defret cross-product-pp-aux-correct
  (implies (and valid
                (valid-sc single-pp a)
                (rp-termp single-pp)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (equal (sum (sum-list-eval res-s-lst a)
                            (sum-list-eval res-pp-lst a)
                            (sum-list-eval res-c-lst a))
                       (rp-evlt single-pp a))
                (integerp (rp-evlt single-pp a))))
  :fn cross-product-pp-aux
  :hints (("Goal"
           :expand ((rp-trans (CADR SINGLE-PP)))
           ;; :use ((:instance cross-product-pp-aux-precollect2-correct
           ;;                  (single-pp (cadr single-pp)))

           ;;       (:instance cross-product-pp-aux-precollect2-correct))
           :in-theory (e/d (times-of-sum-reverse
                            valid-sc-of-car-when-validlistp
                            cross-product-pp-aux-precollect2-correct
                            rp-termp-of-car-when-rp-term-listp
                            valid-sc-caddr-when-times
                            GET-PP-AND-COEF
                            and*
                            rp-evlt-lst-of-two-elemets
                            CROSS-PRODUCT-PP-PATTERN-CHECK3-implies
                            rp-evlt-of-list-in-hyp
                            cross-product-pp-aux
                            regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_--_when_mult-formula-checks
                            regular-rp-evl-of_times_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_times_when_mult-formula-checks
                            regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_and-list_when_mult-formula-checks
                            RP-TERM-LISTP)
                           (bitp
                            ;; cross-product-pp-aux-precollect2-correct
                            rp-trans
                            rp-evl-lst-of-cons
                            rp-evlt-lst-of-cons
                            rp-trans-lst-is-lst-when-list-is-absent
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition valid-sc)
                            (:rewrite valid-sc-subterms-cdr)
                            (:definition eval-and-all)
                            (:rewrite valid-sc-subterms-of-cdr)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst
                            if*)))))

(defret cross-product-pp-aux-valid-sc
  (implies (and valid
                (valid-sc single-pp a)
                (rp-termp single-pp)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn cross-product-pp-aux
  :hints (("Goal"
           :in-theory (e/d (cross-product-pp-aux
                            VALID-SC-OF-CAR-WHEN-VALIDLISTP
                            RP-TERMP-OF-CAR-WHEN-RP-TERM-LISTP
                            regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_--_when_mult-formula-checks
                            regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp
                            regular-rp-evl-of_and-list_when_mult-formula-checks)
                           (rp-trans
                            rp-evl-lst-of-cons
                            rp-evlt-lst-of-cons
                            rp-trans-lst-is-lst-when-list-is-absent
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition valid-sc)
                            (:rewrite valid-sc-subterms-cdr)
                            (:definition eval-and-all)
                            (:rewrite valid-sc-subterms-of-cdr)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

(local
 (defthm dummy-multiply-merge-lemma
   (equal (+ x (* count x))
          (* (1+ count) x))))

(defthm SUM-LIST-EVAL-of-repeat
  (implies (natp x)
           (equal (sum-list-eval (repeat x y) a)
                  (* x (ifix (rp-evlt y a)))))
  :hints (("Goal"
           :in-theory (e/d (REPEAT
                            sum
                            rw-dir2)
                           (+-IS-SUM
                            rw-dir1)))))

(local
 (defthm dummy-sum-cancel-lemma3-1
   (implies (integerp a)
            (equal (equal (sum x y a) a)
                   (equal (sum x y) 0)))
   :hints (("Goal"
            :in-theory (e/d (sum)
                            (+-IS-SUM))))))

(local
 (defthm collect-common-multiples
   (implies (and (integerp a)
                 (integerp x)
                 (integerp y))
            (equal (sum (* a x)
                        (* a y))
                   (* a (sum x y))))
   :hints (("Goal"
            :in-theory (e/d (sum)
                            (+-IS-SUM))))))

(defthm rp-term-listp-of-nthcdr
  (implies (and (rp-term-listp x)
                (<= size (len x)))
           (rp-term-listp (nthcdr size x)))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2)
                           (rw-dir1
                            +-IS-SUM)))))

(defret cross-product-pp-aux2-correct
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum (sum-list-eval res-s-lst a)
                       (sum-list-eval res-pp-lst a)
                       (sum-list-eval res-c-lst a))
                  (sum-list-eval pp-lst a)))
  :fn cross-product-pp-aux2
  :hints (("Goal"
           :in-theory (e/d (cross-product-pp-aux2
                            rw-dir2)
                           (rw-dir1
                            rp-trans
                            rp-evl-lst-of-cons
                            rp-evlt-lst-of-cons
                            rp-trans-lst-is-lst-when-list-is-absent
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition valid-sc)
                            (:rewrite valid-sc-subterms-cdr)
                            (:definition eval-and-all)
                            (:rewrite valid-sc-subterms-of-cdr)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

(defret cross-product-pp-aux2-correct-singled-out
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                )
           (equal (sum-list-eval res-pp-lst a)
                  (sum (-- (sum-list-eval res-s-lst a))
                       (-- (sum-list-eval res-c-lst a))
                       (sum-list-eval pp-lst a))))
  :fn cross-product-pp-aux2
  :hints (("Goal"
           :use ((:instance cross-product-pp-aux2-correct))
           :in-theory (e/d ()
                           (cross-product-pp-aux2-correct)))))

(defret cross-product-pp-aux2-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn cross-product-pp-aux2
  :hints (("Goal"
           :in-theory (e/d (valid-sc-subterms
                            cross-product-pp-aux2
                            sum)
                           (len
                            +-IS-SUM
                            rp-trans
                            rp-evl-lst-of-cons
                            rp-evlt-lst-of-cons
                            rp-trans-lst-is-lst-when-list-is-absent
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition valid-sc)
                            (:rewrite valid-sc-subterms-cdr)
                            (:definition eval-and-all)
                            (:rewrite valid-sc-subterms-of-cdr)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

(defret cross-product-pp-correct
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum (sum-list-eval res-s-lst a)
                       (sum-list-eval res-pp-lst a)
                       (sum-list-eval res-c-lst a))
                  (sum-list-eval pp-lst a)))
  :fn cross-product-pp
  :hints (("Goal"
           :in-theory (e/d (cross-product-pp)
                           (rp-trans
                            rp-evl-lst-of-cons
                            rp-evlt-lst-of-cons
                            rp-trans-lst-is-lst-when-list-is-absent
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition valid-sc)
                            (:rewrite valid-sc-subterms-cdr)
                            (:definition eval-and-all)
                            (:rewrite valid-sc-subterms-of-cdr)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

(defret cross-product-pp-correct-singled-out
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (-- (sum-list-eval res-s-lst a))
                       (-- (sum-list-eval res-c-lst a))
                       (sum-list-eval pp-lst a))))
  :fn cross-product-pp
  :hints (("Goal"
           :use ((:instance cross-product-pp-correct))
           :in-theory (e/d ()
                           (cross-product-pp-correct)))))

(defret cross-product-pp-valid-sc-subterms
  (implies (and (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (and (valid-sc-subterms res-s-lst a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-c-lst a)))
  :fn cross-product-pp
  :hints (("Goal"
           :in-theory (e/d (cross-product-pp)
                           (rp-trans
                            rp-evl-lst-of-cons
                            rp-evlt-lst-of-cons
                            rp-trans-lst-is-lst-when-list-is-absent
                            ;;rp-trans-opener
                            rp-evl-of-lambda
                            rp-evl-of-variable
                            (:definition valid-sc)
                            (:rewrite valid-sc-subterms-cdr)
                            (:definition eval-and-all)
                            (:rewrite valid-sc-subterms-of-cdr)
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            rp-evlt-of-ex-from-rp
                            rp-trans-lst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ex-from-pp-lst

(defret ex-from-pp-lst-aux-returns-valid-sc
  (implies (and (force (valid-sc-subterms pp-lst a)))
           (and (VALID-SC-SUBTERMS s-lst a)
                (VALID-SC-SUBTERMS res-pp-lst a)
                (VALID-SC-SUBTERMS c-lst a)))
  :fn ex-from-pp-lst-aux
  :hints (("Goal"
           :in-theory (e/d (ex-from-pp-lst-aux
                            create-and-list-instance
                            is-if is-rp)
                           ((:DEFINITION EVAL-AND-ALL)
                            ;;(:REWRITE VALID-SC-WHEN-SINGLE-C-P)
                            (:TYPE-PRESCRIPTION SINGLE-C-P$INLINE)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            ;;(:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:DEFINITION RP-TRANS)
                            ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION TRANS-LIST)
                            include-fnc-fn
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE VALID-SC-SUBTERMS-OF-CDR))))))

(defret ex-from-pp-lst-returns-valid-sc
  (implies (and (force (valid-sc-subterms pp-lst a)))
           (and (VALID-SC-SUBTERMS s-lst a)
                (VALID-SC-SUBTERMS res-pp-lst a)
                (VALID-SC-SUBTERMS c-lst a)))
  :fn ex-from-pp-lst
  :hints (("Goal"
           :in-theory (e/d (ex-from-pp-lst)
                           ()))))

(defthm bitp-of-single-s-c-res-p-in-sum-form
  (implies (and (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts)
                (valid-sc term a)
                (single-s-c-res-p (ex-from-rp term))
                (has-bitp-rp term))
           (bitp (sum
                  (sum-list
                   (rp-evlt (cadddr (ex-from-rp term)) a))
                  (sum-list
                   (rp-evlt (caddr (ex-from-rp term)) a))
                  (sum-list
                   (rp-evlt (cadr (ex-from-rp term)) a)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance pp-termp-is-bitp-lemma))
           :in-theory (e/d (S-C-RES
                            regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp)
                           (pp-termp-is-bitp-lemma)))))

(defthmd dummy-times-merge-lemma
  (and (equal (sum (times coef x) a1 a2 (-- (times coef y)))
              (sum (times coef (sum x (-- y))) a1 a2))
       (equal (sum (times coef x) a1 a2 (-- (times coef y)) a3)
              (sum (times coef (sum x (-- y))) a1 a2 a3)))
  :hints (("Goal"
           :use ((:instance times-of-sum-reverse))
           :in-theory (e/d () ()))))

(defthm nth-opener-when-consp
  (implies (and (consp x)
                (Posp n))
           (equal (nth n x)
                  (nth (1- n) (cdr x))))
  :hints (("Goal"
           :in-theory (e/d (rw-dir2)
                           (+-IS-SUM
                            rw-dir1)))))

(defthm sum-list-eval-of-nil
  (equal (sum-list-eval nil a)
         0)
  :hints (("Goal"
           :in-theory (e/d (sum-list-eval) ()))))

;; (defthm times-p-coef-implies-for-rp-evlt
;;   (implies (and (times-p x)
;;                 ;;(bind-free (list (cons 'a 'a)) (a))
;;                 )
;;            (equal (rp-trans (cadr x))
;;                   (cadr x)))
;;   :rule-classes ((:forward-chaining
;;                   :match-free :once)))

(defret ex-from-pp-lst-aux-correct
  (implies (and (mult-formula-checks state)
                (force (valid-sc-subterms pp-lst a))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (sum-list (rp-evlt-lst pp-lst a))
                       (-- (sum-list (rp-evlt-lst s-lst a)))
                       (-- (sum-list (rp-evlt-lst c-lst a))))))
  :fn ex-from-pp-lst-aux
  :hints (("goal"
           :induct (ex-from-pp-lst-aux pp-lst)
           :expand (;;(rp-trans (caddr (car pp-lst)))
                    (rp-trans (cadr (car pp-lst)))
                    (GET-PP-AND-COEF (CAR PP-LST))
                    ;;(rp-trans (CADDR (CADR (CAR PP-LST))))
                    ;;(ex-from-pp-lst pp-lst)
                    (:free (x y) (and-list y (list x)))
                    (SUM-LIST-EVAL PP-LST A)
                    (:free (x y) (sum-list-eval (cons x y) a))
                    )
           :do-not-induct t
           :in-theory (e/d* (ex-from-pp-lst-aux
                             dummy-times-merge-lemma
                             times-of-sum-reverse
                             regular-rp-evl-of_times_when_mult-formula-checks
                             

                             regular-rp-evl-of_and-list_when_mult-formula-checks
                             regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp
                             ;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             s-c-res

                             rp-evlt-of-list-2

                             ;;GET-PP-AND-COEF
                             ;;regular-eval-lemmas-with-ex-from-rp

                             HAS-BITP-RP-FORCE-HYP-REWRITE
                             )
                            (PP-TERMP-IS-BITP-LEMMA
                             PP-HAS-BITP-RP-IMPLIES
                             BINARY-FNC-P-IMPLIES-BITP
                             BINARY-FNC-P-RELIEVE
                             
                             (:REWRITE VALID-SC-OF-SINGLE-S-P)
                             VALID-SC-SUBTERMS-CONS
                             BITP-OF-RP-EVLT-OF-BINARY-FNC-P/AND-LISTP/LOGBIT-P
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:REWRITE DUMMY-SUM-LEMMA)
                             (:DEFINITION SUM-LIST-EVAL)
                             (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                             (:REWRITE
                              GET-PP-AND-COEF-CORRECT-WHEN-COEF-IS-0)
                             (:REWRITE EQUAL-WITH-ZERO-AND-1-WHEN-BITP)
                             (:TYPE-PRESCRIPTION
                              INTEGERP-OF-GET-PP-AND-COEF.COEF)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_AND-LIST_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE DUMMY-SUM-CANCEL-LEMMA1)
                             (:DEFINITION PP-TERM-P-FN)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:REWRITE WHEN-EX-FROM-RP-IS-1)
                             (:REWRITE VALID-SC-SUBTERMS-CDR)
                             (:TYPE-PRESCRIPTION PP-TERM-P-FN)
                             rp-termp
                             endp
                             NTH-OF-CONSTANT
                             ;;VALID-SC-SUBTERMS-CONS
                             VALID-SC-SUBTERMS
                             rp-trans
                             (:REWRITE CONSP-RP-TRANS-LST)
                             (:TYPE-PRESCRIPTION O<)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_--_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             ;;                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                             (:TYPE-PRESCRIPTION BINARY-SUM)
                             (:DEFINITION ACL2::APPLY$-BADGEP)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:DEFINITION INCLUDE-FNC-FN)
                             (:DEFINITION SUBSETP-EQUAL)
                             (:DEFINITION MEMBER-EQUAL)
                             valid-sc
                             sum-of-negated-elements
                             eval-and-all
                             ;;type-fix-when-bitp
                             ;;--of--equals
                             default-car
                             default-cdr
                             include-fnc-subterms-fn
                             rp-trans-lst-is-lst-when-list-is-absent
                             bitp
                             rp-trans-is-term-when-list-is-absent
                             ex-from-rp
                             rp-evlt-of-ex-from-rp
                             ;;is-falist
                             rp-termp)))
          ))

(defret ex-from-pp-lst-correct
  (implies (and (mult-formula-checks state)
                (force (valid-sc-subterms pp-lst a))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (sum-list (rp-evlt-lst pp-lst a))
                       (-- (sum-list (rp-evlt-lst s-lst a)))
                       (-- (sum-list (rp-evlt-lst c-lst a))))))
  :fn ex-from-pp-lst
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d* (ex-from-pp-lst
                             ;;regular-eval-lemmas-with-ex-from-rp
                             )
                            ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; extract-equals-from-pp-lst

(local
 (defthm is-equals-of-two-sides-lemma
   (implies (and (is-equals (ex-from-rp term))
                 (valid-sc term a))
            (equal (rp-evlt (caddr (ex-from-rp term)) a)
                   (rp-evlt (cadr (ex-from-rp term)) a)))
   :hints (("Goal"
            :do-not-induct t
            :expand ((VALID-SC (EX-FROM-RP TERM) A))
            :use ((:instance VALID-SC-OF-EX-FROM-RP))
            :in-theory (e/d ()
                            (ex-from-rp
                             VALID-SC-EX-FROM-RP
                             VALID-SC-OF-EX-FROM-RP))))))

(defret extract-equals-from-pp-lst-aux-correct
  (implies (and (force (valid-sc-subterms e-lst a))
                (force (rp-term-listp e-lst))
                res-pp-lst
                (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (and (equal (and$ (and-list 0
                                       (rp-evlt-lst res-e-lst a))
                             (sum-list-eval res-pp-lst a))
                       (and-list 0
                                 (rp-evlt-lst e-lst a)))
                (bitp (sum-list-eval res-pp-lst a))))
  :fn extract-equals-from-pp-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-equals-from-pp-lst-aux e-lst)
           :in-theory (e/d* (regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             extract-equals-from-pp-lst-aux)
                            ()))
          (and stable-under-simplificationp
               '(:use ((:instance pp-term-p-is-bitp
                                  (term (CADDR (EX-FROM-RP (CAR E-LST))))
                                  (strict nil)))))))

(defthmd sum-lst-and-eval-for-cross-product-pp-redef
  (implies (and ;;pp-lst
            (force (bitp (sum-list-eval pp-lst a))))
           (equal (sum-lst-and-eval-for-cross-product-pp pp-lst e-lst a)
                  (and$ (and-list 0
                                  (rp-evlt-lst e-lst a))
                        (sum-list-eval pp-lst a))))
  :hints (("Goal"
           :in-theory (e/d (AND-EVAL-FOR-CROSS-PRODUCT-PP
                            SUM-LST-AND-EVAL-FOR-CROSS-PRODUCT-PP)
                           ()))))

(defret extract-equals-from-pp-lst-aux-correct-2
  (implies (and (force (valid-sc-subterms e-lst a))
                (force (rp-term-listp e-lst))
                res-pp-lst
                (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-lst-and-eval-for-cross-product-pp res-pp-lst res-e-lst a)
                  (and-list 0
                            (rp-evlt-lst e-lst a))))
  :fn extract-equals-from-pp-lst-aux
  :hints (("Goal"
           :in-theory (e/d* (sum-lst-and-eval-for-cross-product-pp-redef
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             extract-equals-from-pp-lst-aux)
                            (bitp)))))

(defret extract-equals-from-pp-lst-aux-valid-sc
  (implies (force (valid-sc-subterms e-lst a))
           (and (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms res-e-lst a)))
  :fn extract-equals-from-pp-lst-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-equals-from-pp-lst-aux e-lst)
           :in-theory (e/d* (extract-equals-from-pp-lst-aux)
                            (valid-sc)))))

(local
 (defthmd and-list-of-rp-evlt-of-list
   (implies (equal (car term) 'list)
            (equal (AND-LIST 0 (RP-EVLT term a))
                   (and-list 0 (RP-EVLT-LST (cdr term) a))))))

(defret extract-equals-from-pp-lst-correct
  (implies (and (force (valid-sc-subterms pp-lst a))
                (force (rp-term-listp pp-lst))
                (mult-formula-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval res-lst a)
                  (sum-list-eval pp-lst a)))
  :fn extract-equals-from-pp-lst
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x y)
                           (SUM-LIST-EVAL (cons x y) a))
                    (GET-PP-AND-COEF (CAR PP-LST))
                    (SUM-LIST-EVAL NIL A)
                    (SUM-LIST-EVAL PP-LST A))
           :induct (extract-equals-from-pp-lst pp-lst limit)
           :in-theory (e/d* (and-list-of-rp-evlt-of-list
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp
                             extract-equals-from-pp-lst)
                            (rp-termp
                             rp-trans
                             SUM-LIST-EVAL
                             valid-sc-subterms
                             valid-sc
                             ex-from-rp)))))

(defret extract-equals-from-pp-lst-valid-sc
  (implies (and (force (valid-sc-subterms pp-lst a)))
           (valid-sc-subterms res-lst a))
  :fn extract-equals-from-pp-lst
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-equals-from-pp-lst pp-lst limit)
           :in-theory (e/d* (extract-equals-from-pp-lst)
                            ((:REWRITE VALID-SC-SUBTERMS-CONS)
                             (:REWRITE VALID-SC-SUBTERMS-OF-CDR)
                             (:REWRITE VALID-SC-WHEN-LIST-INSTANCE)
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE EX-FROM-SYNP-LEMMA1)
                             (:REWRITE
                              RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                             (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                             rp-termp
                             rp-trans
                             SUM-LIST-EVAL
                             ex-from-rp)))))

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

(defret ex-from-pp-lst-correct-with-sum-list-eval
  (implies (and (mult-formula-checks state)
                (force (valid-sc-subterms pp-lst a))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval res-pp-lst a)
                  (sum (sum-list-eval pp-lst a)
                       (-- (sum-list-eval s-lst a))
                       (-- (sum-list-eval c-lst a)))))
  :fn ex-from-pp-lst
  :hints (("goal"
           :use ((:instance ex-from-pp-lst-correct))
           :do-not-induct t
           :in-theory (e/d* ()
                            (rp-trans
                             valid-sc
                             )))))

(defthm sum-of-5-equiv
  (implies (equal (sum x1 x2 x3 x4 x5) y)
           (equal (equal (sum x1 x2 x3 x4 x5 other) other2)
                  (equal (sum y other) other2))))

(defthm dummy-sum-of-5-and-2-shared-e-at-the-end
  (equal (equal (sum x1 x2 x3 x4 x5 a)
                (sum y1 a))
         (equal (sum x1 x2 x3 x4 x5)
                (sum y1))))

(defthmd when-sum-equiv-to-negated
  (equal (equal (sum a b) (-- x))
         (equal (-- (sum a b)) (ifix x)))
  :hints (("Goal"
           :in-theory (e/d (-- sum)
                           (+-IS-SUM)))))

(defthmd neg-times-into-coef
  (and (equal (-- (times coef term))
              (times (-- coef) term))
       (equal (times coef (-- term))
              (times (-- coef) term))))

(defthm times-p-coef-implies-for-rp-evlt
  (implies (and (times-p x)
                ;;(bind-free (list (cons 'a 'a)) (a))
                )
           (equal (rp-trans (cadr x))
                  (cadr x)))
  )

(defret new-sum-merge-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms sum-lst a)
                (rp-term-listp sum-lst))
           (and (valid-sc s a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (equal (sum (sum-list (rp-evlt s a))
                            (sum-list-eval pp-lst a)
                            (sum-list-eval c-lst a))
                       (sum-list-eval sum-lst a))))
  :fn new-sum-merge-aux
  :hints (("goal"
           :do-not-induct t
           :induct (new-sum-merge-aux sum-lst limit)
           :expand ((rp-trans (CADR (CAR SUM-LST)))
                    (new-sum-merge-aux sum-lst limit)
                    (get-pp-and-coef (car sum-lst)))
           :in-theory (e/d* (times-of-sum-reverse
                             -to---
                             new-sum-merge-aux
                             s-c-res
                             when-sum-equiv-to-negated
                             c-fix-arg-aux-correct-lemma
                             ;;regular-eval-lemmas-with-ex-from-rp

                             neg-times-into-coef

                             regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_--_when_mult-formula-checks
                             regular-rp-evl-of_times_when_mult-formula-checks
                             regular-rp-evl-of_equals_when_mult-formula-checks
                             regular-rp-evl-of_equals_when_mult-formula-checks_with-ex-from-rp
                             (:rewrite
                              regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_cons_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_sum-list_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp)

                             ;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             ;;new-sum-merge-aux-dissect-term
                             ;;new-sum-merge-aux-add-negated-coughed
                             (:induction new-sum-merge-aux)
                             sum-list-eval-of-cons
                             sum-list-eval-of-atom)
                            (
                             ;;(:rewrite rp::sum-assoc)
                             (:e --)
                             TIMES-OF---
                             (:rewrite
                              get-pp-and-coef-correct-when-coef-is-0)
                             (:type-prescription s-sum-merge)
                             (:rewrite equal-with-zero-and-1-when-bitp)
                             (:rewrite when-ex-from-rp-is-1)
                             (:definition is-synp$inline)
                             (:rewrite valid-sc-subterms-cdr)
                             sum-cancel-common
                             (:e tau-system)
                             (:definition eq)
                             (:type-prescription pp-term-p-fn)
                             (:definition pp-term-p-fn)
                             (:type-prescription quote-p$inline)
                             (:type-prescription is-rp$inline)
                             (:rewrite sum-of-negated-elements)
                             (:definition sum-list-eval)
                             ;;(:rewrite minus-of-sum)
                             (:type-prescription rp-termp)

                             (:type-prescription sum-list-eval)
                             (:type-prescription single-c-p$inline)
                             (:type-prescription mult-formula-checks)
                             (:type-prescription single-s-p$inline)
                             (:rewrite not-include-rp-means-valid-sc-lst)
                             (:type-prescription ex-from-synp)
                             (:type-prescription single-s-c-res-p$inline)
                             (:type-prescription o<)
                             (:definition include-fnc-subterms-fn)
                             (:type-prescription sum-list-p$inline)
                             (:type-prescription and-list-p$inline)
                             (:rewrite default-cdr)
                             (:type-prescription valid-sc-subterms)
                             (:type-prescription binary-sum)
                             (:rewrite default-car)

                             (:rewrite dummy-sum-cancel-lemma1)
                             (:type-prescription valid-sc)
                             (:type-prescription rp-term-listp)
                             (:definition new-sum-merge-aux)
                             ;;                             (:rewrite acl2::o-p-o-infp-car)

                             rp-trans
                             ;;rp-evlt-of-ex-from-rp
                             eval-and-all
                             rp-termp
                             rp-term-listp
                             valid-sc
                             valid-sc-subterms
                             rp-trans-is-term-when-list-is-absent
                             (:rewrite rp-evl-of-variable)
                             (:definition is-falist))))))

(defret extract-from-equals-lst-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms pp-lst a)
                (rp-term-listp pp-lst)
                changed)
           (and (valid-sc s a)
                (valid-sc-subterms res-pp-lst a)
                (valid-sc-subterms c-lst a)
                (and (equal (sum (sum-list (rp-evlt s a))
                                 (sum-list-eval res-pp-lst a)
                                 (sum-list-eval c-lst a))
                            (sum-list-eval pp-lst a))
                     (equal (sum (sum-list (rp-evlt s a))
                                 (sum-list-eval res-pp-lst a)
                                 (sum-list-eval c-lst a)
                                 a1)
                            (sum (sum-list-eval pp-lst a)
                                 a1)))))
  :fn extract-from-equals-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-from-equals-lst pp-lst)
           :expand ((extract-from-equals-lst pp-lst)
                    (get-pp-and-coef (car pp-lst))
                    (SUM-LIST-EVAL PP-LST A)
                    (:free (x y)
                           (SUM-LIST-EVAL (cons x y) a)))
           :in-theory (e/d* (times-of-sum-reverse

                             extract-from-equals-lst
                             s-c-res
                             when-sum-equiv-to-negated
                             c-fix-arg-aux-correct-lemma
                             ;;regular-eval-lemmas-with-ex-from-rp

                             regular-rp-evl-of_--_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_--_when_mult-formula-checks
                             regular-rp-evl-of_times_when_mult-formula-checks
                             regular-rp-evl-of_equals_when_mult-formula-checks
                             regular-rp-evl-of_equals_when_mult-formula-checks_with-ex-from-rp
                             (:rewrite
                              regular-rp-evl-of_and-list_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_cons_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_c_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_s-c-res_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_sum-list_when_mult-formula-checks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_s_when_mult-formula-checks_with-ex-from-rp)

                             ;;rp-evlt-of-ex-from-rp-reverse-only-atom-and-car
                             ;;new-sum-merge-aux-dissect-term
                             ;;new-sum-merge-aux-add-negated-coughed
                             (:induction new-sum-merge-aux)
                             sum-list-eval-of-cons
                             sum-list-eval-of-atom
                             ;;VALID-SC-SUBTERMS
                             )
                            (;;(:rewrite rp::sum-assoc)
                             SUM-LIST-EVAL-OF-CONS
                             sum-list-eval-of-atom
                             VALID-SC-SUBTERMS
                             ;;valid-sc-subterms-cons
                             valid-sc-subterms-of-consed
                             (:META BINARY-OR**/AND**-GUARD-META-CORRECT)
                             (:rewrite
                              get-pp-and-coef-correct-when-coef-is-0)
                             (:type-prescription s-sum-merge)
                             (:rewrite equal-with-zero-and-1-when-bitp)
                             (:rewrite when-ex-from-rp-is-1)
                             (:definition is-synp$inline)
                             (:rewrite valid-sc-subterms-cdr)
                             sum-cancel-common
                             (:e tau-system)
                             (:definition eq)
                             (:type-prescription pp-term-p-fn)
                             (:definition pp-term-p-fn)
                             (:type-prescription quote-p$inline)
                             (:type-prescription is-rp$inline)
                             (:rewrite sum-of-negated-elements)
                             (:definition sum-list-eval)
                             ;;(:rewrite minus-of-sum)
                             (:type-prescription rp-termp)

                             (:type-prescription sum-list-eval)
                             (:type-prescription single-c-p$inline)
                             (:type-prescription mult-formula-checks)
                             (:type-prescription single-s-p$inline)
                             (:rewrite not-include-rp-means-valid-sc-lst)
                             (:type-prescription ex-from-synp)
                             (:type-prescription single-s-c-res-p$inline)
                             (:type-prescription o<)
                             (:definition include-fnc-subterms-fn)
                             (:type-prescription sum-list-p$inline)
                             (:type-prescription and-list-p$inline)
                             (:rewrite default-cdr)
                             (:type-prescription valid-sc-subterms)
                             (:type-prescription binary-sum)
                             (:rewrite default-car)

                             (:rewrite dummy-sum-cancel-lemma1)
                             (:type-prescription valid-sc)
                             (:type-prescription rp-term-listp)
                             (:definition new-sum-merge-aux)
                             ;;                             (:rewrite acl2::o-p-o-infp-car)

                             rp-trans
                             ;;rp-evlt-of-ex-from-rp
                             eval-and-all
                             rp-termp
                             rp-term-listp
                             valid-sc
                             valid-sc-subterms
                             rp-trans-is-term-when-list-is-absent
                             (:rewrite rp-evl-of-variable)
                             (:definition is-falist))))))

(defret new-sum-merge-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (rp-termp term))
           (and (valid-sc s a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a)
                (equal (sum (sum-list (rp-evlt s a))
                            (sum-list-eval pp-lst a)
                            (sum-list-eval c-lst a))
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

(defret integer-listp-of-CONS-WITH-TIMES
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (integer-listp (rp-evlt-lst rest a))
                (integerp (rp-evlt term a)))
           (integer-listp (rp-evlt-lst res-lst a)))
  :fn CONS-WITH-TIMES
  :hints (("Goal"
           :in-theory (e/d (CONS-WITH-TIMES
                            CREATE-TIMES-INSTANCE)
                           ()))))

#|(defret integerp-of-GET-PP-AND-COEF
(implies (and (rp-evl-meta-extract-global-facts :state state)
(mult-formula-checks state)
(integerp (rp-evlt term a)))
(integerp (rp-evlt res-term a)))
:fn GET-PP-AND-COEF
:hints (("Goal"
:in-theory (e/d* (regular-rp-evl-of_times_when_mult-formula-checks
GET-PP-AND-COEF)
()))))|#

#|(defthm integer-listp-rp-evlt-lst
(implies (and (rp-evl-meta-extract-global-facts :state state)
(mult-formula-checks state)
(integer-listp (rp-evlt-lst lst1 a))
(integer-listp (rp-evlt-lst lst2 a)))
(integer-listp (rp-evlt-lst (S-SUM-MERGE-AUX lst1 lst2) a)))
:hints (("Goal"
:induct (S-SUM-MERGE-AUX lst1 lst2)
:in-theory (e/d (S-SUM-MERGE-AUX)
(rp-trans)))))|#

#|(defret integer-listp-c-fix-arg-aux
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
:in-theory (e/d (
C-FIX-ARG-AUX
rp-evlt-of-ex-from-rp-reverse-only-atom-and-car)
(rp-evlt-of-ex-from-rp)))))|#

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
                          (sum-list-eval arg-c-lst a)))
                  t))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (f2 (sum (sum-list (rp-evlt arg-s a))
                                (sum-list-eval arg-pp-lst a)
                                (sum-list-eval arg-c-lst a))))))
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
           ;;:expand ((C-SUM-MERGE-LST ''0 TO-BE-COUGHED-C-LST))
           :in-theory (e/d (c-spec-meta-aux
                            ;; c-pattern2-reduce-correct -when-res-c-is-0
                            ;;c-pattern2-reduce-correct-res-single-c-on-one-side
                            times2
                            ;;CREATE-S-C-RES-INSTANCE
                            minus-of-sum

                            ;;C-SUM-MERGE-MAIN

                            valid-sc-single-step
                            f2-of-times2-reverse
                            rp-trans-lst-of-consp
                            s-c-res
                            sum-list-eval-of-atom
                            sum-list-eval-of-cons)
                           (;;f2-of-times2-reverse
                            f2-of-minus-3
                            nfix
                            f2-of-minus
                            rp-trans
                            (:rewrite
                             rp-trans-is-term-when-list-is-absent)
                            (:type-prescription rp-termp)
                            (:type-prescription rp-term-listp)
                            (:type-prescription o<)
                            (:definition eval-and-all)
                            (:definition include-fnc-fn)
                            (:rewrite not-include-rp-means-valid-sc-lst)
                            (:rewrite default-car)
                            (:definition
                             include-fnc-subterms-fn)
                            (:type-prescription include-fnc-subterms-fn)
                            (:type-prescription valid-sc)
                            (:rewrite sum-of-negated-elements)
                            ;; (:rewrite minus-of-sum)
                            (:rewrite ex-from-synp-lemma1)
                            (:rewrite dummy-sum-cancel-lemma1)
                            (:rewrite default-cdr)
                            (:definition is-synp$inline)
                            (:type-prescription binary-sum)
                            (:definition sum-list-eval)
                            rp-trans
                            rp-trans-lst
                            rp-trans-of-quoted
                            rp-evl-of-quote
                            f2-of-minus-2
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; extract-binary-xor-for-s-spec

(defret valid-sc-of-<fn>
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a))
           (valid-sc res a))
  :fn extract-binary-xor-for-s-spec-aux
  :hints (("Goal"
           :in-theory (e/d (extract-binary-xor-for-s-spec-aux)
                           ()))))

(defret valid-sc-subterms-of-<fn>
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (valid-sc-subterms res-lst a))
  :fn extract-binary-xor-for-s-spec-aux-lst
  :hints (("Goal"
           :in-theory (e/d (extract-binary-xor-for-s-spec-aux-lst)
                           ()))))

(defret valid-sc-of-extract-binary-xor-for-s-spec
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a))
           (valid-sc res a))
  :fn extract-binary-xor-for-s-spec
  :hints (("Goal"
           :in-theory (e/d (valid-sc-single-step
                            extract-binary-xor-for-s-spec)
                           ()))))

(defthm m2-of-binary-xor
  (and (equal (m2 (sum (binary-xor x y) other))
              (m2 (sum (bit-fix x)
                       (bit-fix y)
                       other)))
       (equal (m2 (binary-xor x y))
              (m2 (sum (bit-fix x)
                       (bit-fix y)))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            BIT-FIX
                            bitp)
                           ()))))

(defthm bitp-of-pp-term-p-lemma-when-binary-xor
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (pp-term-p term)
                (case-match term (('binary-xor & &) t)))
           (and (bitp (rp-evlt (cadr term) a))
                (bitp (rp-evlt (caddr term) a))
                (pp-term-p (cadr term) :strict nil)
                (pp-term-p (caddr term) :strict nil)))
  :hints (("goal"
           :use ((:instance pp-termp-is-bitp
                            (term (cadr term)))
                 (:instance pp-termp-is-bitp
                            (term (caddr term))))
           :do-not-induct t
           :expand ((pp-term-p term :strict nil)
                    (valid-sc term a))
           :in-theory (e/d (ex-from-rp
                            ;;valid-sc
                            is-rp is-if
                            pp-term-p)
                           (valid-sc-of-single-s-p
                            valid-sc
                            pp-termp-of-ex-from-rp
                            when-ex-from-rp-is-1
                            bitp-of-rp-evlt-of-binary-fnc-p/and-listp/logbit-p
                            eval-and-all
                            pp-termp-is-bitp)))))

(defthmd binary-not-to-binary-xor-1
  (equal (not$ x)
         (binary-xor 1 x))
  :hints (("Goal"
           :in-theory (e/d (not$ binary-xor) ()))))

(defthmd ex-from-rp-when-car-is-binary-not
  (implies (EQUAL (CAR TERM) 'BINARY-NOT)
           (equal (ex-from-rp term) term))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp is-rp) ()))))

(defthmd ex-from-rp-when-car-is-binary-xor
  (implies (EQUAL (CAR TERM) 'BINARY-xor)
           (equal (ex-from-rp term) term))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp is-rp) ()))))

(defret <fn>-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a)
                (pp-term-p term))
           (and (equal (m2 (rp-evlt res a))
                       (m2 (rp-evlt term a)))
                (equal (m2 (sum other (rp-evlt res a)))
                       (m2 (sum other (rp-evlt term a))))
                ))
  :fn extract-binary-xor-for-s-spec-aux
  :otf-flg t
  :hints (("Goal"
           :expand ((EXTRACT-BINARY-XOR-FOR-S-SPEC-AUX TERM)
                    (PP-TERM-P TERM :STRICT NIL))
           :induct (extract-binary-xor-for-s-spec-aux term)
           :do-not-induct t
           :in-theory (e/d* (or*
                             M2-OF-SUM-1-OTHER
                             ex-from-rp-when-car-is-binary-not
                             ex-from-rp-when-car-is-binary-xor
                             binary-not-to-binary-xor-1
                             valid-sc-single-step
                             extract-binary-xor-for-s-spec-aux
                             regular-rp-evl-of_s_when_mult-formula-checks
                             regular-rp-evl-of_cons_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-xor_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-not_when_mult-formula-checks_with-ex-from-rp
                             ;;regular-rp-evl-of_binary-and_when_mult-formula-checks_with-ex-from-rp
                             ;;regular-rp-evl-of_binary-and_when_mult-formula-checks
                             regular-rp-evl-of_binary-sum_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-sum_when_mult-formula-checks)
                            ((:TYPE-PRESCRIPTION RP-TRANS-LST)
                             INCLUDE-FNC-FN
                             rp-trans
                             pp-term-p
                             M2-SUMS-EQUIVALENCE
                             (:rewrite default-cdr)
                             (:rewrite default-car)
                             (:definition trans-list)
                             eval-and-all
                             and-list-to-binary-and-correct
                             (:meta binary-or**/and**-guard-meta-correct)
                             valid-sc-of-single-s-p
                             (:rewrite valid-rp-bitp-lemma)
                             valid-sc)))
          (and stable-under-simplificationp
               '(:use ((:instance M2-SUMS-EQUIVALENCE
                                  (x (RP-EVLT (EXTRACT-BINARY-XOR-FOR-S-SPEC-AUX (CADDR TERM))
                                              A))
                                  (y (RP-EVLT (CADDR TERM) A))
                                  (a (RP-EVLT (EXTRACT-BINARY-XOR-FOR-S-SPEC-AUX (CADR TERM))
                                              A))
                                  (b (RP-EVLT (CADR TERM) A))))))))


(defret <fn>-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms lst a))
           (and (equal (m2 (sum-list-eval res-lst a))
                       (m2 (sum-list-eval lst a)))
                (equal (m2 (sum other (sum-list-eval res-lst a)))
                       (m2 (sum other (sum-list-eval lst a))))
                (equal (m2 (sum (sum-list-eval res-lst a) other))
                       (m2 (sum (sum-list-eval lst a) other)))
                (equal (m2-chain other (sum-list-eval res-lst a))
                       (m2-chain other (sum-list-eval lst a)))
                (equal (m2-chain (sum-list-eval res-lst a) other)
                       (m2-chain (sum-list-eval lst a) other))))
  :fn extract-binary-xor-for-s-spec-aux-lst
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :induct (extract-binary-xor-for-s-spec-aux-lst lst)
           :in-theory (e/d* (m2-chain
                             valid-sc-subterms
                             extract-binary-xor-for-s-spec-aux-lst)
                            (M2-SUMS-EQUIVALENCE
                             VALID-SC-SUBTERMS-CDR
                             VALID-SC-SUBTERMS-CONS
                             extract-binary-xor-for-s-spec-aux-correct)))
          (and stable-under-simplificationp
               '(:use ((:instance M2-SUMS-EQUIVALENCE
                                  (x (RP-EVLT (EXTRACT-BINARY-XOR-FOR-S-SPEC-AUX (CAR LST))
                                              A))
                                  (y (RP-EVLT (CAR LST) A))
                                  (a (SUM-LIST-EVAL (EXTRACT-BINARY-XOR-FOR-S-SPEC-AUX-LST (CDR LST))
                                                    A))
                                  (b (SUM-LIST-EVAL (CDR LST) A)))
                       (:instance extract-binary-xor-for-s-spec-aux-correct
                                  (term (car lst))
                                  (other (SUM-LIST-EVAL (EXTRACT-BINARY-XOR-FOR-S-SPEC-AUX-LST (CDR LST))
                                                        A))))))
                                  
          ))

(defret <fn>-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc term a))
           (equal (m2 (sum-list (rp-evlt res a)))
                  (m2 (sum-list (rp-evlt term a)))))
  :fn extract-binary-xor-for-s-spec
  :hints (("Goal"
           :in-theory (e/d* (or*
                             valid-sc-single-step
                             extract-binary-xor-for-s-spec
                             regular-rp-evl-of_s_when_mult-formula-checks
                             regular-rp-evl-of_cons_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-xor_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-sum_when_mult-formula-checks_with-ex-from-rp
                             regular-rp-evl-of_binary-sum_when_mult-formula-checks)
                            ((:rewrite default-cdr)
                             (:rewrite default-car)
                             (:definition trans-list)
                             eval-and-all
                             and-list-to-binary-and-correct
                             (:meta binary-or**/and**-guard-meta-correct)
                             valid-sc-of-single-s-p
                             (:rewrite valid-rp-bitp-lemma)
                             valid-sc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-c-spec-meta correct

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

; Matt K. mod: Avoid ACL2(p) error.
(acl2::set-waterfall-parallelism nil)

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
                           (new-sum-merge-correct)))
          (and stable-under-simplificationp
               '(:instructions ((s :backchain-limit 10))))))
