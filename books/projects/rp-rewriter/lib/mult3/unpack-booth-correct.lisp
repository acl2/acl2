
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

(include-book "unpack-booth")
(include-book "summation-tree-meta-fncs-correct")

(include-book "lemmas")
(include-book "lemmas-2")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

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
(create-regular-eval-lemma unpack-booth 1 mult-formula-checks)

(local
 (in-theory (disable (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:DEFINITION SUBSETP-EQUAL)
                     (:DEFINITION MEMBER-EQUAL)
                     (:REWRITE DEFAULT-CDR)
                     (:REWRITE ACL2::SUBSETP-REFLEXIVE-LEMMA)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1))))



(defret unpack-booth-for-pp-lst-correct
  (implies (and
            (rp-evl-meta-extract-global-facts :state state)
            (mult-formula-checks state)
            (valid-sc-subterms pp-lst a))
           (and (equal (sum-list-eval res-pp-lst a)
                       (sum-list-eval pp-lst a))
                (valid-sc-subterms res-pp-lst a)))
  :fn unpack-booth-for-pp-lst
  :hints (("Goal"
           :do-not-induct t
           :induct (unpack-booth-for-pp-lst pp-lst)
           :in-theory (e/d (unpack-booth-for-pp-lst) ()))))

#|(defthmd rp-evlt-of-ex-from-rp-reverse
  (implies (syntaxp (or (atom term)
                        (not (include-fnc term 'ex-from-rp))))
           (equal (rp-evlt term a)
                  (rp-evlt (ex-from-rp term) a))))||#


(local
 (defthmd ex-from-rp-when---
   (implies (and (EQUAL (CAR C-TERM) '--)
                 (CONSP C-TERM)
                 (CONSP (CDR C-TERM))
                 (NOT (CDDR C-TERM))
                 (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (equal (rp-evlt (ex-from-rp c-term) a)
                   (-- (rp-evlt (cadr c-term) a))))
   
   :hints (("Goal"
            :in-theory (e/d* (regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (rp-trans))))))



(defthmd f2-reverse-cough
  (implies (syntaxp (include-fnc term1 'C-FIX-ARG-AUX))
           (equal (sum term1 (f2 term2))
                  (f2 (sum term1 term1 term2))))
  :hints (("Goal"
           :use ((:instance f2-of-times2
                            (a term1)
                            (b term2)))
           :in-theory (e/d (times2) ()))))


(local
 (defthm dummy-lemma-1
   (equal (equal (sum (-- x) other)
                 (-- y))
          (equal (sum x (-- other))
                 (ifix y)))
   :hints (("Goal"
            :in-theory (e/d (sum
                             --)
                            (+-is-SUM))))))

(local
 (defthmd
   rp-evlt-of-ex-from-rp-reverse-2
   (implies (syntaxp (or (atom term)
                         (not (include-fnc term 'ex-from-rp))))
            (equal (rp-evl (rp-trans term) a)
                   (rp-evl (rp-trans (ex-from-rp term))
                           a)))))


(defthm c-fix-arg-aux-correct-one-side
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (b* (((mv coughed result)
                 (c-fix-arg-aux pp-lst neg-flag)))
             (equal
              (sum-list-eval result a)
              (sum (sum-list-eval pp-lst a)
                   (-- (sum-list-eval coughed a))
                   (-- (sum-list-eval coughed a))))))
  :hints (("Goal"
           :use ((:instance c-fix-arg-aux-correct))
           :in-theory (e/d () (c-fix-arg-aux-correct)))))

(defret create-c-instance-is-correct-one-side
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (valid-sc-subterms s-lst a)
                (valid-sc-subterms pp-lst a)
                (valid-sc-subterms c-lst a))
           (and (equal (sum-list-eval res-c-lst a)
                       (sum (-- (sum-list-eval res-s-lst a))
                            (-- (sum-list-eval res-pp-lst a))
                            (f2 (sum (sum-list-eval s-lst a)
                                     (sum-list-eval pp-lst a)
                                     (sum-list-eval c-lst a)))))))
  :fn create-c-instance)



(defret-mutual
  unpack-booth-for-s-correct
  (defret unpack-booth-for-s-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc  s-term a)
              (rp-termp s-term))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a))
                         (ifix (rp-evlt s-term a)))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-s)

  (defret unpack-booth-for-s-lst-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  s-lst a)
              (rp-term-listp s-lst))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a))
                         (sum-list-eval s-lst a))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-s-lst)

  (defret unpack-booth-for-c-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc  c-term a)
              (rp-termp c-term))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a))
                         (ifix (rp-evlt c-term a)))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-c)

  (defret unpack-booth-for-c-lst-correct
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  c-lst a)
              (rp-term-listp c-lst))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a))
                         (sum-list-eval c-lst a))
                  (valid-sc-subterms c-res-lst a)
                  (valid-sc-subterms pp-res-lst a)
                  (valid-sc-subterms s-res-lst a)))
    :fn unpack-booth-for-c-lst)

  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (unpack-booth-for-c-lst
                             unpack-booth-for-s-lst
                             unpack-booth-for-c
                             unpack-booth-for-s
                             rp-evlt-of-ex-from-rp-reverse-2
                             ex-from-rp-when---
                             f2-reverse-cough
                             (:REWRITE
                              REGULAR-RP-EVL-OF_C_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             (:REWRITE
                              REGULAR-RP-EVL-OF_s_WHEN_MULT-FORMULA-CHECKS_WITH-EX-FROM-RP)
                             )
                            (rp-evlt-of-ex-from-rp
                             ex-from-rp
                             rp-termp
                             (:REWRITE DEFAULT-CAR)
                             valid-sc-subterms
                             rp-term-listp

                             (:REWRITE SUM-OF-NEGATED-ELEMENTS)
                             ;;(:REWRITE MINUS-OF-SUM)
                             F2-OF-MINUS-2
                             F2-OF-MINUS
                             valid-sc
                             (:REWRITE RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                             ;;(:REWRITE RP-TRANS-OPENER-WHEN-LIST)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                             (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                             eval-and-all
                             rp-trans)))))


(defret unpack-booth-for-c-lst-correct-with-other
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  c-lst a)
              (rp-term-listp c-lst))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a)
                              other)
                         (sum (sum-list-eval c-lst a)
                              other))
                  ))
    :fn unpack-booth-for-c-lst)


(defret unpack-booth-for-s-lst-correct-with-other
    (implies (and
              (rp-evl-meta-extract-global-facts :state state)
              (mult-formula-checks state)
              (valid-sc-subterms  s-lst a)
              (rp-term-listp s-lst))
             (and (equal (sum (sum-list-eval s-res-lst a)
                              (sum-list-eval pp-res-lst a)
                              (sum-list-eval c-res-lst a)
                              other)
                         (sum (sum-list-eval s-lst a)
                              other)
                  )))
    :fn unpack-booth-for-s-lst)

(local
 (defthm --of-ifix
     (equal (-- (ifix x))
            (-- x))
   :hints (("Goal"
            :in-theory (e/d (--) ())))))

(defret unpack-booth-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (rp-termp term)
                (valid-sc term a))
           (and (valid-sc res a)
                (equal (rp-evlt res a)
                       (rp-evlt term a))))
  :fn unpack-booth-meta
  ;;:otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (unpack-booth-meta
                             UNPACK-BOOTH
                             S-C-RES
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas)
                            (rp-termp
                             valid-sc)))))
  
