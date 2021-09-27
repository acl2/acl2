; RP-REWRITER

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

(include-book "../aux-functions")

(local
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(include-book "../eval-functions")

(include-book "../meta-rule-macros")

(local
 (include-book "../proofs/measure-lemmas"))

(local
 (include-book "../proofs/rp-equal-lemmas"))



(defun cons-to-list (term)
  term)

(defun list-to-cons (term)
  term)

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

(def-formula-checks
  cons-to-list-formula-checks
  (list-to-cons
   cons-to-list))


(define quote-all (lst)
  :returns (res rp-term-listp)
  (if (atom lst)
      nil
    (cons (list 'quote (car lst))
          (quote-all (cdr lst)))))

(define cons-to-list-meta-aux (term)
  :returns (mv (res-lst rp-term-listp :hyp (rp-termp term))
               (valid booleanp))
  (case-match term
    (('cons a rest)
     (b* (((mv rest-lst valid)
           (cons-to-list-meta-aux rest)))
       (if valid
           (mv (cons a rest-lst) t)
         (mv nil nil))))
    (''nil
     (mv nil t))
    (('quote lst)
     (if (true-listp lst)
         (mv (quote-all lst) t)
       (mv nil nil)))
    (& (mv nil nil))))


(define cons-to-list-meta (term)
  :returns (mv (res rp-termp :hyp (rp-termp term))
               (dont-rw))
  (case-match term
    (('cons-to-list a)
     (b* (((mv res valid) (cons-to-list-meta-aux a)))
       (if valid
           (if (consp res)
               (mv `(list . ,res) t)
             (mv ''nil t))
         (mv a t))))
    (&
     (mv term nil))))

(local
 (defthm rp-termp-of-trans-list
   (implies (rp-term-listp lst)
            (rp-termp (trans-list lst)))))

(define list-to-cons-meta (term)
  :returns (mv (res rp-termp :hyp (rp-termp term))
               (dont-rw))
  (case-match term
    (('list-to-cons ('list . lst))
     (mv (trans-list lst) t))
    (('list-to-cons ('list))
     (mv ''nil t))
    (('list-to-cons a)
     (mv a t))
    (&
     (mv term nil))))



(local
 (defret quote-all-correct
   (implies (and (true-listp lst))
            (and (equal (rp-evlt-lst res a)
                        (rp-evlt (list 'quote lst) a))
                 (equal (rp-evlt (trans-list res) a) lst)
                 (valid-sc-subterms res a)))
   :fn quote-all
   :hints (("goal"
            :do-not-induct t
            :induct (quote-all lst)
            :in-theory (e/d (quote-all
                             valid-sc is-if is-rp)
                            ())))))

(local
 (defret cons-to-list-meta-aux-correct
   (implies valid
            (and (equal (rp-evlt (trans-list res-lst) a)
                        (rp-evlt term a))
                 (equal (RP-EVL
                         (TRANS-LIST (RP-TRANS-LST res-lst)) a)
                        (rp-evlt term a))
                 (implies (valid-sc term a)
                          (valid-sc-subterms res-lst a))))
   :fn cons-to-list-meta-aux
   :hints (("Goal"
            :in-theory (e/d (cons-to-list-meta-aux)
                            (cons-equal
                             (:DEFINITION RP-TERMP)
                             (:DEFINITION RP-TERM-LISTP)
                             (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                             (:DEFINITION TRUE-LISTP)
                             (:REWRITE IS-IF-RP-TERMP)
                             (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)))))))

(local
 (defret quote-all-correct-lemma
   (implies (and (not (consp res))
                 (true-listp lst))
            (equal lst 'nil))
   :rule-classes :forward-chaining
   :fn quote-all
   :hints (("Goal"
            :in-theory (e/d (quote-all)
                            ())))))

(local
 (defret cons-to-list-meta-aux-correct-lemma
   (implies (and valid
                 (not (consp res-lst)))
            (equal term ''nil))
   :rule-classes :forward-chaining
   :fn cons-to-list-meta-aux
   :hints (("Goal"
            :in-theory (e/d (cons-to-list-meta-aux)
                            ())))))

(local
 (create-regular-eval-lemma cons-to-list 1 cons-to-list-formula-checks))




(local
 (create-regular-eval-lemma list-to-cons 1 cons-to-list-formula-checks))

(local
 (defthm rp-trans-of-list
   (implies (and (consp x)
                 (equal (car x) 'list))
            (equal (rp-trans x)
                   (trans-list (rp-trans-lst (cdr x)))))))   

(rp::add-meta-rule
 :meta-fnc cons-to-list-meta
 :trig-fnc cons-to-list
 :valid-syntaxp t
 :formula-checks cons-to-list-formula-checks
 :returns (mv term dont-rw)
 :hints (("Goal"
          :expand ((:free (x) (rp-trans (cons 'list x)))
                   (:free (x) (rp-termp (cons 'list x))))
          :in-theory (e/d* (cons-to-list-meta
                            is-rp
                            valid-sc
                            is-if
                            regular-eval-lemmas)
                           (rp-termp
                            is-falist
                            trans-list
                            RP-EVLT-LST-OF-CONS
                            RP-EVL-OF-TRANS-LIST-LEMMA
                            rp-trans
                            rp-trans-lst
                            rp-term-listp)))))

(rp::add-meta-rule
 :meta-fnc list-to-cons-meta
 :trig-fnc list-to-cons
 :valid-syntaxp t
 :formula-checks cons-to-list-formula-checks
 :returns (mv term dont-rw)
 :hints (("Goal"
          :expand ((:free (x) (rp-trans (cons 'list x)))
                   (:free (x) (rp-termp (cons 'list x))))
          :in-theory (e/d* (list-to-cons-meta
                            is-rp
                            valid-sc
                            is-if
                            regular-eval-lemmas)
                           (rp-termp
                            ;;is-falist
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC-LST)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            trans-list
                            ;;RP-EVLT-LST-OF-CONS
                            ;;RP-EVL-OF-TRANS-LIST-LEMMA
                            rp-trans
                            rp-trans-lst
                            rp-term-listp)))))
