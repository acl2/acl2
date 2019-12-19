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

(include-book "meta-fncs")

(local
 (in-theory (enable ex-from-rp-loose-is-ex-from-rp)))

(local
 (in-theory (enable rp-trans trans-list)))

(local
 (defthm-rp-equal
   (defthm rp-order-is-rp-equal
     (implies (and (rp-termp term1)
                   (rp-termp term2))
              (equal (mv-nth 1 (rp-order term1 term2))
                     (rp-equal term1 term2)))
     :flag rp-equal)
   (defthm rp-order-lst-is-rp-equal-subterms
     (implies (and (rp-term-listp subterm1)
                   (rp-term-listp subterm2))
              (equal (mv-nth 1 (rp-order-lst subterm1 subterm2))
                     (rp-equal-subterms subterm1 subterm2)))
     :flag rp-equal-subterms)
   :hints (("goal"
            :expand ((rp-order term1 term2))
            :in-theory (e/d (rp-order-lst
                             rp-order) ())))))

(create-regular-eval-lemma -- 1 mult-formula-checks)
(create-regular-eval-lemma binary-append 2 mult-formula-checks)
(create-regular-eval-lemma binary-and 2 mult-formula-checks)
(create-regular-eval-lemma and-list 1 mult-formula-checks)

(defun sum-list-eval (lst a)
  (if (atom lst)
      0
    (sum (rp-evlt (car lst) a)
         (sum-list-eval (cdr lst) a))))

(defthm to-list*-sum-eval
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state))
           (equal (sum-list (rp-evl (trans-list (rp-trans-lst lst)) A))
                  (sum-list-eval lst a)))
  :hints (("Goal"
           :do-not-induct t
           :induct (sum-list-eval lst a)
           :expand ((RP-EVL-OF-TRANS-LIST NIL A)
                    (:free (x y)
                           (RP-EVL-OF-TRANS-LIST (cons x y) a)))
           :in-theory (e/d (sum-list
                            trans-list) ()))))

(local
 (define negated-termsp ((term1)
                         (term2))
   (b* (((mv neg1 term1)
         (case-match term1 (('-- a) (mv t a)) (& (mv nil term1))))
        ((mv neg2 term2)
         (case-match term2 (('-- a) (mv t a)) (& (mv nil term2))))
        (equals
         (rp-equal term1 term2)))
     (and (not (equal neg1 neg2))
          equals))))

(local
 (defthm sum-of-negated-terms
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (mult-formula-checks state)
                (negated-termsp x y))
           (and (equal (sum (rp-evlt x a) (rp-evlt y a))
                       0)
                (equal (sum (rp-evlt x a) (rp-evlt y a) z)
                       (ifix z))))
  :hints (("Goal"
           :in-theory (e/d (negated-termsp
                            sum
                            --)
                           (rp-equal-cnt
                            ex-from-rp
                            rp-equal
                            UNICITY-OF-0
                            rp-evl-of-rp-equal))
           :use ((:instance rp-evlt-of-rp-equal
                            (term1 x)
                            (term2 (cadr y)))
                 (:instance rp-evlt-of-rp-equal
                            (term1 y)
                            (term2 (cadr x))))))))

(local
 (defthm s-order-and-negated-termsp-redef
   (implies (and (rp-termp term1)
                 (rp-termp term2))
            (equal (MV-NTH 1
                           (s-order-and-negated-termsp term1
                                                       term2))
                   (negated-termsp term1 term2)))
   :hints (("Goal"
            :in-theory (e/d (s-order-and-negated-termsp
                             negated-termsp)
                            ())))))

(local
 (defthm PP-LIST-ORDER-equals-redef
   (equal (mv-nth 1 (PP-LIST-ORDER x y))
          (equal x y))
   :hints (("Goal"
            :in-theory (e/d (pp-list-order) ())))))

(skip-proofs
 (local
  (defthm pp-order-equals-redef
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (equal (mv-nth 1 (pp-order x y))
                    (equal (rp-evlt (case-match x (('-- a) a) (& x)) a)
                           (rp-evlt  (case-match y (('-- a) a) (& y)) a))))
    :hints (("Goal"
             :in-theory (e/d (pp-order)
                             (rp-trans)))))))

;; (local
;;  (defthm pp-order-and-negated-termsp-redef
;;    (implies (and (rp-evl-meta-extract-global-facts :state state)
;;                       (mult-formula-checks state)
;;                  (rp-termp term1)
;;                  (rp-termp term2))
;;             (equal (mv-nth 1
;;                            (pp-order-and-negated-termsp term1
;;                                                         term2))
;;                    (negated-termsp term1 term2)))
;;    :otf-flg t
;;    :hints (("goal"
;;             :in-theory (e/d (pp-order-and-negated-termsp
;;                              negated-termsp)
;;                             ())))))

(skip-proofs
 (progn
   (defthm pp-sum-merge-aux-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state))
              (equal (sum-list (rp-evlt `(list . ,(mv-nth 0 (pp-sum-merge-aux
                                                             term1 term2 cnt)))
                                        a))
                     (sum (sum-list (rp-evlt `(list . ,term1) a))
                          (sum-list (rp-evlt `(list . ,term2) a)))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((RP-TRANS (CONS 'LIST* TERM2))
                       (RP-EVL-OF-TRANS-LIST NIL A)
                       (:free (x y)
                              (sum-list (cons x y)))
                       (RP-TRANS (CONS 'LIST* TERM1)))
              :induct (pp-sum-merge-aux term1 term2 cnt)
              :in-theory (e/d (pp-sum-merge-aux)
                              (rp-termp)))))

   (defthm pp-sum-merge-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (mult-formula-checks state))
              (equal (sum-list (rp-evlt (mv-nth 0 (pp-sum-merge term1 term2)) a))
                     (sum (sum-list (rp-evlt term1 a))
                          (sum-list (rp-evlt term2 a)))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance pp-sum-merge-aux-correct
                               (term1 (cdr term1))
                               (term2 (cdr term2))
                               (cnt 0)))
              :in-theory (e/d (pp-sum-merge)
                              (rp-trans
                               pp-sum-merge-aux-correct)))))))

(progn
  (defthm s-sum-merge-aux-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-term-listp term1)
                  (rp-term-listp term2))
             (equal (sum-list (rp-evlt `(list . ,(s-sum-merge-aux term1 term2)) a))
                    (sum (sum-list (rp-evlt `(list . ,term1) a))
                         (sum-list (rp-evlt `(list . ,term2) a)))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((RP-TRANS (CONS 'LIST* TERM2))
                      (RP-EVL-OF-TRANS-LIST NIL A)
                      (:free (x y)
                             (sum-list (cons x y)))
                      (RP-TRANS (CONS 'LIST* TERM1)))
             :induct (s-sum-merge-aux term1 term2)
             :in-theory (e/d (s-sum-merge-aux) (rp-termp)))))

  (defthm s-sum-merge-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state)
                  (rp-termp term1)
                  (rp-termp term2))
             (equal (sum-list (rp-evlt (s-sum-merge term1 term2) a))
                    (sum (sum-list (rp-evlt term1 a))
                         (sum-list (rp-evlt term2 a)))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance s-sum-merge-aux-correct
                              (term1 (cdr term1))
                              (term2 (cdr term2))))
             :in-theory (e/d (s-sum-merge)
                             (rp-termp
                              s-sum-merge-aux-correct
                              rp-trans))))))

(skip-proofs
 (defthm c-spec-valid-rp-meta-rulep
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (let ((rule (make rp-meta-rule-rec
                              :fnc 'c-spec-meta
                              :trig-fnc 'c-spec
                              :dont-rw t
                              :valid-syntax t)))
              (and (valid-rp-meta-rulep rule state)
                   (rp-meta-valid-syntaxp-sk rule state))))
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (rp-meta-valid-syntaxp)
                            (rp-termp
                             rp-term-listp
                             valid-sc))))))

(skip-proofs
 (defthm s-spec-valid-rp-meta-rulep
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (let ((rule (make rp-meta-rule-rec
                              :fnc 's-spec-meta
                              :trig-fnc 's-spec
                              :dont-rw t
                              :valid-syntax t)))
              (and (valid-rp-meta-rulep rule state)
                   (rp-meta-valid-syntaxp-sk rule state))))
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (rp-meta-valid-syntaxp)
                            (rp-termp
                             rp-term-listp
                             valid-sc))))))

(skip-proofs
 (defthm s-c-spec-valid-rp-meta-rulep
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (let ((rule (make rp-meta-rule-rec
                              :fnc 's-c-spec-meta
                              :trig-fnc 's-c-spec
                              :dont-rw t
                              :valid-syntax t)))
              (and (valid-rp-meta-rulep rule state)
                   (rp-meta-valid-syntaxp-sk rule state))))
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (rp-meta-valid-syntaxp)
                            (rp-termp
                             rp-term-listp
                             valid-sc))))))

(skip-proofs
 (defthm c-s-spec-valid-rp-meta-rulep
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (let ((rule (make rp-meta-rule-rec
                              :fnc 's-c-spec-meta
                              :trig-fnc 'c-s-spec
                              :dont-rw t
                              :valid-syntax t)))
              (and (valid-rp-meta-rulep rule state)
                   (rp-meta-valid-syntaxp-sk rule state))))
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (rp-meta-valid-syntaxp)
                            (rp-termp
                             rp-term-listp
                             valid-sc))))))

(skip-proofs
 (defthm sort-sum-metavalid-rp-meta-rulep
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (mult-formula-checks state))
            (let ((rule (make rp-meta-rule-rec
                              :fnc 'sort-sum-meta
                              :trig-fnc 'sort-sum
                              :dont-rw t
                              :valid-syntax t)))
              (and (valid-rp-meta-rulep rule state)
                   (rp-meta-valid-syntaxp-sk rule state))))
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (rp-meta-valid-syntaxp)
                            (rp-termp
                             rp-term-listp
                             valid-sc))))))

(rp::add-meta-rules
 mult-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 's-spec-meta
        :trig-fnc 's-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 'c-spec-meta
        :trig-fnc 'c-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 's-c-spec-meta
        :trig-fnc 's-c-spec
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 's-c-spec-meta
        :trig-fnc 'c-s-spec
        :dont-rw t
        :valid-syntax t)

  (make rp-meta-rule-rec
        :fnc 'sort-sum-meta
        :trig-fnc 'sort-sum
        :dont-rw t
        :valid-syntax t)))
