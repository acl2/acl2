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

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(include-book "../mult-defs")

(define rp-equal-cnt-pp+ (term1 term2)
  (rp-equal-cnt term1 term2 0))

(memoize 'rp-equal-cnt-pp+)

(define is-car-x-pp+ ((x consp))
  (or (eq (car x) 'p+)
      (eq (car x) 'adder-b+)
      ))

(defun rp-equal-iter-pp+ (x y lst-flg)
  ;; returns (mv order equal-x-y)
  (declare (xargs :guard t
                  :measure (+ (cons-count x) (cons-count y))
                  :hints (("Goal"
                           :in-theory (e/d (measure-lemmas) ())))))
  (cond
   (lst-flg (if (or (atom x)
                    (atom y))
                (equal x y)
              (and (rp-equal-iter-pp+ (car x) (car y) nil)
                   (rp-equal-iter-pp+ (cdr x) (cdr y) t))))
   (t (let ((x (ex-from-rp-loose x))
            (y (ex-from-rp-loose y)))
        (cond ((or (atom x)
                   (atom y)
                   (eq (car x) 'quote))
               (equal x y))
              ((is-car-x-pp+ x)
               (rp-equal-cnt-pp+ x y))
              (t (and (equal (car x) (car y))
                      (rp-equal-iter-pp+ (cdr x) (cdr y) t))))))))

(define rp-equal-cnt-iter (x y cnt)
  (declare (ignorable cnt))
  (rp-equal-iter-pp+ x y nil))

(defund rp-equal-iter-pp+-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('equal a b)
     (if (rp-equal-iter-pp+ a b nil)
         (mv ''t t)
       (mv term `(nil t t))))
    (& (mv term nil))))

(def-formula-checks-default-evl
 rp-evl
 (strip-cars *small-evl-fncs*))

(def-formula-checks
 rp-equal-iter-pp+-meta-formula-checks
 (rp-equal-iter-pp+-meta
  p+))

(local
 (defthmd rp-evlt-of-ex-from-rp-loose-reverse
   (implies (syntaxp (atom term))
            (equal (rp-evlt term a)
                   (rp-evlt (EX-FROM-RP-LOOSE term) a)))
   :hints (("Goal"
            :induct (EX-FROM-RP-LOOSE term)
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             IS-RP-LOOSE) ())))))

(local
 (encapsulate
   nil

   (local
    (defthm rp-termp-lemma1
      (implies (and (rp-termp term)
                    (consp term))
               (rp-termp (car term)))
      :hints (("goal"
               :expand (rp-termp term)
               :in-theory (e/d (ex-from-rp-loose is-rp-loose
                                                 rp-termp) ())))))

   (local
    (defthm rp-termp-lemma2
      (implies (and (rp-termp term)
                    (CONSP term))
               (rp-termp (car term)))
      :hints (("goal"
               :expand (rp-termp term)
               :in-theory (e/d (ex-from-rp-loose is-rp-loose
                                                 rp-termp) ())))))

   (local
    (defthm lemma2
      (implies (and (equal (rp-evl-lst (cdr x) a)
                           (rp-evl-lst (cdr y) a))
                    (equal (car x) (car y))
                    (consp x)
                    (consp y)
                    (not (quotep x)))
               (equal (equal (rp-evl x a)
                             (rp-evl y a))
                      t))
      :hints (("Goal"
               :in-theory (e/d (rp-evl-of-fncall-args) ())))))
   
   
   (local
    (defthm lemma2-v2
      (implies (and (equal (rp-evlt-lst (cdr x) a)
                           (rp-evlt-lst (cdr y) a))
                    (equal (car x) (car y))
                    (consp x)
                    (rp-termp x)
                    (rp-termp y)
                    (consp y)
                    (not (quotep x)))
               (equal (equal (rp-evlt x a)
                             (rp-evlt y a))
                      t))
      :hints (("Goal"
               :do-not-induct t
               :cases ((is-falist x))
               :expand ((RP-TRANS Y)
                        (RP-EVL-OF-TRANS-LIST NIL A))
               :in-theory (e/d (rp-evl-of-fncall-args) ())))))

   (local
    (defthm rp-evlt-of-rp-equal-iter-pp+-lemma
      (if (equal lst-flg 'nil)
          (implies (and (rp-evl-meta-extract-global-facts)
                        (rp-termp x)
                        (rp-termp y)
                        (rp-equal-iter-pp+-meta-formula-checks state)
                        (rp-equal-iter-pp+ x y lst-flg))
                   (equal (equal (rp-evlt x a)
                                 (rp-evlt y a))
                          t))
        (implies (and (rp-evl-meta-extract-global-facts)
                      (rp-term-listp x)
                      (rp-term-listp y)
                      (rp-equal-iter-pp+-meta-formula-checks state)
                      (rp-equal-iter-pp+ x y lst-flg))
                 (equal (equal (rp-evlt-lst x a)
                               (rp-evlt-lst y a))
                        t)))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (EX-FROM-RP-LOOSE X))
                                (term2 (EX-FROM-RP-LOOSE y))))
               :in-theory (e/d (rp-equal-iter-pp+
                                ;;rp-evl-of-fncall-args
                                rp-evlt-of-ex-from-rp-loose-reverse
                                rp-equal-cnt-pp+)
                               (EVL-OF-EXTRACT-FROM-RP-LOOSE
                                rp-termp))))))

   (defthm rp-evl-of-rp-equal-iter-pp+
     (implies (and (rp-evl-meta-extract-global-facts)
                   (rp-termp term)
                   (rp-equal-iter-pp+-meta-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (rp-equal-iter-pp+-meta term)) a)
                     (rp-evlt term a)))
     :hints (("Goal"
              :use ((:instance rp-evlt-of-rp-equal-iter-pp+-lemma
                               (x (CADR TERM))
                               (y (CADDR TERM))
                               (lst-flg nil)))
              :in-theory (e/d (rp-equal-iter-pp+-meta
                               rp-equal-iter-pp+
                               rp-equal-cnt-pp+)
                              (EX-FROM-RP-LEMMA1)))))))

(local
 (defthm rp-valid-termp-rp-equal-iter-pp+-meta
   (implies (and (rp-termp term))
            (rp-termp (mv-nth 0 (rp-equal-iter-pp+-meta term))))
   :hints (("Goal"
            :in-theory (e/d (RP-EQUAL-ITER-PP+-META) ())))))

(local
 (defthm valid-sc-rp-equal-iter-pp+-meta
   (implies (and (valid-sc term a))
            (valid-sc (mv-nth 0 (rp-equal-iter-pp+-meta term)) a))
   :hints (("Goal"
            :in-theory (e/d (RP-EQUAL-ITER-PP+-META) ())))))

(local
 (defthm DONT-RW-SYNTAXP-RP-EQUAL-ITER-PP+-META
   (dont-rw-syntaxp (mv-nth 1 (rp-equal-iter-pp+-meta term)))
   :hints (("Goal"
            :in-theory (e/d (rp-equal-iter-pp+-meta) ())))))

(defthm rp-equal-iter-pp+-meta-is-valid-rp-meta-rulep
  (implies (and (rp-equal-iter-pp+-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'rp-equal-iter-pp+-meta
                             :trig-fnc 'equal
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            rp-term-listp
                            VALID-SC)))))


(rp::add-meta-rules
 rp-equal-iter-pp+-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'rp-equal-iter-pp+-meta
        :trig-fnc 'equal
        :dont-rw t
        :valid-syntax t)))

#|(mutual-recursion
(defun
rp-equal-for-pp+ (term1 term2)
(declare (xargs :mode :logic
:verify-guards t
:guard t))
"check syntactic equivalance of two terms by ignoring all the rp terms"
(let* ((term1 (ex-from-rp-loose term1))
(term2 (ex-from-rp-loose term2)))
(cond ((or (atom term1)
(atom term2)
(acl2::fquotep term1)
(acl2::fquotep term2))
(equal term1 term2))
((eq (car term1) 'pp+)
(rp-eq term1 term2))
(t (and (eq (car term1) (car term2))
(rp-equal-for-pp+-subterms (cdr term1)
(cdr term2)))))))
(defun rp-equal-for-pp+-subterms (subterm1 subterm2)
(declare (xargs :mode :logic
:guard t))
(if (or (atom subterm1) (atom subterm2))
(equal subterm1 subterm2)
(and (rp-equal-for-pp+ (car subterm1) (car subterm2))
(rp-equal-for-pp+-subterms (cdr subterm1)
(cdr subterm2))))))||#

#|(local
(make-flag  rp-equal-for-pp+ :defthm-macro-name defthm-rp-equal-for-pp+))||#
