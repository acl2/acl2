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

(include-book "fnc-defs")

(define rp-equal-cnt-memoized (term1 term2)
  (rp-equal-cnt term1 term2 0))

(memoize 'rp-equal-cnt-memoized)

(define is-car-x-pp+ ((x consp))
  (or (eq (car x) 'p+)
      (eq (car x) 'adder-b+)
      ))

(define are-c-instances ((x consp)
                         (y consp))
  :inline t
  (and (case-match x (('c & & & &) t))
       (case-match y (('c & & & &) t)))
  ///
  (defthm are-c-instances-implies-fc
    (implies (are-c-instances x y)
             (and (case-match x (('c & & & &) t))
                  (case-match y (('c & & & &) t))))
    :rule-classes :forward-chaining))

(define are-s-instances ((x consp)
                         (y consp))
  :inline t
  (and (case-match x (('s & & &) t))
       (case-match y (('s & & &) t)))
  ///
  (defthm are-s-instances-implies-fc
    (implies (are-s-instances x y)
             (and (case-match x (('s & & &) t))
                  (case-match y (('s & & &) t))))
    :rule-classes :forward-chaining))

(define rp-equal-iter-pp ((x)
                          (y)
                          (lst-flg booleanp))
  ;; returns (mv order equal-x-y)
  :guard (and (if lst-flg
                  (rp-term-listp x)
                (rp-termp x))
              (if lst-flg
                  (rp-term-listp y)
                (rp-termp y)))
  :prepwork ((local
              (in-theory (disable ex-from-rp)))
             (defthm nth-of-constant
               (implies (and (syntaxp (quotep pos))
                             (natp pos))
                        (equal (nth pos lst)
                               (IF (ENDP lst)
                                   NIL
                                   (IF (ZP pos)
                                       (CAR lst)
                                       (NTH (- pos 1) (CDR lst))))))))
  :measure (+ (cons-count x) (cons-count y))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (cond
   (lst-flg (if (or (atom x)
                    (atom y))
                (equal x y)
              (and (rp-equal-iter-pp (car x) (car y) nil)
                   (rp-equal-iter-pp (cdr x) (cdr y) t))))
   (t (let ((x (ex-from-rp$ x))
            (y (ex-from-rp$ y)))
        (cond ((or (atom x)
                   (atom y)
                   (eq (car x) 'quote))
               (equal x y))
              ((are-c-instances x y)
               (and (equal (nth 1 x) (nth 1 y))
                    (rp-equal-iter-pp (nth 2 x) (nth 2 y) nil)
                    (rp-equal-cnt-memoized (nth 3 x) (nth 3 y))
                    (rp-equal-iter-pp (nth 4 x) (nth 4 y) nil)))
              ((are-s-instances x y)
               (and (equal (nth 1 x) (nth 1 y))
                    (rp-equal-cnt-memoized (nth 2 x) (nth 2 y))
                    (rp-equal-iter-pp (nth 3 x) (nth 3 y) nil)))
              ((and (s-c-res-p x)
                    (s-c-res-p y))
               (and (rp-equal-iter-pp (nth 1 x) (nth 1 y) nil)
                    (rp-equal-cnt-memoized (nth 2 x) (nth 2 y))
                    (rp-equal-iter-pp (nth 3 x) (nth 3 y) nil)))              
              (t (and (equal (car x) (car y))
                      (rp-equal-iter-pp (cdr x) (cdr y) t))))))))

(define rp-equal-cnt-iter ((x rp-termp)
                           (y rp-termp)
                           cnt)
  (declare (ignorable cnt))
  (rp-equal-iter-pp x y nil))

(define rp-equal-iter-pp+-meta ((term rp-termp))
  (case-match term
    (('equal a b)
     (if (rp-equal-iter-pp a b nil)
         (mv ''t t)
       (mv term `(nil t t))))
    (& (mv term nil))))

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

(local
 (defthmd rp-evlt-of-ex-from-rp-reverse
   (implies (syntaxp (atom term))
            (equal (rp-evlt term a)
                   (rp-evlt (EX-FROM-RP term) a)))
   :hints (("Goal"
            :induct (EX-FROM-RP term)
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP)
                            ())))))

(local
 (encapsulate
   nil

   (local
    (defthm lemma1
      (implies (and (equal (rp-evlt-lst (cdr x) a)
                           (rp-evlt-lst (cdr y) a))
                    (equal (car x) (car y))
                    (consp x)
                    (consp y)
                    (not (quotep x)))
               (equal (equal (rp-evlt x a)
                             (rp-evlt y a))
                      t))
      :hints (("Goal"
               :do-not-induct t
               :cases ((is-falist x))
               :expand ((RP-TRANS Y))
               :in-theory (e/d (rp-evl-of-fncall-args) ())))))

   (defthm rp-evlt-of-rp-equal-iter-pp+-correct
     (if (equal lst-flg 'nil)
         (implies (and ;;(rp-evl-meta-extract-global-facts)
                       (rp-equal-iter-pp x y lst-flg))
                  (equal (rp-evlt x a)
                         (rp-evlt y a)))
       (implies (and ;;(rp-evl-meta-extract-global-facts)
                     (rp-equal-iter-pp x y lst-flg))
                (equal (rp-evlt-lst x a)
                       (rp-evlt-lst y a))))
     :hints (("Goal"
              :expand ((:free (x) (nth 3 x))
                       (:free (x) (nth 2 x))
                       (:free (x) (nth 1 x))
                       (:free (x) (nth 0 x)))
              :do-not-induct t
              :induct (rp-equal-iter-pp x y lst-flg)

              :in-theory (e/d (rp-equal-iter-pp
                               ex-from-rp-loose-is-ex-from-rp
                               ;;rp-evl-of-fncall-args
                               rp-evlt-of-ex-from-rp-reverse
                               rp-equal-cnt-memoized)
                              (EVL-OF-EXTRACT-FROM-RP-LOOSE
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE RP-EVL-OF-RP-EQUAL2-SUBTERMS)
;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:DEFINITION RP-EQUAL-SUBTERMS)
                               (:REWRITE
                                RP-EQUAL-SUBTERMS-IMPLIES-RP-EQUAL2-SUBTERMS)
                               (:DEFINITION RP-EQUAL2-SUBTERMS)
                               (:REWRITE RP-EVL-OF-RP-EQUAL-LOOSE)
                               (:REWRITE ACL2::NTH-WHEN-PREFIXP)
                               (:REWRITE RP-EVL-OF-RP-EQUAL-SUBTERMS)
                               (:REWRITE RP-EVL-OF-RP-EQUAL)
                               (:DEFINITION EX-FROM-RP)
                               (:REWRITE RP-EVL-OF-RP-EQUAL2)
                               (:DEFINITION RP-EQUAL2)
                               (:REWRITE RP-EQUAL-IMPLIES-RP-EQUAL2)
                               (:REWRITE NOT-INCLUDE-RP)
                               (:REWRITE DEFAULT-CDR)
                               (:DEFINITION RP-TRANS)
                               ;;rp-evlt-of-ex-from-rp-reverse
                               rp-evlt-of-ex-from-rp
                               rp-termp)))))

   (defthm rp-evlt-of-rp-equal-iter-pp+
     (equal (rp-evlt (mv-nth 0 (rp-equal-iter-pp+-meta term)) a)
            (rp-evlt term a))
     :hints (("Goal"
              :use ((:instance rp-evlt-of-rp-equal-iter-pp+-correct
                               (x (CADR TERM))
                               (y (CADDR TERM))
                               (lst-flg nil)))
              :in-theory (e/d (rp-equal-iter-pp+-meta
                               rp-equal-iter-pp
                               rp-equal-cnt-memoized)
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

#|(rp::add-meta-rules
 empty-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'rp-equal-iter-pp+-meta
        :trig-fnc 'equal
        :dont-rw t
        :valid-syntax t)))||#

(rp::add-meta-rule
 :meta-fnc rp-equal-iter-pp+-meta
 :trig-fnc equal
 :valid-syntaxp t
 :returns (mv term dont-rw))


(disable-meta-rules rp-equal-meta)
(disable-meta-rules rp-equal-cnt-meta)
