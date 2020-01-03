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
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(define adder-and (x y)
  (and$ x y)
  ///
  (def-rp-rule$ t t
    bitp-adder-and
    (bitp (adder-and a b))))

(define adder-or (x y)
  (or$ x y)
  ///
  (def-rp-rule$ t t
    bitp-adder-or
    (bitp (adder-or a b))))

(define merge-adder-and (x y)
  (adder-and x y))

(define merge-adder-b+ (x y)
  :verify-guards nil
  (adder-sum x y))

(define merge-adder-or (x y)
  (adder-or x y))

(defmacro adder-and$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'adder-and rp::rst))))

(add-macro-fn adder-and$ adder-and t)

(defmacro adder-or$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'adder-or rp::rst))))

(add-macro-fn adder-or$ adder-or t)

(defmacro merge-adder-sum (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'type-fix (car rp::rst)))
        (t (xxxjoin 'merge-adder-b+ rp::rst))))

(add-macro-fn merge-adder-sum merge-adder-b+ t)

(define ex-from-rp/m2/f2/adder-sum/and/or (term)
  (case-match term
    (('adder-and x &)
     (ex-from-rp/m2/f2/adder-sum/and/or x))
    (('adder-or x &)
     (ex-from-rp/m2/f2/adder-sum/and/or x))
    (('adder-b+ x &)
     (ex-from-rp/m2/f2/adder-sum/and/or x))
    (('rp & x)
     (ex-from-rp/m2/f2/adder-sum/and/or x))
    (('m2 x)
     (ex-from-rp/m2/f2/adder-sum/and/or x))
    (('f2 x)
     (ex-from-rp/m2/f2/adder-sum/and/or x))
    ((fnc x s rest)
     `(,fnc ,s ,rest ,x))
    ((fnc x s)
     `(,fnc ,s ,x))
    (&
     term)))

(define adder-and$-order (x y)
  (b* ((x (ex-from-rp x))
       (y (ex-from-rp y))
       (x-is-and (case-match x (('adder-and & &) t)))
       (y-is-and (case-match y (('adder-and & &) t)))
       (x (ex-from-rp/m2/f2/adder-sum/and/or x))
       (y (ex-from-rp/m2/f2/adder-sum/and/or y)))
    (cond ((or x-is-and
               y-is-and)
           nil)
          (t (b* (((mv res &)
                   (lexorder2 y x)))
               res)))))

(defthmd sanity-of-adder-and$-order
  (implies (adder-and$-order x y)
           (not (adder-and$-order y x)))
  :hints (("Goal"
           :in-theory (e/d (LEXORDER2-SANITY
                            adder-and$-order) ()))))

(define adder-or$-order (x y)
  (b* ((x (ex-from-rp x))
       (y (ex-from-rp y))
       (x-is-or (case-match x (('adder-or & &) t)))
       (y-is-or (case-match y (('adder-or & &) t)))
       (x (ex-from-rp/m2/f2/adder-sum/and/or x))
       (y (ex-from-rp/m2/f2/adder-sum/and/or y)))
    (cond ((or x-is-or
               y-is-or)
           nil)
          (t (b* (((mv res &)
                   (lexorder2 x y)))
               res)))))

(defthmd sanity-of-adder-or$-order
  (implies (adder-or$-order x y)
           (not (adder-or$-order y x)))
  :hints (("Goal"
           :in-theory (e/d (LEXORDER2-SANITY
                            adder-or$-order) ()))))

(define adder-sum-order (x y)
  (b* ((x (ex-from-rp x))
       (y (ex-from-rp y))
       (x-is-const (or (case-match x (('quote &) t))
                       (integerp x)))
       (y-is-const (or (case-match y (('quote &) t))
                       (integerp y)))
       (x-is-m2 (case-match x (('m2 &) t)))
       (y-is-m2 (case-match y (('m2 &) t)))
       (x-is-f2 (case-match x (('f2 &) t)))
       (y-is-f2 (case-match y (('f2 &) t)))
       (x-is-adder (case-match x (('adder-b+ & &) t)))
       (y-is-adder (case-match y (('adder-b+ & &) t)))
       (x (ex-from-rp/m2/f2/adder-sum/and/or x))
       (y (ex-from-rp/m2/f2/adder-sum/and/or y)))
    (cond ((or x-is-adder
               y-is-adder)
           nil)
          ((or x-is-const
               y-is-const)
           (not y-is-const))
          ((or (and x-is-m2
                    y-is-m2)
               (and x-is-f2
                    y-is-f2))
           (b* (((mv res &)
                 (lexorder2 y x)))
             res))
          ((or x-is-m2
               y-is-m2)
           (not y-is-m2))
          ((or x-is-f2
               y-is-f2)
           (not x-is-f2))
          (t (b* (((mv res &)
                   (lexorder2 y x)))
               res)))))

(defthmd sanity-of-adder-sum-order
  (implies (adder-sum-order x y)
           (not (adder-sum-order y x)))
  :hints (("Goal"
           :in-theory (e/d (LEXORDER2-SANITY
                            adder-sum-order) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

(define resolve-adder-and-order-rec (x y)
  :measure (+ (cons-count x)
              (cons-count y))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig-x x)
       (orig-y y)
       (x (ex-from-rp x))
       (y (ex-from-rp y)))
    (case-match x
      (('adder-and x1 x2)
       (case-match y
         (('adder-and y1 y2)
          (cond ((not (adder-and$-order y1 x1))
                 (b* (((mv rest rest-dont-rw)
                       (resolve-adder-and-order-rec x2 orig-y)))
                   (mv `(adder-and ,x1 ,rest)
                       (list nil t rest-dont-rw))))
                (t
                 (b* (((mv rest rest-dont-rw)
                       (resolve-adder-and-order-rec orig-x y2)))
                   (mv `(adder-and ,y1 ,rest)
                       (list nil t rest-dont-rw))))))
         (& (cond ((not (adder-and$-order y x1))
                   (b* (((mv rest rest-dont-rw)
                         (resolve-adder-and-order-rec x2 orig-y)))
                     (mv `(adder-and ,x1 ,rest)
                         (list nil t rest-dont-rw))))
                  (t (mv `(adder-and ,orig-y ,orig-x)
                         (list nil t t)))))))
      (& (case-match y
           (('adder-and y1 y2)
            (cond ((not (adder-and$-order y1 x))
                   (mv `(adder-and ,orig-x ,orig-y)
                       (list nil t t)))
                  (t
                   (b* (((mv rest rest-dont-rw)
                         (resolve-adder-and-order-rec orig-x y2)))
                     (mv `(adder-and ,y1 ,rest)
                         (list nil t rest-dont-rw))))))
           (& (cond ((not (adder-and$-order y x))
                     (mv `(adder-and ,orig-x ,orig-y)
                         (list nil t t)))
                    (t (mv `(adder-and ,orig-y ,orig-x)
                           (list nil t t))))))))))

(define resolve-adder-sum-order-rec (x y)
  :measure (+ (cons-count x)
              (cons-count y))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig-x x)
       (orig-y y)
       (x (ex-from-rp x))
       (y (ex-from-rp y)))
    (case-match x
      (('adder-b+ x1 x2)
       (case-match y
         (('adder-b+ y1 y2)
          (cond ((not (adder-sum-order y1 x1))
                 (b* (((mv rest rest-dont-rw)
                       (resolve-adder-sum-order-rec x2 orig-y)))
                   (mv `(adder-b+ ,x1 ,rest)
                       (list nil t rest-dont-rw))))
                (t
                 (b* (((mv rest rest-dont-rw)
                       (resolve-adder-sum-order-rec orig-x y2)))
                   (mv `(adder-b+ ,y1 ,rest)
                       (list nil t rest-dont-rw))))))
         (& (cond ((not (adder-sum-order y x1))
                   (b* (((mv rest rest-dont-rw)
                         (resolve-adder-sum-order-rec x2 orig-y)))
                     (mv `(adder-b+ ,x1 ,rest)
                         (list nil t rest-dont-rw))))
                  (t (mv `(adder-b+ ,orig-y ,orig-x)
                         (list nil t t)))))))
      (& (case-match y
           (('adder-b+ y1 y2)
            (cond ((not (adder-sum-order y1 x))
                   (mv `(adder-b+ ,orig-x ,orig-y)
                       (list nil t t)))
                  (t
                   (b* (((mv rest rest-dont-rw)
                         (resolve-adder-sum-order-rec orig-x y2)))
                     (mv `(adder-b+ ,y1 ,rest)
                         (list nil t rest-dont-rw))))))
           (& (cond ((not (adder-sum-order y x))
                     (mv `(adder-b+ ,orig-x ,orig-y)
                         (list nil t t)))
                    (t (mv `(adder-b+ ,orig-y ,orig-x)
                           (list nil t t))))))))))

(define resolve-adder-and-order (term)
  (case-match term
    (('merge-adder-and x y)
     (b* (((mv res dont-rw) (resolve-adder-and-order-rec x y)))
       (mv res dont-rw)))
    (& (mv term nil))))

(define resolve-adder-sum-order (term)
  (case-match term
    (('merge-adder-b+ x y)
     (b* (((mv res dont-rw) (resolve-adder-sum-order-rec x y)))
       (mv res dont-rw)))
    (& (mv term nil))))

(encapsulate
  nil

  (local
   (in-theory (disable adder-and$-order
                       adder-sum-order
                       ex-from-rp
                       ex-from-rp-loose)))

  (def-formula-checks
    adder-rule-formula-checks
    (merge-adder-and
     merge-adder-b+
     adder-sum
     sum
     resolve-adder-and-order
     resolve-adder-sum-order)))


(local
 (in-theory (disable rp-trans
                     rp-evlt-of-ex-from-rp)))

(local
 (progn
   #|(defthm rp-syntaxp-resolve-adder-and-order-rec
     (implies (and (rp-syntaxp x)
                   (rp-syntaxp y))
              (rp-syntaxp (mv-nth 0 (resolve-adder-and-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order-rec) ()))))||#

   #|(defthm all-falist-consistent-resolve-adder-and-order-rec
     (implies (and (all-falist-consistent x)
                   (all-falist-consistent y))
              (all-falist-consistent (mv-nth 0 (resolve-adder-and-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order-rec) ()))))||#

   (defthm rp-termp-resolve-adder-and-order-rec
     (implies (and (rp-termp x)
                   (rp-termp y))
              (rp-termp (mv-nth 0 (resolve-adder-and-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order-rec) ()))))

   (defthm valid-sc-resolve-adder-and-order-rec
     (implies (and (valid-sc x a)
                   (valid-sc y a))
              (valid-sc (mv-nth 0 (resolve-adder-and-order-rec x y)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order-rec
                               is-if
                               is-rp) ()))))))

(local
 (progn
   #|(defthm rp-syntaxp-resolve-adder-sum-order-rec
     (implies (and (rp-syntaxp x)
                   (rp-syntaxp y))
              (rp-syntaxp (mv-nth 0 (resolve-adder-sum-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order-rec) ()))))||#

   #|(defthm all-falist-consistent-resolve-adder-sum-order-rec
     (implies (and (all-falist-consistent x)
                   (all-falist-consistent y))
              (all-falist-consistent (mv-nth 0 (resolve-adder-sum-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order-rec) ()))))||#

   (defthm rp-termp-resolve-adder-sum-order-rec
     (implies (and (rp-termp x)
                   (rp-termp y))
              (rp-termp (mv-nth 0 (resolve-adder-sum-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order-rec) ()))))

   (defthm valid-sc-resolve-adder-sum-order-rec
     (implies (and (valid-sc x a)
                   (valid-sc y a))
              (valid-sc (mv-nth 0 (resolve-adder-sum-order-rec x y)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order-rec
                               is-if
                               is-rp) ()))))))

(local
 (progn
   #|(defthm rp-syntaxp-resolve-adder-and-order
     (implies (and (rp-syntaxp x))
              (rp-syntaxp (mv-nth 0 (resolve-adder-and-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order) ()))))||#

   #|(defthm all-falist-consistent-resolve-adder-and-order
     (implies (and (all-falist-consistent x))
              (all-falist-consistent (mv-nth 0 (resolve-adder-and-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order) ()))))||#

   (defthm rp-termp-resolve-adder-and-order
     (implies (and (rp-termp x))
              (rp-termp (mv-nth 0 (resolve-adder-and-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order) ()))))

   (defthm valid-sc-resolve-adder-and-order
     (implies (and (valid-sc x a))
              (valid-sc (mv-nth 0 (resolve-adder-and-order x)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order
                               is-if
                               is-rp) ()))))))

(local
 (progn
   #|(defthm rp-syntaxp-resolve-adder-sum-order
     (implies (and (rp-syntaxp x))
              (rp-syntaxp (mv-nth 0 (resolve-adder-sum-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order) ()))))||#

   #|(defthm all-falist-consistent-resolve-adder-sum-order
     (implies (and (all-falist-consistent x))
              (all-falist-consistent (mv-nth 0 (resolve-adder-sum-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order) ()))))||#

   (defthm rp-termp-resolve-adder-sum-order
     (implies (and (rp-termp x))
              (rp-termp (mv-nth 0 (resolve-adder-sum-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order) ()))))

   (defthm valid-sc-resolve-adder-sum-order
     (implies (and (valid-sc x a))
              (valid-sc (mv-nth 0 (resolve-adder-sum-order x)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order
                               is-if
                               is-rp) ()))))))

(encapsulate
  nil

  (local
   (defthm and-comm
     (and (equal (and$ x y)
                 (and$ y x))
          (equal (and$ x y z)
                 (and$ y x z)))
     :hints (("Goal"
              :in-theory (e/d (and$) ())))))

  (local
   (defthmd rp-evlt-ex-from-rp-reverse
     (implies (syntaxp (atom x))
              (equal (rp-evlt x a)
                     (rp-evlt (ex-from-rp x) a)))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               rp-evlt-of-ex-from-rp) ())))))

  (local
   (defthmd eval-of-adder-and-1
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP y)
                   (EQUAL (CAR y) 'ADDER-AND)
                   (CONSP (CDR y))
                   (CONSP (CDDR y))
                   (NOT (CDDDR y)))
              (equal (rp-evlt y a)
                     (adder-and (RP-EVLT (CADR y) A)
                                (RP-EVLT (CADDR y) A))))
     :hints (("Goal"
              :in-theory (e/d ( rp-trans)
                              (ex-from-rp))))))

  (local
   (defthm eval-of-adder-and
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP (EX-FROM-RP Y))
                   (EQUAL (CAR (EX-FROM-RP Y)) 'ADDER-AND)
                   (CONSP (CDR (EX-FROM-RP Y)))
                   (CONSP (CDDR (EX-FROM-RP Y)))
                   (NOT (CDDDR (EX-FROM-RP Y))))
              (equal (rp-evlt y a)
                     (adder-and (RP-EVLT (CADR (EX-FROM-RP Y)) A)
                                (RP-EVLT (CADDR (EX-FROM-RP Y)) A))))
     :hints (("Goal"
              :in-theory (e/d (rp-evlt-ex-from-rp-reverse
                               rp-trans
                               eval-of-adder-and-1)
                              (ex-from-rp))))))

  (local
   (defthm rp-evl-resolve-adder-and-order-rec
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evlt (mv-nth 0 (resolve-adder-and-order-rec x y)) a)
                     (adder-and (rp-evlt x a)
                                (rp-evlt y a))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-and-order-rec
                               rp-trans
                               adder-and) ())))))

  (defthm rp-evl-resolve-adder-and-order
    (implies (and (adder-rule-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state))
             (equal (rp-evlt (mv-nth 0 (resolve-adder-and-order x)) a)
                    (rp-evlt x a)))
    :hints (("Goal"
             :in-theory (e/d (resolve-adder-and-order
                              rp-trans
                              merge-adder-and) ())))))

(encapsulate
  nil

  (local
   (defthm sum-comm
     (and (equal (sum x y)
                 (sum y x))
          (equal (sum x y z)
                 (sum y x z)))
     :hints (("Goal"
              :in-theory (e/d (sum) ())))))

  (local
   (defthmd rp-evlt-ex-from-rp-reverse
     (implies (syntaxp (atom x))
              (equal (rp-evlt x a)
                     (rp-evlt (ex-from-rp x) a)))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               rp-evlt-of-ex-from-rp) ())))))

  (local
   (in-theory (enable
               adder-sum
               merge-adder-b+)))

  (local
   (defthmd eval-of-adder-sum-1
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP y)
                   (EQUAL (CAR y) 'ADDER-b+)
                   (CONSP (CDR y))
                   (CONSP (CDDR y))
                   (NOT (CDDDR y)))
              (equal (rp-evlt y a)
                     (adder-sum (RP-EVLT (CADR y) A)
                                (RP-EVLT (CADDR y) A))))
     :hints (("Goal"
              :in-theory (e/d ( rp-trans)
                              (ex-from-rp
                               adder-sum))))))

  (local
   (defthm eval-of-adder-sum
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP (EX-FROM-RP Y))
                   (EQUAL (CAR (EX-FROM-RP Y)) 'ADDER-b+)
                   (CONSP (CDR (EX-FROM-RP Y)))
                   (CONSP (CDDR (EX-FROM-RP Y)))
                   (NOT (CDDDR (EX-FROM-RP Y))))
              (equal (rp-evlt y a)
                     (adder-sum (RP-EVLT (CADR (EX-FROM-RP Y)) A)
                                (RP-EVLT (CADDR (EX-FROM-RP Y)) A))))
     :hints (("Goal"
              :in-theory (e/d (rp-evlt-ex-from-rp-reverse
                               
                               eval-of-adder-sum-1)
                              (ex-from-rp))))))

  (local
   (defthm rp-evlt-resolve-adder-sum-order-rec
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evlt (mv-nth 0 (resolve-adder-sum-order-rec x y)) a)
                     (adder-sum (rp-evlt x a)
                                (rp-evlt y a))))
     :hints (("Goal"
              :in-theory (e/d (resolve-adder-sum-order-rec
                               rp-trans
                               adder-sum) ())))))

  (defthm rp-evl-resolve-adder-sum-order
    (implies (and (adder-rule-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state))
             (equal (rp-evlt (mv-nth 0 (resolve-adder-sum-order x)) a)
                    (rp-evlt x a)))
    :hints (("Goal"
             :in-theory (e/d (resolve-adder-sum-order
                              rp-trans
                              merge-adder-b+) ())))))

(local
 (defthm dont-rw-syntaxp-resolve-adder-and-order
   (dont-rw-syntaxp (mv-nth 1 (resolve-adder-and-order term)))
   :hints (("Goal"
            :in-theory (e/d (resolve-adder-and-order
                             resolve-adder-and-order-rec) ())))))

(local
 (defthm dont-rw-syntaxp-resolve-adder-sum-order
   (dont-rw-syntaxp (mv-nth 1 (resolve-adder-sum-order term)))
   :hints (("Goal"
            :in-theory (e/d (resolve-adder-sum-order
                             resolve-adder-sum-order-rec) ())))))

(defthm resolve-adder-and-order-is-valid-rp-meta-rulep
  (implies (and (adder-rule-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'resolve-adder-and-order
                             :trig-fnc 'merge-adder-and
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            
                            
                            VALID-SC)))))

(defthm resolve-adder-sum-order-is-valid-rp-meta-rulep
  (implies (and (adder-rule-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'resolve-adder-sum-order
                             :trig-fnc 'merge-adder-b+
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            
                            
                            VALID-SC)))))

(rp::add-meta-rules
 adder-rule-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'resolve-adder-and-order
        :trig-fnc 'merge-adder-and
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 'resolve-adder-sum-order
        :trig-fnc 'merge-adder-b+
        :dont-rw t
        :valid-syntax t)))
