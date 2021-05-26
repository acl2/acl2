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
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

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
    (('-- x)
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
       (?x-is-bit-of (case-match x (('bit-of a &) (atom (ex-from-rp a)))))
       (?y-is-bit-of (case-match y (('bit-of a &) (atom (ex-from-rp a)))))
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
       (?x-is-bit-of (case-match x (('bit-of a &) (atom (ex-from-rp a)))))
       (?y-is-bit-of (case-match y (('bit-of a &) (atom (ex-from-rp a)))))
       (x (ex-from-rp/m2/f2/adder-sum/and/or x))
       (y (ex-from-rp/m2/f2/adder-sum/and/or y)))
    (cond ((or x-is-or
               y-is-or)
           nil)
          (t (b* (((mv res &)
                   (lexorder2 y x)))
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
       (x (case-match x (('-- arg) (ex-from-rp arg)) (& x)))
       (y (case-match y (('-- arg) (ex-from-rp arg)) (& y)))
       (x-is-m2 (case-match x (('m2 &) t)))
       (y-is-m2 (case-match y (('m2 &) t)))
       (x-is-f2 (case-match x (('f2 &) t)))
       (y-is-f2 (case-match y (('f2 &) t)))
       (x-is-adder (case-match x (('adder-b+ & &) t)))
       (y-is-adder (case-match y (('adder-b+ & &) t)))
       (?x-is-bit-of (case-match x (('bit-of a &) (atom (ex-from-rp a)))))
       (?y-is-bit-of (case-match y (('bit-of a &) (atom (ex-from-rp a)))))
       (x-before-heavy-ex x)
       (y-before-heavy-ex y)
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
                 (lexorder2 y-before-heavy-ex x-before-heavy-ex)))
             res))
          ((or x-is-m2
               y-is-m2)
           (not y-is-m2))
          ((or x-is-f2
               y-is-f2)
           (not x-is-f2))
          #|((and x-is-bit-of
          y-is-bit-of
          (equal (caddr x) (caddr y))
          )
          (b* (((mv res &)
          (lexorder2 x y)))
          res))||#
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
     adder-mux
     adder-or
     f2
     m2
     adder-and
     adder-b+
     bitp
     bit-of)))

(local
 (in-theory (disable rp-trans
                     rp-evlt-of-ex-from-rp)))

(local
 (progn
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
                   (consp y)
                   (equal (car y) 'adder-b+)
                   (consp (cdr y))
                   (consp (cddr y))
                   (not (cdddr y)))
              (equal (rp-evlt y a)
                     (adder-sum (rp-evlt (cadr y) a)
                                (rp-evlt (caddr y) a))))
     :hints (("goal"
              :in-theory (e/d ( rp-trans)
                              (ex-from-rp
                               adder-sum))))))

  (local
   (defthm eval-of-adder-sum
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (consp (ex-from-rp y))
                   (equal (car (ex-from-rp y)) 'adder-b+)
                   (consp (cdr (ex-from-rp y)))
                   (consp (cddr (ex-from-rp y)))
                   (not (cdddr (ex-from-rp y))))
              (equal (rp-evlt y a)
                     (adder-sum (rp-evlt (cadr (ex-from-rp y)) a)
                                (rp-evlt (caddr (ex-from-rp y)) a))))
     :hints (("goal"
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

(rp::add-meta-rule
 :meta-fnc resolve-adder-and-order
 :trig-fnc merge-adder-and
 :valid-syntaxp t
 :formula-checks adder-rule-formula-checks ;
 :returns (mv term dont-rw))
(rp::add-meta-rule
 :meta-fnc resolve-adder-sum-order
 :trig-fnc merge-adder-b+
 :valid-syntaxp t
 :formula-checks adder-rule-formula-checks
 :returns (mv term dont-rw))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; adder-mux-meta

(define is-bit-of (x)
  (b* ((x (ex-from-rp x)))
    (case-match x
      (('bit-of & &)
       t))))

(define insert-select-from-adder-mux (s i0 i1)
  :returns (mv (res-term rp-termp
                         :hyp (and (rp-termp s)
                                   (rp-termp i0)
                                   (rp-termp i1))
                         :hints (("Goal"
                                  :in-theory (e/d (is-rp) ()))))
               dont-rw
               (success booleanp))
  (b* (;;(i0 (ex-from-rp i0))
       ;;(i1 (ex-from-rp i1))
       ((mv i0-is-f2 i0-arg1 i0-arg2)
        (case-match i0
          (('f2 ('adder-b+ arg1 arg2))
           (mv  t arg1 arg2))
          (& (mv nil nil nil))))
       ((mv i1-is-adder-or  i1-arg1 i1-arg2)
        (case-match i1
          (('adder-or arg1 arg2)
           (mv t  arg1 arg2))
          (& (mv nil  nil nil)))))
    (cond ((and i1-is-adder-or
                i0-is-f2
                (or (is-bit-of i0-arg1)
                    (is-rp-bitp i0-arg1))
                (or (is-bit-of i1-arg1)
                    (is-rp-bitp i1-arg1))
                (or (is-bit-of i0-arg2)
                    (is-rp-bitp i0-arg2))
                (or (is-bit-of i1-arg2)
                    (is-rp-bitp i1-arg2))
                (or (and (rp-equal i1-arg1 i0-arg1)
                         (rp-equal i1-arg2 i0-arg2))
                    (and (rp-equal i1-arg1 i0-arg2)
                         (rp-equal i1-arg2 i0-arg1))))
           (mv `(rp 'bitp
                    (f2 (merge-adder-b+
                         ,s (merge-adder-b+ ,i0-arg1 ,i0-arg2))))
               `(nil nil (nil (nil t (nil t t))))
               t))
          (t (mv ''nil nil nil)))))


(acl2::defines
 adder-mux-meta-aux
 :flag-defthm-macro defthm-adder-mux-meta-aux
 :flag-local nil

 :hints (("Goal"
          :in-theory (e/d (measure-lemmas)
                          ())))
 :guard-hints (("Goal"
                :in-theory (e/d (is-rp) ())))

 (define adder-mux-meta-aux (s i0 i1)
   :returns (mv res-term
                dont-rw
                (success booleanp))
   :measure (cons-count i0)
   (b* (;;(i0-side-cond  (get-first-side-cond i0))
        (i0 (ex-from-rp i0))
        (i1 (ex-from-rp i1)))
     (cond ((or (atom i0)
                (quotep i0)
                (atom i1)
                (quotep i1)
                (eq (car i0) 'falist) ;; just to make the proofs easy
                (eq (car i1) 'falist)
                (is-if i0) ;; just to make the proofs easy
                (is-if i1)
                )
            (if (equal i0 i1)
                (mv i0 t t)
              (mv ''nil t nil)))
           ((equal (car i0) (car i1))
            (b* (((mv args args-dont-rw args-success)
                  (adder-mux-meta-aux-lst s (cdr i0) (cdr i1)))
                 ((unless args-success)
                  (mv ''nil t nil)))
              (mv `(,(car i0) . ,args)
                  `(nil . ,args-dont-rw)
                  t)))
           ;;)
           (t (insert-select-from-adder-mux s i0 i1)))))

 (define adder-mux-meta-aux-lst (s i0-lst i1-lst)
   :returns (mv res-term-lst
                dont-rw-lst
                (success booleanp))
   :measure (cons-count i0-lst)
   (if (or (atom i0-lst)
           (atom i1-lst))
       (mv i0-lst nil (equal i0-lst i1-lst))
     (b* (((mv cur-term cur-dont-rw cur-success)
           (adder-mux-meta-aux s (car i0-lst) (car i1-lst)))
          ((unless cur-success)
           (mv nil nil nil))
          ((mv rest-lst rest-dont-rw rest-success)
           (adder-mux-meta-aux-lst s (cdr i0-lst) (cdr i1-lst)))
          ((unless rest-success)
           (mv nil nil nil)))
       (mv (cons-with-hint cur-term rest-lst i0-lst)
           (cons cur-dont-rw rest-dont-rw)
           t)))))

(define adder-mux-meta (term)
  :returns (mv res-term
               dont-rw)
  (case-match term
    (('adder-mux s i0 i1)
     (b* (((unless (and (or (is-rp-bitp s)
                            (is-bit-of s)
                            (m2-p s))
                        (or (is-rp-bitp i0)
                            (is-bit-of i0)
                            (m2-p i0))
                        (or (is-rp-bitp i1)
                            (is-bit-of i1)
                            (m2-p i1))))
           (mv term nil))
          ((mv res-term dont-rw success)
           (adder-mux-meta-aux s i0 i1)))
       (if success
           (mv `(rp 'bitp ,res-term) `(nil nil ,dont-rw))
         (mv term nil))))
    (& (mv term nil))))

(local
 (defthm is-rp-adder-mux-meta-aux-returns-rp-termp-lemma
   (implies (and (EQUAL (CAR I0) 'RP)
                 (RP-TERMP I0))
            (IS-RP (LIST 'RP (CADR I0) other)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(defret-mutual
  adder-mux-meta-aux-returns-rp-termp
  (defret adder-mux-meta-aux-returns-rp-termp
    (implies (and (rp-termp i0)
                  (rp-termp i1)
                  (rp-termp s))
             (rp-termp res-term))
    :fn adder-mux-meta-aux)
  (defret adder-mux-meta-aux-lst-returns-rp-term-listp
    (implies (and (rp-term-listp i0-lst)
                  (rp-term-listp i1-lst)
                  (rp-termp s))
             (rp-term-listp res-term-lst))
    :fn adder-mux-meta-aux-lst)
  :hints (("goal"
           :expand ((:free (x) (is-rp `(rp 'bitp ,x))))
           :in-theory (e/d (adder-mux-meta-aux-lst
                            is-rp
                            adder-mux-meta-aux
                            ;;GET-FIRST-SIDE-COND
                            )
                           ((:definition falist-consistent))))))

(local
 (defthm is-rp-of-MERGE-ADDER-B+
   (not (is-rp `(MERGE-ADDER-B+ . , x)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm is-rp-of-f2
   (not (is-rp `(f2 . , x)))
   :hints (("Goal"
            :in-theory (e/d (is-rp) ())))))

(local
 (encapsulate
   nil
   (local
    (in-theory (e/d (rp-trans)
                    (bitp))))

   (create-regular-eval-lemma bitp 1 adder-rule-formula-checks)
   (create-regular-eval-lemma rp 2 adder-rule-formula-checks)
   (create-regular-eval-lemma bit-of 2 adder-rule-formula-checks)
   (create-regular-eval-lemma f2 1 adder-rule-formula-checks)
   (create-regular-eval-lemma m2 1 adder-rule-formula-checks)
   (create-regular-eval-lemma adder-mux 3 adder-rule-formula-checks)
   (create-regular-eval-lemma merge-adder-b+ 2 adder-rule-formula-checks)
   (create-regular-eval-lemma ADDER-B+ 2 adder-rule-formula-checks)
   (create-regular-eval-lemma ADDER-or 2 adder-rule-formula-checks)))

(local
 (defthmd bitp-of-f2-with-merge-adder-sum
   (implies (and (bitp x)
                 (bitp y)
                 (bitp z))
            (bitp (F2 (MERGE-ADDER-SUM x y z))))))

(local
 (defthm valid-sc-subterms-of-cdr
   (implies (and (consp x)
                 (not (is-if x))
                 (NOT (EQUAL (CAR x) 'quote))
                 (NOT (is-rp x))
                 (VALID-SC x A))
            (VALID-SC-SUBTERMS (CDR x) A))
   :hints (("Goal"
            :expand (VALID-SC x A)
            :in-theory (e/d (is-rp is-if) ())))))

(local
 (defthm not-is-rp-ex-from-rp
   (NOT (IS-RP (EX-FROM-RP I1)))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp) ())))))

(local
 (defthm is-bit-of-implies-bitp
   (implies (and (adder-rule-formula-checks state)
                 (rp-evl-meta-extract-global-facts :state state)
                 (is-bit-of term))
            (bitp (rp-evlt term a)))
   :hints (("Goal"
            :in-theory (e/d* (is-bit-of
                              regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (bitp))))))

(local
 (defthm IS-RP-BITP-implies-bitp
   (implies (and (adder-rule-formula-checks state)
                 (rp-evl-meta-extract-global-facts :state state)
                 (is-rp-bitp term)
                 (valid-sc term a))
            (bitp (rp-evlt term a)))
   :hints (("Goal"

            :in-theory (e/d* (is-rp-bitp
                              is-if
                              is-rp
                              valid-sc-single-step
                              regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (bitp))))))

(defret insert-select-from-adder-mux-returns-valid-sc
  (implies (and (valid-sc i0 a)
                (valid-sc i1 a)
                (valid-sc s a)
                (bitp (rp-evlt s a))
                (adder-rule-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (valid-sc res-term a))
  :fn insert-select-from-adder-mux
  :hints (("goal"
           :do-not-induct t
           :in-theory (e/d* (insert-select-from-adder-mux
                             is-if
                             bitp-of-f2-with-merge-adder-sum
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp
                             context-from-rp
                             is-rp)
                            (bitp)))))


(local
 (defthm adder-mux-meta-aux-returns-valid-sc-lemma1
   (implies (and (CONSP I0)
                 (NOT (CADR I0))
                 (CONSP (CDR I0))
                 (not (EQUAL (CAR I0) 'QUOTE)))
            (not (rp-termp i0)))
   :hints (("Goal"
            :in-theory (e/d (rp-termp is-rp) ())))))

(local

 (defthm is-rp-of-cons-ex-from-rp
   (implies (and (rp-termp i0))
            (not (is-rp (cons (car (ex-from-rp i0)) other))))
   :hints (("Goal"
            :in-theory (e/d (rp-termp
                             is-rp)
                            ())))))


(defret-mutual
  adder-mux-meta-aux-returns-valid-sc
  (defret adder-mux-meta-aux-returns-valid-sc
    (implies (and (valid-sc i0 a)
                  (valid-sc i1 a)
                  (valid-sc s a)
                  (bitp (rp-evlt s a))
                  (adder-rule-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-termp i0)
                  (rp-termp i1)
                  (rp-termp s)
                  success
                  )
             (valid-sc res-term a))
    :fn adder-mux-meta-aux)
  (defret adder-mux-meta-aux-lst-returns-valid-sc-subterms
    (implies (and (valid-sc-subterms i0-lst a)
                  (valid-sc-subterms i1-lst a)
                  (valid-sc s a)
                  (bitp (rp-evlt s a))
                  (adder-rule-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-term-listp i0-lst)
                  (rp-term-listp i1-lst)
                  (rp-termp s)
                  success
                  )
             (valid-sc-subterms res-term-lst a))
    :fn adder-mux-meta-aux-lst)
  :hints (("goal"
           :do-not-induct t
           :expand ((:free (x y) (context-from-rp `(merge-adder-b+ . ,x) y))
                    (:free (x y) (context-from-rp `(f2 . ,x) y))
                    (:free (x y) (context-from-rp `(rp . ,x) y))
                    (:free (x y) (valid-sc (cons x y) a)))
           :in-theory (e/d* (adder-mux-meta-aux-lst
                             bitp-of-f2-with-merge-adder-sum
                             adder-mux-meta-aux
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp
                             ;;is-rp
                             ;;is-if
                             )
                            (bitp
                             ;;rp-term-listp
                             rp-termp)))))

(defret adder-mux-meta-returns-rp-termp
  (implies (rp-termp term)
           (rp-termp res-term))
  :fn ADDER-MUX-META
  :hints (("Goal"
           :in-theory (e/d (ADDER-MUX-META
                            is-rp)
                           ()))))

(local
 (defthmd bitp-of-f2-with-+
   (and (implies (and (bitp x)
                      (bitp y))
                 (bitp (f2 (+ x y ))))
        (implies (and (bitp x)
                      (bitp y))
                 (bitp (f2 (+ 1 x y))))
        (implies (and (bitp x))
                 (equal (f2 x)
                        0)))))

(local
 (defthmd adder-or$-to-f2
   (implies (and (bitp x)
                 (bitp y))
            (equal (adder-or$ x y)
                   (f2 (+ 1 x y))))))

(local
 (defthmd bitp-implies-integerp
   (implies (bitp x)
            (integerp x))))

(local
 (defthmd integerp-of-sum
   (implies (and (integerp x)
                 (integerp y))
            (integerp (+ x y)))))

(defret insert-select-from-adder-mux-correct
  (implies (and (valid-sc i0 a)
                (valid-sc i1 a)
                (valid-sc s a)
                (bitp (rp-evlt s a))
                (adder-rule-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state)
                (rp-termp i0)
                (rp-termp i1)
                (rp-termp s)
                success)
           (equal (rp-evlt res-term a)
                  (if (equal (rp-evlt s a) 0)
                      (rp-evlt i0 a)
                    (rp-evlt i1 a))))
  :fn insert-select-from-adder-mux
  :hints (("goal"
           :in-theory (e/d* (insert-select-from-adder-mux
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             merge-adder-sum
                             adder-mux
                             adder-sum
                             bitp-of-f2-with-+
                             adder-or$-to-f2
                             bitp-implies-integerp
                             integerp-of-sum
                             bit-fix)
                            (bitp
                             (:rewrite default-cdr)
                             ex-from-rp
                             valid-sc
                             (:definition eval-and-all)
                             rp-termp)))))


(defun two-list-induct (lst1 lst2)
  (cond ((atom lst1)
         nil)
        ((atom lst2)
         nil)
        (t (two-list-induct (cdr lst1) (cdr lst2)))))

(local
 (defthmd adder-mux-meta-aux-is-correct-lemma1
   (implies (and (equal (rp-evlt-lst lst1 a)
                        (rp-evlt-lst lst2 a)))
            (equal (rp-evl (trans-list (rp-trans-lst lst1)) a)
                   (rp-evl (trans-list (rp-trans-lst lst2)) a)))
   :rule-classes :forward-chaining
   :hints (("goal"
            ;;:do-not-induct t
            :induct (two-list-induct lst1 lst2)
            :expand ((rp-trans-lst lst1)
                     (rp-trans-lst lst2)
                     (trans-list (cons (rp-trans (car lst1))
                                       (rp-trans-lst (cdr lst1))))
                     (trans-list (cons (rp-trans (car lst2))
                                       (rp-trans-lst (cdr lst2)))))
            :in-theory (e/d (rp-trans
                             rp-trans-lst
                             ;;trans-list
                             )
                            (trans-list))))))

(defret-mutual
  adder-mux-meta-aux-is-correct
  (defret adder-mux-meta-aux-is-correct
    (implies (and (valid-sc i0 a)
                  (valid-sc i1 a)
                  (valid-sc s a)
                  (bitp (rp-evlt s a))
                  (adder-rule-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-termp i0)
                  (rp-termp i1)
                  (rp-termp s)
                  success)
             (equal (rp-evlt res-term a)
                    (if (equal (rp-evlt s a) 0)
                        (rp-evlt i0 a)
                      (rp-evlt i1 a))))
    :fn adder-mux-meta-aux)
  (defret adder-mux-meta-aux-lst-is-correct
    (implies (and (valid-sc-subterms i0-lst a)
                  (valid-sc-subterms i1-lst a)
                  (valid-sc s a)
                  (bitp (rp-evlt s a))
                  (adder-rule-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-term-listp i0-lst)
                  (rp-term-listp i1-lst)
                  (rp-termp s)
                  success)
             (equal (rp-evlt-lst res-term-lst a)
                    (if (equal (rp-evlt s a) 0)
                        (rp-evlt-lst i0-lst a)
                      (rp-evlt-lst i1-lst a))))
    :fn adder-mux-meta-aux-lst)
  :hints (("goal"
           :do-not-induct t

           :in-theory (e/d* (adder-mux-meta-aux-is-correct-lemma1
                             adder-mux-meta-aux-lst
                             adder-mux-meta-aux
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp
                             adder-mux
                             rp-evlt-of-ex-from-rp-reverse-for-atom
                             rp-evl-of-fncall-args
                             rp-trans)
                            (bitp
                             rp-trans-is-term-when-list-is-absent
                             ;;rp-evl-of-variable
                             ;;rp-trans
                             ;;rp-term-listp
                             rp-termp)))))


(local
 (encapsulate
   nil
   (local
    (include-book "lemmas"))
   
   (defthm m2-p-implies-bitp
     (implies (and (adder-rule-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (m2-p term))
              (bitp (rp-evlt term a)))
     :hints (("Goal"
              :in-theory (e/d* (regular-eval-lemmas
                                regular-eval-lemmas-with-ex-from-rp)
                               (bitp)))))

   (defthm bit-m2-local
     (bitp (m2 x)))
   
   ))

(defret adder-mux-meta-returns-valid-sc
  (implies (and (valid-sc term a)
                (adder-rule-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state)
                (rp-termp term))
           (valid-sc res-term a))
  :fn adder-mux-meta
  :hints (("goal"
           :in-theory (e/d* (adder-mux-meta
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas
                             is-rp
                             valid-sc-single-step
                             is-if)
                            (bitp
                             ;;(:definition valid-sc)
                             (:definition ex-from-rp)
                             (:rewrite default-cdr)
                             (:definition eval-and-all)
                             (:rewrite valid-sc-cadr)
                             (:rewrite valid-sc-caddr)
                             (:rewrite valid-sc-cadddr)
                             (:rewrite default-car)
                             (:rewrite acl2::o-p-o-infp-car)
                             rp-termp)))))

(defret adder-mux-meta-is-correct
  (implies (and (valid-sc term a)
                (rp-termp term)
                (adder-rule-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (equal (rp-evlt res-term a)
                  (rp-evlt term a)))
  :fn adder-mux-meta
  :hints (("Goal"
           :in-theory (e/d* (adder-mux-meta
                             regular-eval-lemmas-with-ex-from-rp
                             adder-mux
                             regular-eval-lemmas)
                            ()))))


(rp::add-meta-rule
 :meta-fnc adder-mux-meta
 :trig-fnc adder-mux
 :valid-syntaxp t
 :formula-checks adder-rule-formula-checks ;
 :returns (mv term dont-rw))
