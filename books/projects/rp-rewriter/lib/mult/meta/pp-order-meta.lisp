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

(include-book "../binary-fn-defs")

(include-book "../mult-defs")

(include-book "../macros")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(include-book "pp-order-fncs")

(local
 (in-theory (disable binary-and
                     rp-equal-cnt)))

(define search-pp-ands-for-negation-aux (term neg-flag x)
  (b* ((x (ex-from-rp x)))
    (case-match x
      (('binary-and x1 x2)
       (b* ((x1 (ex-from-rp x1)))
         (case-match x1
           (('binary-not sub)
            (if neg-flag
                (search-pp-ands-for-negation-aux term neg-flag x2)
              (or (rp-equal-cnt term sub -1)
                  (search-pp-ands-for-negation-aux term neg-flag x2))))
           (& (if (not neg-flag)
                  (search-pp-ands-for-negation-aux term neg-flag x2)
                (or (rp-equal-cnt term x1 -1)
                    (search-pp-ands-for-negation-aux term neg-flag x2)))))))
      (('binary-not sub)
       (if neg-flag nil (rp-equal-cnt term sub -1)))
      (&
       (if (not neg-flag) nil (rp-equal-cnt term x -1))))))

(define search-pp-ands-for-negation (x y)
  (b* ((x (ex-from-rp x)))
    (case-match x
      (('binary-and x1 x2)
       (b* ((x1 (ex-from-rp x1)))
         (case-match x1
           (('binary-not sub)
            (or (search-pp-ands-for-negation-aux sub t y)
                (search-pp-ands-for-negation x2 y)))
           (& (or (search-pp-ands-for-negation-aux x1 nil y)
                  (search-pp-ands-for-negation x2 y))))))
      (('binary-not sub)
       (search-pp-ands-for-negation-aux sub t y))
      (& (search-pp-ands-for-negation-aux x nil y)))))

(define resolve-pp-and-order-rec (x y)
  :measure (+ (cons-count x)
              (cons-count y))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig-x x)
       (orig-y y)
       (x (ex-from-rp x))
       (y (ex-from-rp y)))
    (case-match x
      (('binary-and x1 x2)
       (case-match y
         (('binary-and y1 y2)
          (cond
           ((rp-equal-cnt x1 y1 -1)
            (resolve-pp-and-order-rec x2 orig-y))
           ((not (pp-and$-order y1 x1))
            (b* (((mv rest rest-dont-rw)
                  (resolve-pp-and-order-rec x2 orig-y)))
              (mv `(binary-and ,x1 ,rest)
                  (list nil t rest-dont-rw))))
           (t
            (b* (((mv rest rest-dont-rw)
                  (resolve-pp-and-order-rec orig-x y2)))
              (mv `(binary-and ,y1 ,rest)
                  (list nil t rest-dont-rw))))))
         (& (cond
             ((rp-equal-cnt x1 y -1)
              (mv orig-x t))
             ((not (pp-and$-order y x1))
              (b* (((mv rest rest-dont-rw)
                    (resolve-pp-and-order-rec x2 orig-y)))
                (mv `(binary-and ,x1 ,rest)
                    (list nil t rest-dont-rw))))
             (t (mv `(binary-and ,orig-y ,orig-x)
                    (list nil t t)))))))
      (& (case-match y
           (('binary-and y1 y2)
            (cond ((rp-equal-cnt x y1 -1)
                   (mv orig-y t))
                  ((not (pp-and$-order y1 x))
                   (mv `(binary-and ,orig-x ,orig-y)
                       (list nil t t)))
                  (t
                   (b* (((mv rest rest-dont-rw)
                         (resolve-pp-and-order-rec orig-x y2)))
                     (mv `(binary-and ,y1 ,rest)
                         (list nil t rest-dont-rw))))))
           (& (cond ((rp-equal-cnt x y -1)
                     (mv `(bit-fix ,x) `(nil t)))
                    ((not (pp-and$-order y x))
                     (mv `(binary-and ,orig-x ,orig-y)
                         (list nil t t)))
                    (t (mv `(binary-and ,orig-y ,orig-x)
                           (list nil t t))))))))))

(define resolve-pp-and-order (term)
  (case-match term
    (('merge-pp-and x y)
     (if (search-pp-ands-for-negation x y)
         (mv ''0 t)
       (b* (((mv res dont-rw) (resolve-pp-and-order-rec x y)))
         (mv res dont-rw))))
    (& (mv term nil))))

(define resolve-pp-or-order-rec (x y)
  :measure (+ (cons-count x)
              (cons-count y))
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig-x x)
       (orig-y y)
       (x (ex-from-rp x))
       (y (ex-from-rp y)))
    (case-match x
      (('binary-or x1 x2)
       (case-match y
         (('binary-or y1 y2)
          (cond ((not (pp-or$-order y1 x1))
                 (b* (((mv rest rest-dont-rw)
                       (resolve-pp-or-order-rec x2 orig-y)))
                   (mv `(binary-or ,x1 ,rest)
                       (list nil t rest-dont-rw))))
                (t
                 (b* (((mv rest rest-dont-rw)
                       (resolve-pp-or-order-rec orig-x y2)))
                   (mv `(binary-or ,y1 ,rest)
                       (list nil t rest-dont-rw))))))
         (& (cond ((not (pp-or$-order y x1))
                   (b* (((mv rest rest-dont-rw)
                         (resolve-pp-or-order-rec x2 orig-y)))
                     (mv `(binary-or ,x1 ,rest)
                         (list nil t rest-dont-rw))))
                  (t (mv `(binary-or ,orig-y ,orig-x)
                         (list nil t t)))))))
      (& (case-match y
           (('binary-or y1 y2)
            (cond ((not (pp-or$-order y1 x))
                   (mv `(binary-or ,orig-x ,orig-y)
                       (list nil t t)))
                  (t
                   (b* (((mv rest rest-dont-rw)
                         (resolve-pp-or-order-rec orig-x y2)))
                     (mv `(binary-or ,y1 ,rest)
                         (list nil t rest-dont-rw))))))
           (& (cond ((not (pp-or$-order y x))
                     (mv `(binary-or ,orig-x ,orig-y)
                         (list nil t t)))
                    (t (mv `(binary-or ,orig-y ,orig-x)
                           (list nil t t))))))))))

(define resolve-pp-or-order (term)
  (case-match term
    (('merge-pp-or x y)
     (b* (((mv res dont-rw) (resolve-pp-or-order-rec x y)))
       (mv res dont-rw)))
    (& (mv term nil))))

(encapsulate
  nil

  (local
   (in-theory (disable pp-and$-order
                       pp-or$-order
                       ex-from-rp
                       ex-from-rp-loose)))

  (def-formula-checks
    pp-formula-checks
    (merge-pp-and
     merge-pp-or
     binary-not
     binary-and
     resolve-pp-and-order
     resolve-pp-or-order)))

(local
 (progn
   (defthm rp-syntaxp-resolve-pp-and-order-rec
     (implies (and (rp-syntaxp x)
                   (rp-syntaxp y))
              (rp-syntaxp (mv-nth 0 (resolve-pp-and-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order-rec) ()))))

   (defthm all-falist-consistent-resolve-pp-and-order-rec
     (implies (and (all-falist-consistent x)
                   (all-falist-consistent y))
              (all-falist-consistent (mv-nth 0 (resolve-pp-and-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order-rec) ()))))

   (defthm pseudo-termp2-resolve-pp-and-order-rec
     (implies (and (pseudo-termp2 x)
                   (pseudo-termp2 y))
              (pseudo-termp2 (mv-nth 0 (resolve-pp-and-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order-rec) ()))))

   (defthm valid-sc-resolve-pp-and-order-rec
     (implies (and (valid-sc x a)
                   (valid-sc y a))
              (valid-sc (mv-nth 0 (resolve-pp-and-order-rec x y)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order-rec
                               is-if
                               is-rp) ()))))))

(local
 (progn
   (defthm rp-syntaxp-resolve-pp-or-order-rec
     (implies (and (rp-syntaxp x)
                   (rp-syntaxp y))
              (rp-syntaxp (mv-nth 0 (resolve-pp-or-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order-rec) ()))))

   (defthm all-falist-consistent-resolve-pp-or-order-rec
     (implies (and (all-falist-consistent x)
                   (all-falist-consistent y))
              (all-falist-consistent (mv-nth 0 (resolve-pp-or-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order-rec) ()))))

   (defthm pseudo-termp2-resolve-pp-or-order-rec
     (implies (and (pseudo-termp2 x)
                   (pseudo-termp2 y))
              (pseudo-termp2 (mv-nth 0 (resolve-pp-or-order-rec x y))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order-rec) ()))))

   (defthm valid-sc-resolve-pp-or-order-rec
     (implies (and (valid-sc x a)
                   (valid-sc y a))
              (valid-sc (mv-nth 0 (resolve-pp-or-order-rec x y)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order-rec
                               is-if
                               is-rp) ()))))))

(local
 (progn
   (defthm rp-syntaxp-resolve-pp-and-order
     (implies (and (rp-syntaxp x))
              (rp-syntaxp (mv-nth 0 (resolve-pp-and-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order) ()))))

   (defthm all-falist-consistent-resolve-pp-and-order
     (implies (and (all-falist-consistent x))
              (all-falist-consistent (mv-nth 0 (resolve-pp-and-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order) ()))))

   (defthm pseudo-termp2-resolve-pp-and-order
     (implies (and (pseudo-termp2 x))
              (pseudo-termp2 (mv-nth 0 (resolve-pp-and-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order) ()))))

   (defthm valid-sc-resolve-pp-and-order
     (implies (and (valid-sc x a))
              (valid-sc (mv-nth 0 (resolve-pp-and-order x)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-and-order
                               is-if
                               is-rp) ()))))))

(local
 (progn
   (defthm rp-syntaxp-resolve-pp-or-order
     (implies (and (rp-syntaxp x))
              (rp-syntaxp (mv-nth 0 (resolve-pp-or-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order) ()))))

   (defthm all-falist-consistent-resolve-pp-or-order
     (implies (and (all-falist-consistent x))
              (all-falist-consistent (mv-nth 0 (resolve-pp-or-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order) ()))))

   (defthm pseudo-termp2-resolve-pp-or-order
     (implies (and (pseudo-termp2 x))
              (pseudo-termp2 (mv-nth 0 (resolve-pp-or-order x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order) ()))))

   (defthm valid-sc-resolve-pp-or-order
     (implies (and (valid-sc x a))
              (valid-sc (mv-nth 0 (resolve-pp-or-order x)) a))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order
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
   (defthmd rp-evl-ex-from-rp-reverse
     (implies (syntaxp (atom x))
              (equal (rp-evl x a)
                     (rp-evl (ex-from-rp x) a)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthmd eval-of-pp-and-1
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP y)
                   (EQUAL (CAR y) 'binary-AND)
                   (CONSP (CDR y))
                   (CONSP (CDDR y))
                   (NOT (CDDDR y)))
              (equal (rp-evl y a)
                     (binary-AND (RP-EVL (CADR y) A)
                                 (RP-EVL (CADDR y) A))))
     :hints (("Goal"
              :in-theory (e/d ( )
                              (ex-from-rp))))))

  (local
   (defthm eval-of-pp-and
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP (EX-FROM-RP Y))
                   (EQUAL (CAR (EX-FROM-RP Y)) 'binary-AND)
                   (CONSP (CDR (EX-FROM-RP Y)))
                   (CONSP (CDDR (EX-FROM-RP Y)))
                   (NOT (CDDDR (EX-FROM-RP Y))))
              (equal (rp-evl y a)
                     (binary-AND (RP-EVL (CADR (EX-FROM-RP Y)) A)
                                 (RP-EVL (CADDR (EX-FROM-RP Y)) A))))
     :hints (("Goal"
              :in-theory (e/d (rp-evl-ex-from-rp-reverse
                               eval-of-pp-and-1)
                              (ex-from-rp))))))

  (local
   (defthm lemma1
     (implies (not (EX-FROM-RP X))
              (equal (RP-EVL X A) nil))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp is-rp)
                              (NOT-INCLUDE-RP
                               EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma2
     (and
      (equal (RP-EQUAL (EX-FROM-RP X) y)
             (RP-EQUAL X y))
      (equal (RP-EQUAL y (EX-FROM-RP X))
             (RP-EQUAL y X)))
     :hints (("Goal"
              :do-not-induct t
              :expand ((RP-EQUAL (EX-FROM-RP X) y)
                       (RP-EQUAL Y (EX-FROM-RP X))
                       (RP-EQUAL x (EX-FROM-RP Y)))
              :in-theory (e/d (rp-equal
                               
                               ex-from-rp
                               is-rp)
                              (RP-EQUAL-IS-SYMMETRIC))))))

  (local
   (defthm lemma3
     (implies (equal (rp-evl x a) (rp-evl y a))
              (equal (bit-fix (rp-evl x a))
                     (bit-fix (rp-evl y a))))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (bit-fix
                               ex-from-rp
                               is-rp) ())))))

  (local
   (defthm lemma4
     (implies (and (RP-EQUAL x y)
                   (pseudo-termp2 x)
                   #|(not (EQUAL (CAR (EX-FROM-RP X)) 'QUOTE))||#
                   (pseudo-termp2 y))
              (EQUAL (BIT-FIX (RP-EVL x A)) (BIT-FIX (RP-EVL Y A))))
     :hints (("Goal"
              :do-not-induct t
              :do-not '(preprocess fertilize generalize)
              :use ((:instance rp-evl-of-rp-equal
                               (term1 x)
                               (term2 y))
                    (:instance lemma3))
              :in-theory (e/d ()
                              (EX-FROM-RP-LEMMA1
                               pseudo-termp2
                               rp-evl-of-rp-equal
                               
                               (:TYPE-PRESCRIPTION PSEUDO-TERMP2)
                               (:TYPE-PRESCRIPTION RP-EQUAL)
                               ))))))

  (local
   (defthm lemma5
     (implies (and (RP-EQUAL x y)
                   (NOT (CONSP (EX-FROM-RP Y))))
              (NOT (CONSP (EX-FROM-RP x))))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp
                               is-rp
                               rp-equal) ())))))

  

  (local
   (defthm rp-evl-resolve-pp-and-order-rec
     (implies (and (pp-formula-checks state)
                   (pseudo-termp2 x)
                   (pseudo-termp2 y)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evl (mv-nth 0 (resolve-pp-and-order-rec x y)) a)
                     (binary-and (rp-evl x a)
                                 (rp-evl y a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (resolve-pp-and-order-rec x y)
              :in-theory (e/d (resolve-pp-and-order-rec
                               ex-from-rp
                               is-rp
                               and$)
                              (rp-equal-cnt
                               pseudo-termp2
                               rp-equal))))))



  (local
   (defthmd eval-of-binary-not-1
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP y)
                   (EQUAL (CAR y) 'binary-not)
                   (CONSP (CDR y))
                   (NOT (CDDR y)))
              (equal (rp-evl y a)
                     (binary-not (RP-EVL (CADR y) A))))
     :hints (("Goal"
              :in-theory (e/d ( )
                              (ex-from-rp))))))

  (local
   (defthmd eval-of-binary-not-2
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP (ex-from-rp y))
                   (EQUAL (CAR (ex-from-rp y)) 'binary-not)
                   (CONSP (CDR (ex-from-rp y)))
                   (NOT (CDDR (ex-from-rp y))))
              (equal (rp-evl y a)
                     (binary-not (RP-EVL (CADR (ex-from-rp y)) A))))
     :hints (("Goal"
              :in-theory (e/d ( ex-from-rp)
                              ())))))

  (local
   (defthm lemma6
     (implies (and (EQUAL (RP-EVL TERM A) 1)
                   (pseudo-termp2 x)
                   (pseudo-termp2 term)
                   (NOT (EQUAL (RP-EVL x A) 1)))
              (NOT (RP-EQUAL TERM x)))
     :hints (("Goal"
              :do-not-induct t
              :do-not '(preprocess fertilize generalize)
              :use ((:instance rp-evl-of-rp-equal
                               (term1 term)
                               (term2 x))) 
              :in-theory (e/d () ())))))
  
  (local
   (defthmd rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-1
     (implies (and (pp-formula-checks state)
                   (pseudo-termp2 term)
                   (pseudo-termp2 x)
                   (rp-evl-meta-extract-global-facts :state state)
                   (search-pp-ands-for-negation-aux term nil x))
              (equal (binary-and (rp-evl term a)
                                 (rp-evl x a))
                     0))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :induct (SEARCH-PP-ANDS-FOR-NEGATION-AUX term nil x)
              :in-theory (e/d (SEARCH-PP-ANDS-FOR-NEGATION-AUX
                               eval-of-binary-not-1
                               eval-of-binary-not-2
                               not$
                               bit-fix
                               and$) ())))))

  (local
   (defthm lemma7
     (implies (and (not (EQUAL (RP-EVL TERM A) (RP-EVL x A)))
                   (pseudo-termp2 x)
                   (pseudo-termp2 term))
              (NOT (RP-EQUAL TERM x)))
     :hints (("Goal"
              :do-not-induct t
              :do-not '(preprocess fertilize generalize)
              :use ((:instance rp-evl-of-rp-equal
                               (term1 term)
                               (term2 x))) 
              :in-theory (e/d () ())))))

  (local
   (defthm lemma8
     (implies (and (not (EQUAL (RP-EVL TERM A) (RP-EVL x A)))
                   (pseudo-termp2 x)
                   (pseudo-termp2 term))
              (equal (EQUAL (EX-FROM-RP TERM)
                            (EX-FROM-RP X))
                     nil))
     :hints (("Goal"
              :do-not-induct t
              :do-not '(preprocess fertilize generalize)
              :use ((:instance rp-evl-of-rp-equal
                               (term1 term)
                               (term2 x))) 
              :in-theory (e/d () ())))))

  (local
   (defthmd  rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-2
     (implies (and (pp-formula-checks state)
                   (pseudo-termp2 term)
                   (pseudo-termp2 x)
                   (rp-evl-meta-extract-global-facts :state state)
                   (search-pp-ands-for-negation-aux term t x))
              (equal (binary-and  (not$ (rp-evl term a))
                                  (rp-evl x a))
                     0))
     :hints (("Goal"
              :do-not-induct t
              :induct (SEARCH-PP-ANDS-FOR-NEGATION-AUX term t x)
              :in-theory (e/d (SEARCH-PP-ANDS-FOR-NEGATION-AUX
                               eval-of-binary-not-1
                               eval-of-binary-not-2
                               not$
                               bit-fix
                               and$) ()))
             ("Subgoal *1/5"
              :use ((:instance lemma8))))))


  (local
   (defthm lemma9
     (implies (and (pseudo-termp2 x)
                   (CONSP (EX-FROM-RP X))
                   (not (EQUAL (CAR (EX-FROM-RP X)) 'quote))
                   (CONSP (CDR (EX-FROM-RP X)))
                   (NOT (CDDR (EX-FROM-RP X))))
              (pseudo-termp2 (CADR (EX-FROM-RP X))))))
  
  (local
   (in-theory (e/d (eval-of-binary-not-1
                    and$
                    eval-of-binary-not-2)
                   (pseudo-termp2))))
  
  (local
   (defthmd  rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION
     (implies (and (pp-formula-checks state)
                   (pseudo-termp2 x)
                   (pseudo-termp2 y)
                   (rp-evl-meta-extract-global-facts :state state)
                   (SEARCH-PP-ANDS-FOR-NEGATION x y))
              (equal (binary-and (rp-evl x a)
                                 (rp-evl y a))
                     0))
     :hints (("Goal"
              :do-not-induct t
              :induct (SEARCH-PP-ANDS-FOR-NEGATION x y)
               :do-not '(preprocess fertilize generalize)
              :in-theory (e/d (SEARCH-PP-ANDS-FOR-NEGATION) ()))
             ("Subgoal *1/6"
               :do-not '(preprocess fertilize generalize)
               :use ((:instance rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-1
                                (term (EX-FROM-RP X))
                                (x y))))
             ("Subgoal *1/3"
               :do-not '(preprocess fertilize generalize)
               :use ((:instance rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-1
                                (term (EX-FROM-RP (CADR (EX-FROM-RP X))))
                                (x y))))
             ("Subgoal *1/5"
               :do-not '(preprocess fertilize generalize)
               :use ((:instance rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-2
                                (term (EX-FROM-RP X))
                                (x y))
                     (:instance rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-2
                                (term (cadr (EX-FROM-RP X)))
                                (x y))))
             ("Subgoal *1/1"
               :do-not '(preprocess fertilize generalize)
               :use ((:instance rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION-aux-2
                                (term (CADR (EX-FROM-RP (CADR (EX-FROM-RP X)))))
                                (x y)))))))

  (defthm rp-evl-resolve-pp-and-order
    (implies (and (pp-formula-checks state)
                  (pseudo-termp2 x)
                  (rp-evl-meta-extract-global-facts :state state))
             (equal (rp-evl (mv-nth 0 (resolve-pp-and-order x)) a)
                    (rp-evl x a)))
    :hints (("Goal"
             :use ((:instance rp-evl-of-SEARCH-PP-ANDS-FOR-NEGATION
                              (x (cadr x))
                              (y (caddr x))))
             :in-theory (e/d (resolve-pp-and-order
                              merge-pp-and) ())))))

(encapsulate
  nil

  (local
   (defthm or-comm
     (and (equal (or$ x y)
                 (or$ y x))
          (equal (or$ x y z)
                 (or$ y x z)))
     :hints (("Goal"
              :in-theory (e/d (or$) ())))))

  (local
   (defthmd rp-evl-ex-from-rp-reverse
     (implies (syntaxp (atom x))
              (equal (rp-evl x a)
                     (rp-evl (ex-from-rp x) a)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthmd eval-of-pp-or-1
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP y)
                   (EQUAL (CAR y) 'binary-OR)
                   (CONSP (CDR y))
                   (CONSP (CDDR y))
                   (NOT (CDDDR y)))
              (equal (rp-evl y a)
                     (binary-OR (RP-EVL (CADR y) A)
                                (RP-EVL (CADDR y) A))))
     :hints (("Goal"
              :in-theory (e/d ( )
                              (ex-from-rp))))))

  (local
   (defthm eval-of-pp-or
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state)
                   (CONSP (EX-FROM-RP Y))
                   (EQUAL (CAR (EX-FROM-RP Y)) 'binary-OR)
                   (CONSP (CDR (EX-FROM-RP Y)))
                   (CONSP (CDDR (EX-FROM-RP Y)))
                   (NOT (CDDDR (EX-FROM-RP Y))))
              (equal (rp-evl y a)
                     (binary-OR (RP-EVL (CADR (EX-FROM-RP Y)) A)
                                (RP-EVL (CADDR (EX-FROM-RP Y)) A))))
     :hints (("Goal"
              :in-theory (e/d (rp-evl-ex-from-rp-reverse
                               eval-of-pp-or-1)
                              (ex-from-rp))))))

  (local
   (defthm rp-evl-resolve-pp-or-order-rec
     (implies (and (pp-formula-checks state)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evl (mv-nth 0 (resolve-pp-or-order-rec x y)) a)
                     (binary-or (rp-evl x a)
                                (rp-evl y a))))
     :hints (("Goal"
              :in-theory (e/d (resolve-pp-or-order-rec
                               or$) ())))))

  (defthm rp-evl-resolve-pp-or-order
    (implies (and (pp-formula-checks state)
                  (rp-evl-meta-extract-global-facts :state state))
             (equal (rp-evl (mv-nth 0 (resolve-pp-or-order x)) a)
                    (rp-evl x a)))
    :hints (("Goal"
             :in-theory (e/d (resolve-pp-or-order
                              merge-pp-or) ())))))

(local
 (defthm dont-rw-syntaxp-resolve-pp-and-order
   (dont-rw-syntaxp (mv-nth 1 (resolve-pp-and-order term)))
   :hints (("Goal"
            :in-theory (e/d (resolve-pp-and-order
                             resolve-pp-and-order-rec) ())))))

(local
 (defthm dont-rw-syntaxp-resolve-pp-or-order
   (dont-rw-syntaxp (mv-nth 1 (resolve-pp-or-order term)))
   :hints (("Goal"
            :in-theory (e/d (resolve-pp-or-order
                             resolve-pp-or-order-rec) ())))))

(defthm resolve-pp-and-order-is-valid-rp-meta-rulep
  (implies (and (pp-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'resolve-pp-and-order
                             :trig-fnc 'merge-pp-and
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (PSEUDO-TERMP2
                            PSEUDO-TERM-LISTP2
                            RP-SYNTAXP
                            VALID-SC)))))

(defthm resolve-pp-or-order-is-valid-rp-meta-rulep
  (implies (and (pp-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'resolve-pp-or-order
                             :trig-fnc 'merge-pp-or
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (PSEUDO-TERMP2
                            merge-pp-or
                            resolve-pp-or-order
                            PSEUDO-TERM-LISTP2
                            RP-SYNTAXP
                            VALID-SC)))))

(rp::add-meta-rules
 pp-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'resolve-pp-or-order
        :trig-fnc 'merge-pp-or
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 'resolve-pp-and-order
        :trig-fnc 'merge-pp-and
        :dont-rw t
        :valid-syntax t)))

(defthm merge-pp-or-def
  (equal (merge-pp-or x y)
         (or$ x y))
  :hints (("Goal"
           :in-theory (e/d (merge-pp-or) ()))))

(defthm merge-pp-and-def
  (equal (merge-pp-and x y)
         (and$ x y))
  :hints (("Goal"
           :in-theory (e/d (merge-pp-and) ()))))
