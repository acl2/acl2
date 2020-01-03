
;; Rewriting based multiplier proofs

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

;; Meta function to be triggered by m2-new.
;; 1. It searches for m2 terms under the current summation and clears them out.
;; 2. Searches for negated terms and duplicated terms under pp-sum and either
;; negates them (everything can be positive) or removes them (duplicates)

(in-package "RP")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))
(local
 (include-book "projects/rp-rewriter/proofs/proof-function-lemmas" :dir :system))
(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(include-book "../mult-defs")

(local
 (in-theory (enable n2b f2 m2 d2 p+ b+ ba  pp type-fix merge-pp+)))

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

(local
 (defthmd consp-ex-from-rp-loose-and-cons-count-term=1
   (implies (consp (ex-from-rp-loose term))
            (> (cons-count term) 1))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp-loose
                             is-rp-loose
                             cons-count) ())))))

(define f2-pp+-of-x-and-rest (x rest (term true-listp))
  :inline t
  (declare (ignorable term))
  (if (equal rest ''0)
      x
    (cons-with-hint 'p+
                    (cons-with-hint x
                                    (cons-with-hint rest
                                                    nil
                                                    (cddr term))
                                    (cdr term))
                    term)))

(define add-rest-coughed (x rest)
  :inline t
  (if (equal rest ''0)
      x
    `(p+ ,x ,rest)))



(define f2-meta-fix-pps-aux (term)
  (declare (xargs :measure (cons-count term)
                  :hints (("Goal"
                           :in-theory
                           (e/d
                            (consp-ex-from-rp-loose-and-cons-count-term=1
                             measure-lemmas) ())))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('p+ x y)
       (case-match y
         (('p+ y1 y2)
          (cond
           ((case-match x (('quote x-sub)
                           (and (integerp x-sub)
                                (evenp2 x-sub))))
            (b* (((mv rest rest-coughed)
                  (f2-meta-fix-pps-aux y)))
              (mv rest
                  (f2-pp+-of-x-and-rest `',(/ (cadr x) 2) rest-coughed term)))) 
           ((rp-equal-cnt x y1 2)
            (b* (((mv rest rest-coughed)
                  (f2-meta-fix-pps-aux y2)))
              (mv rest
                  (f2-pp+-of-x-and-rest y1 rest-coughed y))))
           ((case-match x (('-- &) t))
            (b* (((mv rest rest-coughed)
                  (f2-meta-fix-pps-aux y)))
              (mv (f2-pp+-of-x-and-rest (cadr x) rest term)
                  (f2-pp+-of-x-and-rest x rest-coughed nil))))
           (t
            (b* (((mv rest rest-coughed)
                  (f2-meta-fix-pps-aux y)))
              (mv (f2-pp+-of-x-and-rest x rest term)
                  rest-coughed)))))
         (&
          (cond ((case-match x (('quote x-sub)
                                (and (integerp x-sub)
                                     (evenp2 x-sub))))
                 (b* (((mv rest rest-coughed)
                       (f2-meta-fix-pps-aux y)))
                   (mv rest (f2-pp+-of-x-and-rest `',(/ (cadr x) 2)
                                                  rest-coughed term))))
                ((rp-equal-cnt x y 2)
                 (mv ''0 x))
                ((case-match x (('-- &) t))
                 (b* (((mv rest rest-coughed)
                       (f2-meta-fix-pps-aux y)))
                   (mv (f2-pp+-of-x-and-rest (cadr x) rest term)
                       (f2-pp+-of-x-and-rest x rest-coughed nil))))
                (t (b* (((mv rest rest-coughed)
                         (f2-meta-fix-pps-aux y)))
                     (mv (f2-pp+-of-x-and-rest x rest term)
                         rest-coughed)))))))
      (('-- x)
       (mv x term-orig))
      (('quote x)
       (if (and (integerp x)
                (evenp2 x))
           (mv ''0 `',(/ x 2))
         (mv term-orig ''0)))
      (& (mv term-orig ''0)))))


(define f2-meta-fix-pps (term)
  (declare (xargs :measure (cons-count term)
                  :hints (("Goal"
                           :in-theory (e/d (measure-lemmas) ())))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('b+ x y)
       (b* ((x-orig x)
            (x (ex-from-rp-loose x)))
         (case-match x
           (('p+ & &)
            (b* (((mv res res-coughed) (f2-meta-fix-pps-aux x))
                 (res2 (ex-from-rp-loose res)))
              (mv (case-match res2
                    (('p+ & &) `(b+ ,res ,y))
                    (''0 y)
                    (& `(b+ (p+ '0 ,res) ,y)))
                  res-coughed)))
           (& (b* (((mv rest rest-coughed)  (f2-meta-fix-pps y)))
                (mv ;;`(b+ ,x-orig ,rest)
                    (cons-with-hint 'b+
                                    (cons-with-hint x-orig
                                                    (cons-with-hint rest
                                                                    nil
                                                                    (cddr term))
                                                    (cdr term))
                                    term)
                    rest-coughed))))))
      (('p+ & &)
       (b* (((mv res res-coughed) (f2-meta-fix-pps-aux term-orig))
            (res2 (ex-from-rp-loose res)))
         (mv (case-match res2
               (('p+ & &) res)
               (''0 ''0)
               (& `(p+ '0 ,res)))
             res-coughed)))
      (& (mv term-orig ''0)))))

(define get-coughed-dont-rw (term)
  (case-match term
    (('merge-b+ & x)
     `(nil t ,(get-coughed-dont-rw x)))
    (& t)))

#|(define is-pp-sum-sorted-cw-i0 (term)
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('p+ x y)
       (case-match y
         (''0
          t)
         (('p+ a &)
          (and (or (not (pp-order a x))
                   (cw "Bad order!: ~p0; ~p1 ~%" x a))
               (is-pp-sum-sorted-cw-i0 y)))
         (&
          (or (not (pp-order y x))
              (cw "Bad order!: ~p0; ~p1 ~%" x y)))))
      (& t))))||#

(define f2-meta-main (term)
  (case-match term
    (('f2-new x)
     (progn$
      #|(if (has-pp-binary-not-atom x)
          (progn$  (cw "this input ~p0 to f2-meta-main has
                 has-pp-binary-not-atom. ~%" x)
                   (hard-error 'resolve-pp-sum-order
                               "error ~%" nil))
        nil)||#
      (b* (((mv res res-coughed) (f2-meta-fix-pps x))
           ;(- (if (is-pp-sum-sorted-cw-i0 res-coughed) nil (cw "res coughed is: ~p0 ~%" res-coughed)))
           ((mv result dont-rw)
            (if (equal res-coughed ''0)
                (mv `(f2 ,res) `(nil t))
              (mv `(merge-b+ (f2 ,res) ,res-coughed)
                  `(nil (nil t) t;,(get-coughed-dont-rw res-coughed)
                        ))))
           
           #|(- (if (has-pp-binary-not-atom result)
                  (progn$  (cw "this output ~p0 from d2-meta-main has
                 has-pp-binary-not-atom. with dont-rw ~p1 ~%" result dont-rw)
                           (hard-error 'resolve-pp-sum-order
                                       "error ~%" nil))
                nil))||#)
        (mv result dont-rw))))
    (&
     (mv term nil))))

(define d2-meta-main (term)
  (case-match term
    (('d2-new ('rp ''evenp2 x))
     (b* (#|(- (if (has-pp-binary-not-atom x)
                 (progn$  (cw "this input ~p0 to d2-meta-main has
                 has-pp-binary-not-atom. ~%" x)
                          (hard-error 'resolve-pp-sum-order
                                      "error ~%" nil))
               nil))||#
          ((mv res res-coughed) (f2-meta-fix-pps x))
          ((mv result dont-rw)
           (if (equal res-coughed ''0)
               (mv `(d2 (rp 'evenp2 ,res))
                   `(nil t))
             (mv `(merge-b+ (d2 (rp 'evenp2 ,res)) ,res-coughed)
                 `(nil (nil t) t;,(get-coughed-dont-rw res-coughed)
                       ))))

          #|(- (if (has-pp-binary-not-atom result)
                  (progn$  (cw "this output ~p0 from d2-meta-main has
                 has-pp-binary-not-atom. with dont-rw ~p1 ~%" result dont-rw)
                           (hard-error 'resolve-pp-sum-order
                                       "error ~%" nil))
                nil))||#)
       (mv result dont-rw)))

    (('d2-new x)
     (b* (((mv res res-coughed) (f2-meta-fix-pps x)))
       (if (equal res-coughed ''0)
           (mv `(d2 ,res)
               `(nil t))
         (mv `(merge-b+ (d2 ,res) ,res-coughed)
             `(nil (nil t) t;,(get-coughed-dont-rw res-coughed)
                   )))))
    (&
     (mv term nil))))

;(f2-meta-main `(f2-new (b+ (m2 x) (pp+ a (pp+ a (pp+ b (pp+ b (pp+ (-- c) (-- c)))))))))

#|(local
 (in-theory (enable and-wrapper)))||#

(def-formula-checks
  f2-meta-formula-checks
  (p+ merge-pp+
       b+ merge-b+
       f2 m2 m2-new
       f2-new d2 d2-new
       d2 --
       evenp2
       f2-meta-main
       d2-meta-main))

;;;;;;;;;;;;;;;;;;;;;;

(local
 (encapsulate
   nil

   (local
    (defthm rp-termp-F2-PP+-OF-X-AND-REST
      (implies (and (rp-termp x)
                    (rp-termp rest))
               (rp-termp (f2-pp+-of-x-and-rest x rest term)))
      :hints (("Goal"
               :in-theory (e/d (F2-PP+-OF-X-AND-REST) ())))))

   (defthm rp-termp-f2-meta-fix-pps-aux
     (implies (rp-termp term)
              (and (rp-termp (mv-nth 0 (f2-meta-fix-pps-aux term)))
                   (rp-termp (mv-nth 1 (f2-meta-fix-pps-aux term)))))
     :hints (("Goal"
              :do-not-induct t
              :induct (f2-meta-fix-pps-aux term)
              :in-theory (e/d (f2-meta-fix-pps-aux)
                              (rp-equal
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                               (:TYPE-PRESCRIPTION RP-EQUAL-CNT)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE RP-EQUAL-REFLEXIVE)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:DEFINITION TRUE-LISTP)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                               (:REWRITE IS-IF-RP-TERMP)
                               (:REWRITE
                                RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)
                               (:TYPE-PRESCRIPTION IS-RP$INLINE)
                               (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                               (:REWRITE IS-RP-PSEUDO-TERMP)
                               (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                               (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                               rp-equal-cnt
                               ex-from-rp-loose
                               ex-from-rp)))))

   (defthm rp-termp-f2-meta-fix-pps
     (implies (rp-termp term)
              (and (rp-termp (mv-nth 0 (f2-meta-fix-pps term)))
                   (rp-termp (mv-nth 1 (f2-meta-fix-pps term)))))
     :hints (("Goal"
              :do-not-induct t
              :induct (f2-meta-fix-pps term)
              :in-theory (e/d (f2-meta-fix-pps)
                              (rp-equal
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE RP-EQUAL-REFLEXIVE)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:DEFINITION TRUE-LISTP)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                               (:REWRITE IS-IF-RP-TERMP)
                               (:REWRITE
                                RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)
                               (:TYPE-PRESCRIPTION IS-RP$INLINE)
                               (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                               (:REWRITE IS-RP-PSEUDO-TERMP)
                               (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                               (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                               rp-equal-cnt
                               ex-from-rp-loose
                               ex-from-rp)))))

   (defthm rp-termp-f2-meta-main
     (implies (rp-termp term)
              (rp-termp (mv-nth 0 (f2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (f2-meta-main)
                              ()))))

   (local
    (defthm is-rp-even
      (is-rp (list 'rp ''evenp2 x))
      :hints (("Goal"
               :in-theory (e/d (is-rp) ())))))
   
   (defthm rp-termp-d2-meta-main
     (implies (rp-termp term)
              (rp-termp (mv-nth 0 (d2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (d2-meta-main)
                              ()))))))

#|(local
 (encapsulate
   nil

   (local
    (defthm is-rp-lemma
      (equal (IS-RP (LIST 'RP ''evenp2 term))
             t)
      :hints (("Goal"
               :in-theory (e/d (is-rp) ())))))

   #|(defthm rp-syntaxp-F2-PP+-OF-X-AND-REST
     (implies (and (rp-syntaxp x)
                   (rp-syntaxp rest))
              (rp-syntaxp (f2-pp+-of-x-and-rest x rest term)))
     :hints (("Goal"
              :in-theory (e/d (F2-PP+-OF-X-AND-REST) ()))))||#

   (defthm rp-syntaxp-f2-meta-fix-pps-aux
     (implies (rp-syntaxp term)
              (and (rp-syntaxp (mv-nth 0 (f2-meta-fix-pps-aux term)))
                   (rp-syntaxp (mv-nth 1 (f2-meta-fix-pps-aux term)))))
     :hints (("Goal"
              :do-not-induct t
              :induct (f2-meta-fix-pps-aux term)
              :in-theory (e/d (f2-meta-fix-pps-aux)
                              (rp-equal
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)

                               (:REWRITE RP-EQUAL-REFLEXIVE)
                               (:DEFINITION TRUE-LISTP)
                               (:TYPE-PRESCRIPTION RP-SYNTAXP)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                               (:TYPE-PRESCRIPTION IS-RP$INLINE)
                               (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                               (:REWRITE IS-RP-PSEUDO-TERMP)

                               (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP)
                               (:DEFINITION INCLUDE-FNC)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                               (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                               (:DEFINITION INCLUDE-FNC-SUBTERMS)

                               (:REWRITE NOT-INCLUDE-RP)

                               rp-equal-cnt
                               ex-from-rp-loose
                               ex-from-rp)))))

   (defthm rp-syntaxp-f2-meta-fix-pps
     (implies (rp-syntaxp term)
              (and (rp-syntaxp (mv-nth 0 (f2-meta-fix-pps term)))
                   (rp-syntaxp (mv-nth 1 (f2-meta-fix-pps term)))))
     :hints (("Goal"
              :do-not-induct t
              :induct (f2-meta-fix-pps term)
              :in-theory (e/d (f2-meta-fix-pps)
                              (rp-equal
                               (:REWRITE DEFAULT-CDR)

                               (:REWRITE DEFAULT-CAR)

                               (:REWRITE RP-EQUAL-REFLEXIVE)
                               (:DEFINITION TRUE-LISTP)
                               (:TYPE-PRESCRIPTION RP-SYNTAXP)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)

                               (:TYPE-PRESCRIPTION IS-RP$INLINE)
                               (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                               (:REWRITE IS-RP-PSEUDO-TERMP)

                               (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP)
                               (:DEFINITION INCLUDE-FNC)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                               (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                               (:DEFINITION INCLUDE-FNC-SUBTERMS)

                               (:REWRITE NOT-INCLUDE-RP)

                               rp-equal-cnt
                               ex-from-rp-loose
                               ex-from-rp)))))

   (defthm rp-syntaxp-f2-meta-main
     (implies (rp-syntaxp term)
              (rp-syntaxp (mv-nth 0 (f2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (f2-meta-main)
                              ()))))

   (defthm rp-syntaxp-d2-meta-main
     (implies (rp-syntaxp term)
              (rp-syntaxp (mv-nth 0 (d2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (d2-meta-main)
                              ()))))))||#

#|(local
 (encapsulate
   nil

   (local
    (defthm lemma1
      (and (not (is-falist (cons 'p+ rest)))
           (not (is-falist (cons '-- rest)))
           (not (is-falist (cons 'b+ rest)))
           (not (is-falist (cons 'merge-b+ rest))))))

   (local
    (defthm all-falist-consistent-F2-PP+-OF-X-AND-REST
      (implies (and (all-falist-consistent x)
                    (all-falist-consistent rest))
               (all-falist-consistent (f2-pp+-of-x-and-rest x rest term)))
      :hints (("Goal"
               :in-theory (e/d (F2-PP+-OF-X-AND-REST)
                               (is-falist))))))

   (local
    (defthm all-falist-consistent-f2-meta-fix-pps-aux
      (implies (all-falist-consistent term)
               (and (all-falist-consistent (mv-nth 0 (f2-meta-fix-pps-aux term)))
                    (all-falist-consistent (mv-nth 1 (f2-meta-fix-pps-aux term)))))
      :hints (("Goal"
               :do-not-induct t
               :induct (f2-meta-fix-pps-aux term)
               :in-theory (e/d (f2-meta-fix-pps-aux)
                               (rp-equal
                                IS-FALIST
                                FALIST-CONSISTENT
                                (:REWRITE DEFAULT-CDR)

                                (:REWRITE DEFAULT-CAR)

                                (:REWRITE RP-EQUAL-REFLEXIVE)
                                (:DEFINITION TRUE-LISTP)
                                (:TYPE-PRESCRIPTION ALL-FALIST-CONSISTENT)
                                (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)

                                (:DEFINITION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                                rp-equal-cnt
                                ex-from-rp-loose
                                (:REWRITE
                                 NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT)
                                (:REWRITE
                                 NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT-LST)
                                (:REWRITE
                                 CDR-TERM-IS-ALL-FALIST-CONSISTENT-LST)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                ex-from-rp))))))

   (local
    (defthm all-falist-consistent-f2-meta-fix-pps
      (implies (all-falist-consistent term)
               (and (all-falist-consistent (mv-nth 0 (f2-meta-fix-pps term)))
                    (all-falist-consistent (mv-nth 1 (f2-meta-fix-pps term)))))
      :hints (("Goal"
               :do-not-induct t
               :induct (f2-meta-fix-pps term)
               :in-theory (e/d (f2-meta-fix-pps)
                               (rp-equal
                                IS-FALIST
                                FALIST-CONSISTENT
                                (:REWRITE DEFAULT-CDR)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE RP-EQUAL-REFLEXIVE)
                                (:DEFINITION TRUE-LISTP)
                                (:TYPE-PRESCRIPTION ALL-FALIST-CONSISTENT)
                                (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                                (:DEFINITION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                                rp-equal-cnt
                                ex-from-rp-loose
                                (:REWRITE
                                 NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT)
                                (:REWRITE
                                 NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT-LST)
                                (:REWRITE
                                 CDR-TERM-IS-ALL-FALIST-CONSISTENT-LST)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                ex-from-rp))))))

   (defthm all-falist-consistent-f2-meta-main
     (implies (all-falist-consistent term)
              (all-falist-consistent (mv-nth 0 (f2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (f2-meta-main)
                              ()))))

   (defthm all-falist-consistent-d2-meta-main
     (implies (all-falist-consistent term)
              (all-falist-consistent (mv-nth 0 (d2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (d2-meta-main)
                              ()))))))||#

(local
 (encapsulate
   nil
   (local
    (defthm dont-rw-syntaxp-get-coughed-dont-rw
      (dont-rw-syntaxp (get-coughed-dont-rw term))
      :hints (("goal"
               :in-theory (e/d (get-coughed-dont-rw) ())))))

   (defthm dont-rw-syntaxp-f2-meta-main
     (dont-rw-syntaxp (mv-nth 1 (f2-meta-main term)))
     :hints (("Goal"
              :in-theory (e/d (f2-meta-main) ()))))

   (defthm dont-rw-syntaxp-d2-meta-main
     (dont-rw-syntaxp (mv-nth 1 (d2-meta-main term)))
     :hints (("Goal"
              :in-theory (e/d (d2-meta-main) ()))))))

(local
 (encapsulate
   nil

   (local
    (include-book "../greedy-lemmas"))

   (local
    (in-theory (disable f2 f2-new d2-new d2 m2 sum -- pp-sum)))

   (local
    (defthmd rp-evlt-of-ex-from-rp-reverse-2
      (implies (syntaxp (or (atom x)
                            (equal x '(CAR (CDR (EX-FROM-RP TERM))))))
               (equal (rp-evlt x a)
                      (rp-evlt (ex-from-rp x) a)))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp
                                is-rp) ())))))

   (local
    (defthm eval-of----when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '--)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state))
               (equal (rp-evlt x a)
                      (-- (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-b+-when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'b+)
                    (CONSP (CDR X))
                    (CONSP (CdDR X))
                    (NOT (CDdDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state))
               (equal (rp-evlt x a)
                      (b+ (rp-evlt (cadr x) a)
                          (rp-evlt (caddr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-f2-when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'f2)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state)
                    )
               (equal (rp-evlt x a)
                      (f2 (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-d2-when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'd2)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state)
                    )
               (equal (rp-evlt x a)
                      (d2 (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-f2-new-when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'f2-new)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state)
                    )
               (equal (rp-evlt x a)
                      (f2-new (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))
   (local
    (defthm eval-of-d2-new-when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'd2-new)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state)
                    )
               (equal (rp-evlt x a)
                      (d2-new (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-pp+-when-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'p+)
                    (CONSP (CDR X))
                    (CONSP (CdDR X))
                    (NOT (CDdDR X))
                    (rp-evl-meta-extract-global-facts)
                    (f2-meta-formula-checks state))
               (equal (rp-evlt x a)
                      (p+ (rp-evlt (cadr x) a)
                           (rp-evlt (caddr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm rp-evl-of-rp-equal-derived
      (let ((term1 (CADR (EX-FROM-RP TERM)))
            (term2 (CADDR (EX-FROM-RP TERM))))
        (IMPLIES (AND (RP-TERMP TERM1)
                      (RP-TERMP TERM2)
                      (RP-EQUAL TERM1 TERM2))
                 (EQUAL (RP-EVLt TERM2 A)
                        (RP-EVLt TERM1 A))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (EX-FROM-RP TERM)))
                                (term2 (CADDR (EX-FROM-RP TERM)))))
               :in-theory (e/d () ())))))

   (local
    (defthm rp-evl-of-rp-equal-derived-2
      (let ((term1 (CADR (EX-FROM-RP TERM)))
            (term2 (CADR (CADDR (EX-FROM-RP TERM)))))
        (IMPLIES (AND (RP-TERMP TERM1)
                      (RP-TERMP TERM2)
                      (RP-EQUAL TERM1 TERM2))
                 (EQUAL (RP-EVLt TERM2 A)
                        (RP-EVLt TERM1 A))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (EX-FROM-RP TERM)))
                                (term2 (CADR (CADDR (EX-FROM-RP TERM))))))
               :in-theory (e/d () ())))))

   (local
    (defthm rp-evl-of-rp-equal-derived-3
      (let ((term1 (CADR (CADR (EX-FROM-RP TERM))))
            (term2 (CADR (CADDR (EX-FROM-RP TERM)))))
        (IMPLIES (AND (RP-TERMP TERM1)
                      (RP-TERMP TERM2)
                      (RP-EQUAL TERM1 TERM2))
                 (EQUAL (RP-EVL TERM2 A)
                        (RP-EVL TERM1 A))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (CADR (EX-FROM-RP TERM))))
                                (term2 (CADR (CADDR (EX-FROM-RP TERM))))))
               :in-theory (e/d () ())))))

   (local
    (defthm rp-evl-of-rp-equal-derived-4
      (let ((term1 (CADR (CADR (EX-FROM-RP TERM))))
            (term2 (CADR (CADR (CADDR (EX-FROM-RP TERM))))))
        (IMPLIES (AND (RP-TERMP TERM1)
                      (RP-TERMP TERM2)
                      (RP-EQUAL TERM1 TERM2))
                 (EQUAL (RP-EVLt TERM2 A)
                        (RP-EVLt TERM1 A))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (CADR (EX-FROM-RP TERM))))
                                (term2 (CADR (CADR (CADDR (EX-FROM-RP TERM)))))))
               :in-theory (e/d () ())))))

   (local
    (defthm dumb-lemma1
      (implies (and (EQUAL (CAR term) '--)
                    (consp term)
                    (consp (cdr term))
                    (not (cddr term))
                    (f2-meta-formula-checks state)
                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (RP-EVLt (EX-FROM-RP term) A)
                      (-- (rp-evlt (cadr term) a))))))

   (local
    (defthm lemma2
      (implies (and (integerp x)
                    (evenp2 x))
               (equal (equal (sum (* 1/2 x)
                                  (* 1/2 x))
                             (type-fix x))
                      t))
      :hints (("Goal"
               :in-theory (e/d (sum evenp2 type-fix) ())))))

   (local
    (defthm rp-evl-of-F2-PP+-OF-X-AND-REST
      (implies (and (f2-meta-formula-checks state)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (sum b (rp-evlt (f2-pp+-of-x-and-rest x rest term) a))
                      (sum b
                           (rp-evlt x a)
                           (rp-evlt rest a))))
      :hints (("Goal"
               :in-theory (e/d (f2-pp+-of-x-and-rest) ())))))

   (local
    (defthm lemma3
      (implies (and (EQUAL (CAR term) 'QUOTE)
                    (consp term)
                    (consp (cdr term)))
               (equal (rp-evlt (ex-from-rp term) a)
                      (cadr term)))
      ))

   (local
    (defthm lemma4
      (implies (and (integerp x)
                    (EVENP2 x))
               (equal (sum (* 1/2 x)
                           (* 1/2 x)
                           y)
                      (sum x y)))
      :hints (("Goal"
               :in-theory (e/d (sum evenp2) ())))))

   (defthm rp-trans-when-quote
     (implies (equal (car x) 'quote)
              (equal (rp-trans x) x))
     :rule-classes :forward-chaining)
   
   (defthm rp-evl-of-f2-meta-fix-pps-aux
     (implies (and (f2-meta-formula-checks state)
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (sum (rp-evlt (mv-nth 0 (f2-meta-fix-pps-aux term)) a)
                          (rp-evlt (mv-nth 1 (f2-meta-fix-pps-aux term)) a)
                          (rp-evlt (mv-nth 1 (f2-meta-fix-pps-aux term)) a))
                     (type-fix (rp-evlt term a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (f2-meta-fix-pps-aux term)
              :expand ((:free (x) (rp-trans (cons 'quote x))))
              :in-theory (e/d (f2-meta-fix-pps-aux
                               rp-evlt-of-ex-from-rp-reverse-2
                               ex-from-rp-loose-is-ex-from-rp)
                              (rp-equal
                               (:e tau-system)
                               rp-trans
                               RP-EVLT-OF-EX-FROM-RP
                               --
                               f2 m2 sum
                               type-fix
                               (:TYPE-PRESCRIPTION B+)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:TYPE-PRESCRIPTION RP-EQUAL)
                               (:TYPE-PRESCRIPTION TYPE-FIX)
                               (:TYPE-PRESCRIPTION F2-META-FORMULA-CHECKS)
                               (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               
                               (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                               (:REWRITE
                                EVAL-OF-B+-WHEN-F2-META-FORMULA-CHECKS)
                               (:REWRITE RP-EVL-OF-UNARY-/-CALL)
                               (:REWRITE RP-EVL-OF-UNARY---CALL)
                               (:REWRITE RP-EVL-OF-TYPESPEC-CHECK-CALL)
                               (:REWRITE RP-EVL-OF-SYNP-CALL)
                               (:REWRITE RP-EVL-OF-SYMBOLP-CALL)
                               (:REWRITE RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL)
                               (:REWRITE RP-EVL-OF-SYMBOL-NAME-CALL)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:REWRITE DEFAULT-CDR)
                               (:DEFINITION EX-FROM-RP)
                               (:DEFINITION INCLUDE-FNC)
                               (:REWRITE NOT-INCLUDE-RP)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               EVL-OF-EXTRACT-FROM-RP-2
                               RP-EVL-OF-VARIABLE
                               (:REWRITE RP-EQUAL-REFLEXIVE)
                               (:REWRITE DEFAULT-CAR)
                               (:DEFINITION RP-TERMP)
                               
                               (:REWRITE EX-FROM-SYNP-LEMMA1)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               (:DEFINITION IS-SYNP$INLINE)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               EVL-OF-EXTRACT-FROM-RP)))))

   (local
    (defthmd dumb-lemma2
      (implies (EQUAL (EX-FROM-RP term) ''0)
               (equal (rp-evlt term a) 0))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse-2)
                               (RP-EVLT-OF-EX-FROM-RP))))))

   (local
    (defthm dumb-lemma3
      (implies (and (EQUAL (EX-FROM-RP (MV-NTH 0 (F2-META-FIX-PPS-AUX TERM)))
                           ''0)
                    (f2-meta-formula-checks state)
                    
                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (SUM (RP-EVLt (MV-NTH 1 (F2-META-FIX-PPS-AUX TERM))
                                   A)
                           (RP-EVLt (MV-NTH 1 (F2-META-FIX-PPS-AUX TERM))
                                   A))
                      (type-fix (rp-evlt term a))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-f2-meta-fix-pps-aux))
               :in-theory (e/d (dumb-lemma2) (type-fix))))))

   (defthm rp-evl-of-f2-meta-fix-pps
     (implies (and (f2-meta-formula-checks state)
                   
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (sum (rp-evlt (mv-nth 0 (f2-meta-fix-pps term)) a)
                          (rp-evlt (mv-nth 1 (f2-meta-fix-pps term)) a)
                          (rp-evlt (mv-nth 1 (f2-meta-fix-pps term)) a))
                     (type-fix (rp-evlt term a))))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :induct (f2-meta-fix-pps term)
              :in-theory (e/d (f2-meta-fix-pps
                               rp-evlt-of-ex-from-rp-reverse-2
                               ex-from-rp-loose-is-ex-from-rp)
                              (rp-equal
                               RP-EVLT-OF-EX-FROM-RP
                               --
                               f2 m2 sum
                               (:REWRITE RP-EVL-OF-VARIABLE)
                               EVL-OF-EXTRACT-FROM-RP
                               type-fix)))))

   (local
    (defthm dumb-lemma4
      (implies (and (f2-meta-formula-checks state)
                    
                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts :state state)
                    (EQUAL (MV-NTH 1 (F2-META-FIX-PPS term)) ''0))
               (equal (type-fix (rp-evlt (mv-nth 0 (f2-meta-fix-pps term)) a))
                      (type-fix (rp-evlt term a))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-f2-meta-fix-pps))
               :in-theory (e/d () (type-fix
                                   RP-EVL-OF-VARIABLE))))))

   (local
    (defthm dumb-lemma5
      (implies (equal (type-fix a)
                      (type-fix b))
               (equal (equal (f2 a) (f2 b))
                      t))
      :hints (("Goal"
               :in-theory (e/d (type-fix f2) ())))))

   (local
    (defthm dumb-lemma5-for-d2
      (implies (equal (type-fix a)
                      (type-fix b))
               (equal (equal (d2 a) (d2 b))
                      t))
      :hints (("Goal"
               :in-theory (e/d (type-fix d2
                                         m2-when-not-type-p
                                         f2-when-not-type-p) ())))))

   (defthm rp-evl-of-f2-meta-main
     (implies (and (f2-meta-formula-checks state)
                   
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evlt (mv-nth 0 (f2-meta-main term)) a)
                     (rp-evlt term a)))
     :otf-flg t
     :hints (("Goal"
              :in-theory (e/d (f2-meta-main
                               push-elements-into-f2)
                              (type-fix)))))

   (defthm rp-evl-of-d2-meta-main
     (implies (and (f2-meta-formula-checks state)
                   
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evlt (mv-nth 0 (d2-meta-main term)) a)
                     (rp-evlt term a)))
     :otf-flg t
     :hints (("Goal"
              :in-theory (e/d (d2-meta-main
                               push-elements-into-d2)
                              (type-fix
                               EX-FROM-RP-LEMMA1
                               
                               
                               (:DEFINITION TRUE-LISTP)
; (:REWRITE SUM-COMM-1-WITH-LOOP-STOPPER)
; (:REWRITE SUM-COMM-2-WITH-LOOP-STOPPER)
                               (:TYPE-PRESCRIPTION F2-META-FORMULA-CHECKS)
                               (:TYPE-PRESCRIPTION INCLUDE-FNC)
                               (:TYPE-PRESCRIPTION IS-RP$INLINE)
                               (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               
                               )))))))

(local
 (encapsulate
   nil

   (local
    (defthm lemma1
      (and (not (is-if (cons 'p+ rest)))
           (not (is-rp (cons 'p+ rest)))
           (not (is-rp (cons 'merge-b+ rest)))
           (not (is-if (cons 'merge-b+ rest)))
           (not (is-rp (cons 'b+ rest)))
           (not (is-if (cons 'b+ rest)))
           (not (is-rp (cons '-- rest)))
           (not (is-if (cons '-- rest)))
           (not (is-rp (cons 'f2 rest)))
           (not (is-if (cons 'f2 rest)))
           (not (is-rp (cons 'f2-new rest)))
           (not (is-if (cons 'f2-new rest))))
      :hints (("Goal"
               :in-theory (e/d (is-if is-rp) ())))))

   (local
    (defthm lemma2
      (implies (and (f2-meta-formula-checks state)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (eval-and-all (context-from-rp (list 'rp ''evenp2 term) NIL) A)
                      (and (evenp2 (RP-EVLt term A))
                           (eval-and-all (context-from-rp term NIL) A))))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (eval-and-all
                                context-from-rp
                                is-rp)
                               (evenp2))))))

   (local
    (defthm valid-sc-F2-PP+-OF-X-AND-REST
      (implies (and (valid-sc x a)
                    (valid-sc rest a))
               (valid-sc (f2-pp+-of-x-and-rest x rest term) a))
      :hints (("Goal"
               :in-theory (e/d (F2-PP+-OF-X-AND-REST) ())))))

   (local
    (defthm lemma3
      (IMPLIES (AND (CONSP term)
              (EQUAL (CAR term)
                     '--)
              (CONSP (CDR term))
              (NOT (CDDR term))
              (VALID-SC TERM A))
         (VALID-SC (CADR term)
                   A))))

   

   (local
    (defthm valid-sc-f2-meta-fix-pps-aux
      (implies (and (valid-sc term a)
                    (rp-termp term))
               (and (valid-sc (mv-nth 0 (f2-meta-fix-pps-aux term)) a)
                    (valid-sc (mv-nth 1 (f2-meta-fix-pps-aux term)) a)))
      :hints (("Goal"
               :do-not-induct t
               :induct (f2-meta-fix-pps-aux term)
               :do-not '( generalize fertilize)
               :expand ((:free (first rest)
                               (valid-sc (cons first rest) a)))
               :in-theory (e/d (f2-meta-fix-pps-aux
                                ex-from-rp-loose-is-ex-from-rp)
                               (rp-equal
                                (:REWRITE ACL2::O-P-O-INFP-CAR)
                                (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                (:REWRITE VALID-SC-EX-FROM-RP-2)
                                (:DEFINITION EVAL-AND-ALL)
                                (:REWRITE IS-IF-RP-TERMP)
                                (:DEFINITION ACL2::APPLY$-BADGEP)
                                (:REWRITE
                                 ACL2::INTEGER-LISTP-IMPLIES-INTEGERP)

                                (:REWRITE RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)
                                (:TYPE-PRESCRIPTION O<)
                                (:TYPE-PRESCRIPTION EVENP2)
                                (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                (:TYPE-PRESCRIPTION FALIST-CONSISTENT)
                                (:REWRITE COMMUTATIVITY-OF-*)
                                rp-termp
                                valid-sc
                                (:e tau-system)
                                (:DEFINITION NOT)
                                (:TYPE-PRESCRIPTION O-P)
                                (:FORWARD-CHAINING RP-TERMP-IMPLIES)
                                (:FORWARD-CHAINING
                                    EXTRACT-FROM-SYNP-PSEUDO-TERM-LISTP)
;(:META ACL2::MV-NTH-CONS-META)
                                (:DEFINITION evenp2)
                                (:REWRITE DEFAULT-*-2)
                                (:REWRITE DEFAULT-*-1)
                                (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                                (:TYPE-PRESCRIPTION RP-TERMP)
                                (:REWRITE DEFAULT-CDR)
                                
                                (:TYPE-PRESCRIPTION RP-EQUAL-CNT)
                                (:REWRITE QUOTEP-TERM-WITH-EX-FROM-RP)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE RP-EQUAL-REFLEXIVE)
                                (:DEFINITION TRUE-LISTP)
                                (:TYPE-PRESCRIPTION VALID-SC)
                                (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                                (:TYPE-PRESCRIPTION IS-RP$INLINE)
                                (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                                (:REWRITE IS-RP-PSEUDO-TERMP)
                                
                                (:DEFINITION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                                
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE NOT-INCLUDE-RP)
                                rp-equal-cnt
                                ex-from-rp-loose
                                ex-from-rp))))))

   (local
    (defthm valid-sc-f2-meta-fix-pps
      (implies (and (valid-sc term a)
                    (rp-termp term))
               (and (valid-sc (mv-nth 0 (f2-meta-fix-pps term)) a)
                    (valid-sc (mv-nth 1 (f2-meta-fix-pps term)) a)))
      :hints (("Goal"
               :do-not-induct t
               :induct (f2-meta-fix-pps term)
               :expand ((:free (first rest)
                               (valid-sc (cons first rest) a)))
               :in-theory (e/d (f2-meta-fix-pps
                                ex-from-rp-loose-is-ex-from-rp)
                               (rp-equal
                                valid-sc
                                (:REWRITE DEFAULT-CDR)
                                
                                (:TYPE-PRESCRIPTION RP-EQUAL-CNT)
                                (:REWRITE QUOTEP-TERM-WITH-EX-FROM-RP)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE RP-EQUAL-REFLEXIVE)
                                (:DEFINITION TRUE-LISTP)
                                (:TYPE-PRESCRIPTION VALID-SC)
                                (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                                (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                                (:TYPE-PRESCRIPTION IS-RP$INLINE)
                                (:TYPE-PRESCRIPTION IS-RP-LOOSE$INLINE)
                                (:REWRITE IS-RP-PSEUDO-TERMP)
                                
                                (:DEFINITION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC)
                                (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                                
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE NOT-INCLUDE-RP)
                                rp-equal-cnt
                                ex-from-rp-loose
                                ex-from-rp))))))

   (defthm valid-sc-f2-meta-main
     (implies (and (valid-sc term a)
                   (rp-termp term))
              (valid-sc (mv-nth 0 (f2-meta-main term)) a))
     :hints (("Goal"
              :in-theory (e/d (f2-meta-main
                               is-rp
                               is-if)
                              ()))))

   ;;;;;

   (local
    (defthm evenp-f2-meta-fix-pps
      (implies (and (f2-meta-formula-checks state)
                    
                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (evenp2 (sum (rp-evlt (mv-nth 0 (f2-meta-fix-pps term)) a)
                                   (rp-evlt (mv-nth 1 (f2-meta-fix-pps term)) a)
                                   (rp-evlt (mv-nth 1 (f2-meta-fix-pps term)) a)))
                      (evenp2 (type-fix (rp-evlt term a)))))
      :hints (("Goal"
               :in-theory (e/d () (evenp2
                                   type-fix
                                   sum))))))

   (local
    (include-book "../greedy-lemmas"))

   (local
    (defthm evenp-f2-meta-fix-pps-lemma1
      (implies (and (f2-meta-formula-checks state)
                    
                    (rp-termp term)
                    (equal (mv-nth 1 (f2-meta-fix-pps term)) ''0)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (evenp2 (rp-evlt (mv-nth 0 (f2-meta-fix-pps term)) a))
                      (evenp2 (rp-evlt term a))))
      :hints (("Goal"
               :use ((:instance evenp-f2-meta-fix-pps))
               :in-theory (e/d () (evenp2
                                   RP-EVL-OF-VARIABLE
                                   evenp-f2-meta-fix-pps
                                   type-fix
                                   sum))))))

   (local
    (defthm evenp-f2-meta-fix-pps-lemma2
      (implies (and (f2-meta-formula-checks state)
                    
                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (evenp2 (rp-evlt (mv-nth 0 (f2-meta-fix-pps term)) a))
                      (evenp2 (rp-evlt term a))))
      :hints (("Goal"
               :use ((:instance evenp-f2-meta-fix-pps))
               :in-theory (e/d () (evenp2
                                   RP-EVL-OF-VARIABLE
                                   evenp-f2-meta-fix-pps
                                   type-fix
                                   sum))))))

   (local
    (defthm valid-sc-of-d2-new
      (implies (case-match term (('d2-new &) t))
               (equal (valid-sc term a)
                      (valid-sc (cadr term) a)))
      :hints (("Goal"
               :in-theory (e/d (valid-sc is-rp
                                         is-if) ())))))

   (defthm valid-sc-d2-meta-main
     (implies (and (valid-sc term a)
                   (f2-meta-formula-checks state)
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state)
                   )
              (valid-sc (mv-nth 0 (d2-meta-main term)) a))
     :hints (("Goal"
              :expand ((:free (rest) (VALID-SC (LIST 'D2 rest) A))
                       (:free (rest) (VALID-SC (cons 'MERGE-B+ rest) A)))
              :in-theory (e/d (d2-meta-main
                               valid-sc-single-step
                               is-rp
                               is-if)
                              (evenp2
                               valid-sc
                               EX-FROM-RP-LEMMA1)))))))

;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm f2-meta-main-valid-rp-meta-rulep
  (implies (and (f2-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'f2-meta-main
                             :trig-fnc 'f2-new
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp-meta-valid-syntaxp)
                           (rp-termp
                            rp-term-listp
                            
                            f2-meta-main
                            valid-sc)))))

(defthm d2-meta-main-valid-rp-meta-rulep
  (implies (and (f2-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'd2-meta-main
                             :trig-fnc 'd2-new
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp-meta-valid-syntaxp)
                           (rp-termp
                            rp-term-listp
                            
                            d2-meta-main
                            valid-sc)))))

(rp::add-meta-rules
 f2-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'f2-meta-main
        :trig-fnc 'f2-new
        :dont-rw t
        :valid-syntax t)
  (make rp-meta-rule-rec
        :fnc 'd2-meta-main
        :trig-fnc 'd2-new
        :dont-rw t
        :valid-syntax t)))
