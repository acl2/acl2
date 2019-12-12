
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
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5))

(local
 (in-theory (enable n2b f2 m2 d2 p+ b+ ba  pp type-fix merge-pp+)))

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

;; extract all the m2 terms in the summation
(define m2-meta-extract-m2s (term)
  (declare (xargs :measure (cons-count term)
                  :hints (("Goal"
                           :in-theory (e/d (measure-lemmas) ())))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('b+ ('-- x) y)
       (b* (#|(x-orig x)||#
            (x (ex-from-rp-loose x)))
         (case-match x
           (('m2 x-in)
            (b* (((mv rest rest-dont-rw) (m2-meta-extract-m2s y)))
              (mv `(merge-b+ ,x-in ,rest)
                  `(nil t ,rest-dont-rw))))
           (& (mv `(merge-b+ ,x ,y)
                  `(nil t t))))))
      (('b+ x y)
       (b* (#|(x-orig x)||#
            (x (ex-from-rp-loose x)))
         (case-match x
           (('m2 x-in)
            (b* (((mv rest rest-dont-rw) (m2-meta-extract-m2s y)))
              (mv `(merge-b+ ,x-in ,rest)
                  `(nil t ,rest-dont-rw))))
           (& (mv term-orig t)))))
      (('m2 x)
       (mv x t))
      (&
       (mv term-orig t)))))

(local
 (defthmd consp-ex-from-rp-loose-and-cons-count-term=1
   (implies (CONSP (EX-FROM-RP-LOOSE TERM))
            (> (CONS-COUNT TERM) 1))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp-loose
                             is-rp-loose
                             cons-count) ())))))

(define m2-pp+-of-x-and-rest (x rest (term true-listp))
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

(define m2-meta-fix-pps-aux (term)
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
       ;; (case-match x
       ;;   (('quote x-sub)

       (case-match y
         (('p+ y1 y2)
          (cond ((case-match x (('quote x-sub)
                                (and (integerp x-sub)
                                     (evenp2 x-sub))))
                 (b* ((rest (m2-meta-fix-pps-aux y)))
                   rest))
                ((rp-equal-cnt x y1 2)
                 (b* ((rest (m2-meta-fix-pps-aux y2)))
                   rest))
                ((case-match x (('-- &) t))
                 (b* ((rest
                       (m2-meta-fix-pps-aux y)))
                   (m2-pp+-of-x-and-rest (cadr x) rest term)))
                (t
                 (b* ((rest
                       (m2-meta-fix-pps-aux y)))
                   (m2-pp+-of-x-and-rest x rest term)))))
         (&
          (cond ((case-match x (('quote x-sub)
                                (and (integerp x-sub)
                                     (evenp2 x-sub))))
                 (b* ((rest (m2-meta-fix-pps-aux y)))
                   rest))
                ((rp-equal-cnt x y 2)
                 ''0)
                ((case-match x (('-- &) t))
                 (b* ((rest
                       (m2-meta-fix-pps-aux y)))
                   (m2-pp+-of-x-and-rest (cadr x) rest term)))
                (t (b* ((rest
                         (m2-meta-fix-pps-aux y)))
                     (m2-pp+-of-x-and-rest x rest term)))))))
      (('-- x)
       x)
      (('quote x)
       (if (and (integerp x)
                (evenp x))
           ''0
         term-orig))
      (& term-orig))))

#|(define m2-meta-fix-pps-aux (term)
  (declare (xargs :measure (cons-count term)
                  :hints (("Goal"
                           :in-theory
                           (e/d
                            (consp-ex-from-rp-loose-and-cons-count-term=1
                             measure-lemmas) ())))))
  (b* ((term-orig term)
       (term (ex-from-rp-loose term)))
    (case-match term
      (('pp+ ('-- x) ('pp+ ('-- y) z))
       (if (rp-equal-cnt x y 0)
           (m2-meta-fix-pps-aux z)
         `(pp+ ,x ,(m2-meta-fix-pps-aux (caddr term)))))
      (('pp+ ('-- x) y)
       `(pp+ ,x ,(m2-meta-fix-pps-aux y)))
      (('pp+ x ('pp+ y z))
       (if (rp-equal-cnt x y 0)
           (m2-meta-fix-pps-aux z)
         `(pp+ ,x ,(m2-meta-fix-pps-aux (caddr term)))))
      (('pp+ x y)
       (if (rp-equal-cnt x y 0)
           ''0
         term-orig))
      (('-- x)
       x)
      (('quote x)
       (if (and (integerp x)
                (evenp x))
           ''0
         term-orig))
      (& term-orig))))||#

(define m2-meta-fix-pps (term)
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
            (b* ((res (m2-meta-fix-pps-aux x))
                 (res2 (ex-from-rp-loose res)))
              (case-match res2
                (('p+ & &) `(b+ ,res ,y))
                (''0 y;`(b+ ,res ,y)
                     )
                (& `(b+ (p+ '0 ,res) ,y)))))
           (& `(b+ ,x-orig ,(m2-meta-fix-pps y))))))
      (('p+ & &)
       (b* ((res (m2-meta-fix-pps-aux term-orig))
            (res2 (ex-from-rp-loose res)))
         (case-match res2
           (('p+ & &) res)
           (''0 ''0)
           (& `(p+ '0 ,res)))))
      (& term-orig))))

#|(define has-repeated-pp (term)
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('b+ x y)
       (or (has-repeated-pp x)
           (has-repeated-pp y)))
      (('p+ x y)
       (b* ((x (ex-from-rp x))
            (y (ex-from-rp y)))
         (case-match y
           (('p+ a &)
            (or (rp-equal x a)
                (has-repeated-pp y)))
           (&
            (rp-equal x y)))))
      (&
       nil))))||#

(define m2-meta-main (term)
  (case-match term
    (('m2-new x)
     (progn$
      #|(if (has-pp-binary-not-atom x)
      (progn$  (cw "this input ~p0 to m2-meta-main has
      has-pp-binary-not-atom. ~%" x)
      (hard-error 'resolve-pp-sum-order
      "error ~%" nil))
      nil)||#

      (b* (((mv result dont-rw)
            (b* ((x-orig x)
                 (x (ex-from-rp-loose x)))
              (case-match x
                (('m2 &)
                 (b* (((mv res dont-rw)
                       (m2-meta-extract-m2s x-orig)))
                   (mv `(m2-new ,res)
                       `(nil ,dont-rw))))
                (('b+ a &)
                 (b* ((a (ex-from-rp-loose a)))
                   (case-match a
                     (('m2 &)
                      (b* (((mv res dont-rw)
                            (m2-meta-extract-m2s x-orig)))
                        (mv `(m2-new ,res)
                            `(nil ,dont-rw))))
                     (& (b* ((res (m2-meta-fix-pps x-orig))
                             #|(- (if (has-repeated-pp res)
                             (cw "Bad EGG! orig = ~p0; res=~p1 ~%"
                             x-orig res)
                             nil))||#)
                          (mv `(m2 ,res)
                              `(nil t)))))))
                (&
                 (b* ((res (m2-meta-fix-pps x-orig))
                      #|(- (if (has-repeated-pp res)
                      (cw "Bad EGG! orig = ~p0; res=~p1 ~%"
                      x-orig res)
                      nil))||#)
                   (mv `(m2 ,res)
                       `(nil t)))))))
           #|(- (if (has-pp-binary-not-atom result)
           (progn$  (cw "this output ~p0 from m2-meta-main has
           has-pp-binary-not-atom. with dont-rw ~p1, Input was ~p2 ~%"
           result dont-rw term)
           (hard-error 'resolve-pp-sum-order
           "error ~%" nil))
           nil))||#)
        (mv result dont-rw))))

    (&
     (mv term nil))))

#|(rp::m2-meta-main '(m2-new (b+ (PP+ (BINARY-AND (BITS '62 '1 MULT)
                                                (BITS '63 '1 MCAND))
                                    (PP+ (BINARY-AND (BITS '63 '1 MCAND)
                                                     (BITS '63 '1 MULT))
                                         (BINARY-AND (BITS '63 '1 MCAND)
                                                     (BITS '63 '1 MULT))))
                               (f2 a))))||#

(encapsulate
  nil
  (local
   (in-theory (disable RP-EQUAL
                       EX-FROM-RP
                       M2-META-FIX-PPS-AUX)))

  (def-formula-checks
    m2-meta-formula-checks
    (p+ merge-pp+
        b+ merge-b+
        f2 m2 m2-new
        f2-new
        d2 --
        m2-meta-main)))

(local
 (encapsulate
   nil

   (defthm rp-termp-m2-pp+-of-x-and-rest
     (implies (and (rp-termp x)
                   (rp-termp rest))
              (rp-termp (m2-pp+-of-x-and-rest x rest term)))
     :hints (("Goal"
              :in-theory (e/d (m2-pp+-of-x-and-rest) ()))))

   (defthm rp-termp-m2-meta-fix-pps-aux
     (implies (rp-termp term)
              (rp-termp (m2-meta-fix-pps-aux term)))
     :hints (("Goal"
              :expand ((RP-TERMP
                        (LIST 'p+
                              (CADR (EX-FROM-RP-LOOSE TERM))
                              (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP-LOOSE
                                                           TERM)))))
                       (RP-TERMP
                        (LIST 'p+
                              (CADR (CADR (EX-FROM-RP-LOOSE TERM)))
                              (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP-LOOSE TERM))))))
              :in-theory (e/d (m2-meta-fix-pps-aux)
                              (not
                               (:REWRITE
                                ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                               (:REWRITE ACL2::ACL2-NUMBERP-X)
                               (:REWRITE RP-EQUAL-SUBTERMS-REFLEXIVE)
                               (:REWRITE ACL2::RATIONALP-X)
                               (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                               (:REWRITE ACL2::SIMPLIFY-SUMS-EQUAL)
                               (:REWRITE RP-EQUAL-REFLEXIVE)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE
                                ACL2::ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE
                                ACL2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                               (:REWRITE
                                ACL2::REDUCE-ADDITIVE-CONSTANT-EQUAL)
                               (:DEFINITION RP-EQUAL)
                               rp-equal-cnt
                               ex-from-rp
                               ex-from-rp-loose
                               rp-termp
                               )))))

   (defthm rp-termp-m2-meta-fix-pps
     (implies (rp-termp term)
              (rp-termp (m2-meta-fix-pps term)))
     :hints (("Goal"
              :in-theory (e/d (M2-META-FIX-PPS) ()))))

   (defthm rp-termp-m2-meta-extract-m2s
     (implies (rp-termp term)
              (rp-termp (mv-nth 0 (m2-meta-extract-m2s term))))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-extract-m2s)
                              (falist-consistent
                               (:REWRITE
                                ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))))))

   (defthm rp-termp-m2-meta-main
     (implies (rp-termp term)
              (rp-termp (mv-nth 0 (m2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-main) ()))))))

#|(local
 (encapsulate
   nil

   (defthm rp-syntaxp-m2-pp+-of-x-and-rest
     (implies (and (rp-syntaxp x)
                   (rp-syntaxp rest))
              (rp-syntaxp (m2-pp+-of-x-and-rest x rest term)))
     :hints (("goal"
              :in-theory (e/d (m2-pp+-of-x-and-rest) ()))))

   (defthm rp-syntaxp-m2-meta-fix-pps-aux
     (implies (rp-syntaxp term)
              (rp-syntaxp (m2-meta-fix-pps-aux term)))
     :hints (("Goal"
              :expand ((RP-SYNTAXP
                        (LIST 'p+
                              (CADR (EX-FROM-RP-LOOSE TERM))
                              (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP-LOOSE
                                                           TERM)))))
                       (RP-SYNTAXP
                        (LIST 'p+
                              (CADR (CADR (EX-FROM-RP-LOOSE TERM)))
                              (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP-LOOSE TERM))))))
              :in-theory (e/d (m2-meta-fix-pps-aux)
                              (not
                               rp-equal-cnt
                               ex-from-rp
                               ex-from-rp-loose
                               rp-syntaxp
                               )))))

   (local
    (defthm rp-syntaxp-m2-meta-fix-pps
      (implies (rp-syntaxp term)
               (rp-syntaxp (m2-meta-fix-pps term)))
      :hints (("Goal"
               :in-theory (e/d (M2-META-FIX-PPS) ())))))

   (local
    (defthm rp-syntaxp-m2-meta-extract-m2s
      (implies (rp-syntaxp term)
               (rp-syntaxp (mv-nth 0 (m2-meta-extract-m2s term))))
      :hints (("Goal"
               :in-theory (e/d (m2-meta-extract-m2s) ())))))

   (defthm rp-syntaxp-m2-meta-main
     (implies (rp-syntaxp term)
              (rp-syntaxp (mv-nth 0 (m2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-main) ()))))))||#

#|(local
 (encapsulate
   nil

   (local
    (defthm all-falist-consistent-m2-pp+-of-x-and-rest
      (implies (and (all-falist-consistent x)
                    (all-falist-consistent rest))
               (all-falist-consistent (m2-pp+-of-x-and-rest x rest term)))
      :hints (("Goal"
               :in-theory (e/d (m2-pp+-of-x-and-rest
                                is-falist)
                               ())))))

   (local
    (defthm all-falist-consistent-m2-meta-fix-pps-aux
      (implies (all-falist-consistent term)
               (all-falist-consistent (m2-meta-fix-pps-aux term)))
      :hints (("Goal"
               :expand ((ALL-FALIST-CONSISTENT
                         (LIST 'p+
                               (CADR (EX-FROM-RP-LOOSE TERM))
                               (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP-LOOSE
                                                            TERM)))))
                        (ALL-FALIST-CONSISTENT
                         (LIST 'p+
                               (CADR (CADR (EX-FROM-RP-LOOSE TERM)))
                               (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP-LOOSE TERM))))))
               :in-theory (e/d (m2-meta-fix-pps-aux)
                               (not
                                rp-equal-cnt
                                ex-from-rp
                                ex-from-rp-loose
                                all-falist-consistent
                                ))))))

   (local
    (defthm all-falist-consistent-m2-meta-fix-pps
      (implies (all-falist-consistent term)
               (all-falist-consistent (m2-meta-fix-pps term)))
      :hints (("Goal"
               :in-theory (e/d (M2-META-FIX-PPS) ())))))

   (local
    (defthm all-falist-consistent-m2-meta-extract-m2s
      (implies (all-falist-consistent term)
               (all-falist-consistent (mv-nth 0 (m2-meta-extract-m2s term))))
      :hints (("Goal"
               :in-theory (e/d (m2-meta-extract-m2s) ())))))

   (defthm all-falist-consistent-m2-meta-main
     (implies (all-falist-consistent term)
              (all-falist-consistent (mv-nth 0 (m2-meta-main term))))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-main) ()))))))||#

(local
 (encapsulate
   nil

   (local
    (use-arithmetic-5 nil))

   (local
    (defthm valid-sc-m2-PP+-OF-X-AND-REST
      (implies (and (valid-sc x a)
                    (valid-sc rest a))
               (valid-sc (m2-pp+-of-x-and-rest x rest term) a))
      :hints (("Goal"
               :in-theory (e/d (m2-PP+-OF-X-AND-REST
                                is-if
                                is-rp) ())))))

   (local
    (defthm valid-sc-m2-meta-fix-pps-aux
      (implies (and (valid-sc term a)
                    (rp-termp term))
               (valid-sc (m2-meta-fix-pps-aux term) a))
      :hints (("Goal"
               :expand ((VALID-SC
                         (LIST 'p+
                               (CADR (EX-FROM-RP TERM))
                               (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP
                                                            TERM))))
                         a)
                        (VALID-SC
                         (LIST 'p+
                               (CADR (CADR (EX-FROM-RP TERM)))
                               (M2-META-FIX-PPS-AUX (CADDR (EX-FROM-RP
                                                            TERM))))
                         a)
                        (VALID-SC ''0 A))
               :do-not '(preprocess)
               :in-theory (e/d (m2-meta-fix-pps-aux
                                is-rp
                                ex-from-rp-loose-is-ex-from-rp
                                is-if)
                               (not
                                (:REWRITE IS-IF-RP-TERMP)
                                (:DEFINITION EVENP)
                                (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                                (:TYPE-PRESCRIPTION IS-RP$INLINE)
                                (:TYPE-PRESCRIPTION EVENP2)
                                (:REWRITE RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS)
                                (:REWRITE QUOTEP-TERM-WITH-EX-FROM-RP)
                                rp-equal-cnt
                                (:DEFINITION RP-EQUAL)
                                (:TYPE-PRESCRIPTION RP-EQUAL)
                                (:REWRITE RP-EQUAL-SUBTERMS-REFLEXIVE)
                                (:REWRITE RP-EQUAL-REFLEXIVE)
                                (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                (:REWRITE ACL2::O-P-O-INFP-CAR)
                                (:DEFINITION ACL2::APPLY$-BADGEP)
                                (:TYPE-PRESCRIPTION VALID-SC)
                                (:TYPE-PRESCRIPTION RP-TERMP)
                                (:REWRITE IS-RP-PSEUDO-TERMP)
                                (:REWRITE
                                 ACL2::INTEGER-LISTP-IMPLIES-INTEGERP)
                                (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                                valid-sc
                                rp-termp
                                ex-from-rp
                                ex-from-rp-loose
                                (:type-prescription rp-equal-cnt)
                                (:rewrite acl2::fn-check-def-not-quote)
                                (:rewrite
                                 acl2::simplify-products-gather-exponents-equal)
                                (:rewrite acl2::acl2-numberp-x)
                                (:rewrite default-cdr)
                                (:definition eval-and-all)
                                (:rewrite acl2::rationalp-x)
                                (:rewrite default-car)

                                (:definition include-fnc)
                                (:rewrite acl2::prefer-positive-addends-equal)
                                (:rewrite acl2::simplify-sums-equal)
                                (:rewrite
                                 acl2::reduce-multiplicative-constant-equal)
                                (:rewrite
                                 acl2::reduce-additive-constant-equal)
                                (:rewrite acl2::equal-of-predicates-rewrite)
                                ))))))

   (defthm valid-sc-m2-meta-fix-pps
     (implies (and (valid-sc term a)
                   (rp-termp term))
              (valid-sc (m2-meta-fix-pps term) a))
     :hints (("Goal"
              :in-theory (e/d (M2-META-FIX-PPS
                               is-rp
                               ex-from-rp-loose-is-ex-from-rp
                               is-if)
                              ()))))

   (local
    (defthm valid-sc-m2-meta-extract-m2s
      (implies (and (valid-sc term a)
                    (rp-termp term))
               (valid-sc (mv-nth 0 (m2-meta-extract-m2s term)) a))
      :hints (("Goal"
               :in-theory (e/d (m2-meta-extract-m2s
                                is-rp
                                ex-from-rp-loose-is-ex-from-rp
                                is-if) ())))))

   (defthm valid-sc-m2-meta-main
     (implies (and (valid-sc term a)
                   (rp-termp term))
              (valid-sc (mv-nth 0 (m2-meta-main term)) a))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-main
                               is-rp
                               is-if) ()))))))

(local
 (encapsulate
   nil
   (local
    (defthm dont-rw-syntaxp-M2-META-EXTRACT-M2S
      (dont-rw-syntaxp (mv-nth 1 (m2-meta-extract-m2s term)))
      :hints (("Goal"
               :in-theory (e/d (m2-meta-extract-m2s) ())))))

   (defthm dont-rw-syntaxp-m2-meta-main
     (dont-rw-syntaxp (mv-nth 1 (m2-meta-main term)))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-main) ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(progn
  (local
   (in-theory (disable m2 m2-new f2 f2-new b+ type-fix p+)))

  (local
   (defthm m2-when-not-type-p
     (implies (not (type-p x))
              (equal (m2 x)
                     0))
     :hints (("Goal"
              :in-theory (e/d (m2 type-fix) ())))))

  )

(local
 (encapsulate
   nil

   (local
    (include-book "../greedy-lemmas"))

   (local
    (defthm rp-evl-of-m2-pp+-of-x-and-rest
      (implies (and (m2-meta-formula-checks state)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (sum b (rp-evlt (m2-pp+-of-x-and-rest x rest term) a))
                      (sum b
                           (rp-evlt x a)
                           (rp-evlt rest a))))
      :hints (("Goal"
               :in-theory (e/d (m2-pp+-of-x-and-rest) ())))))

   (local
    (defthm rp-evl-of-m2-pp+-of-x-and-rest2
      (implies (and (m2-meta-formula-checks state)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (m2 (rp-evlt (m2-pp+-of-x-and-rest x rest term) a))
                      (m2 (sum
                           (rp-evlt x a)
                           (rp-evlt rest a)))))
      :hints (("Goal"
               :in-theory (e/d (m2-pp+-of-x-and-rest) ())))))

   (local
    (defthmd rp-evl-of-ex-from-rp-reverse
      (implies (syntaxp (atom x))
               (equal (rp-evlt x a)
                      (rp-evlt (ex-from-rp x) a)))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp
                                is-rp) ())))))

   (local
    (defthm eval-of-pp+-when-m2-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'p+)
                    (CONSP (CDR X))
                    (CONSP (CdDR X))
                    (NOT (CDdDR X))
                    (rp-evl-meta-extract-global-facts)
                    (m2-meta-formula-checks state))
               (equal (rp-evlt x a)
                      (p+ (rp-evlt (cadr x) a)
                          (rp-evlt (caddr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-b+-when-m2-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'b+)
                    (CONSP (CDR X))
                    (CONSP (CdDR X))
                    (NOT (CDdDR X))
                    (rp-evl-meta-extract-global-facts)
                    (m2-meta-formula-checks state))
               (equal (rp-evlt x a)
                      (b+ (rp-evlt (cadr x) a)
                          (rp-evlt (caddr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of----when-m2-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '--)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (m2-meta-formula-checks state)
                    )
               (equal (rp-evlt x a)
                      (-- (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm eval-of-m2-when-m2-f2-meta-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'm2)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (m2-meta-formula-checks state)
                    )
               (equal (rp-evlt x a)
                      (m2 (rp-evlt (cadr x) a))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm rp-evl-of-rp-equal-derived
      (let ((term1 (CADR (EX-FROM-RP TERM)))
            (term2 (CADDR (EX-FROM-RP TERM))))
        (implies (and (force (rp-termp term1))
                      (force (rp-termp term2))
                      (rp-equal term1 term2))
                 (equal (rp-evlt term2 a)
                        (rp-evlt term1 a))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (EX-FROM-RP TERM)))
                                (term2 (CADDR (EX-FROM-RP TERM)))))
               :in-theory (disable rp-termp
                                   rp-evl-of-rp-equal
                                   ex-from-rp)))))

   (local
    (defthm rp-evl-of-rp-equal-derived-2
      (let ((term1 (CADR (EX-FROM-RP TERM)))
            (term2 (cadr (CADDR (EX-FROM-RP TERM)))))
        (implies (and (force (rp-termp term1))
                      (force (rp-termp term2))
                      (rp-equal term1 term2))
                 (equal (rp-evlt term2 a)
                        (rp-evlt term1 a))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (EX-FROM-RP TERM)))
                                (term2 (CADDR (EX-FROM-RP TERM)))))
               :in-theory (disable rp-termp
                                   rp-evl-of-rp-equal
                                   ex-from-rp)))))

   (local
    (defthm rp-evl-of-rp-equal-derived-3
      (let ((term1 (CADR (CADR (EX-FROM-RP TERM))))
            (term2 (CADR (CADR (CADDR (EX-FROM-RP TERM))))))
        (implies (and (force (rp-termp term1))
                      (force (rp-termp term2))
                      (rp-equal term1 term2))
                 (equal (rp-evlt term2 a)
                        (rp-evlt term1 a))))
      :hints (("Goal"
               :use ((:instance rp-evl-of-rp-equal
                                (term1 (CADR (EX-FROM-RP TERM)))
                                (term2 (CADDR (EX-FROM-RP TERM)))))
               :in-theory (disable rp-termp
                                   rp-evl-of-rp-equal
                                   ex-from-rp)))))

   (local
    (defthm dumb-lemma-0
      (equal (equal (m2 (sum a b))
                    (m2 (sum a c)))
             (equal (m2 b)
                    (m2 c)))
      :hints (("Goal"
               :in-theory (e/d (m2 sum type-fix) ())))))
   (local
    (defthm dumb-lemma-1
      (equal (RP-EVLT (EX-FROM-RP (CADDR (EX-FROM-RP TERM)))
                     A)
             (RP-EVLT  (CADDR (EX-FROM-RP TERM))
                      A))))

   (local
    (defthm dumb-lemma-1b
      (equal (EQUAL
              (M2 (SUM a b))
              (M2 (SUM c a)))
             (equal (m2 b)
                    (m2 c)))
      :hints (("Goal"
               :use ((:instance dumb-lemma-0))
               :in-theory (e/d () (dumb-lemma-0))))))
   
   (local
    (use-arithmetic-5 t))

   (local
    (defthm lemma2
      (implies (and (integerp x)
                    (evenp x))
               (equal (equal 0 (m2 x))
                      t))
      :hints (("Goal"
               :in-theory (e/d (m2 mod type-fix) ())))))

   (local
    (use-arithmetic-5 t))

   (local
    (defthm d-lemma12
      (equal (equal (m2 (sum a x))
                    (m2 (sum y (-- a))))
             (equal (m2 x)
                    (m2 y)))
      :hints (("Goal"
               :in-theory (e/d ( type-fix ) (--))))))

   (local
    (defthm lemma3
      (implies (and (evenp2 x)
                    (integerp x))
               (equal (m2 (sum x y))
                      (m2 y)))
      :hints (("Goal"
               :in-theory (e/d (evenp2
                                type-fix
                                m2
                                sum) ())))))

   (local
    (use-arithmetic-5 nil))

  

   (defthm m2-rp-evl-of-m2-meta-fix-pps-aux
     (implies (and (m2-meta-formula-checks state)
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (m2 (rp-evlt (m2-meta-fix-pps-aux term) a))
                     (m2 (rp-evlt term a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (m2-meta-fix-pps-aux term)
              :in-theory (e/d (m2-meta-fix-pps-aux
                               rp-evl-of-ex-from-rp-reverse
                               ex-from-rp-loose-is-ex-from-rp)
                              (ex-from-rp-loose
                               rp-trans
                               RP-EVLT-OF-EX-FROM-RP
                               (:REWRITE IS-RP-PSEUDO-TERMP)
                               (:REWRITE IS-IF-RP-TERMP)
                               (:REWRITE
                                ACL2::INTEGER-LISTP-IMPLIES-INTEGERP)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                               (:TYPE-PRESCRIPTION RP-EQUAL)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE
                                ACL2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                               (:TYPE-PRESCRIPTION O-P)
                               (:REWRITE
                                ACL2::REDUCE-ADDITIVE-CONSTANT-EQUAL)
                               (:REWRITE ACL2::EQUAL-OF-PREDICATES-REWRITE)
                               (:REWRITE ACL2::|(equal c (/ x))|)
                               (:REWRITE ACL2::|(equal c (- x))|)
                               (:REWRITE ACL2::|(equal (/ x) c)|)
                               EVL-OF-EXTRACT-FROM-RP
                               --
                               ex-from-rp
                               rp-termp
                               rp-equal
                               (:REWRITE
                                ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                               (:REWRITE ACL2::ACL2-NUMBERP-X)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE RP-EQUAL-SUBTERMS-REFLEXIVE)
                               (:REWRITE ACL2::RATIONALP-X)
                               (:REWRITE EX-FROM-SYNP-LEMMA1)
                               (:REWRITE DEFAULT-CAR)
                               (:DEFINITION IS-SYNP$INLINE)
                               (:REWRITE ACL2::SIMPLIFY-SUMS-EQUAL)
                               (:REWRITE RP-EQUAL-REFLEXIVE)

                               RP-EVL-OF-VARIABLE
                               rp-termp
                               (:TYPE-PRESCRIPTION M2)
                               (:TYPE-PRESCRIPTION RP-TERMP)

                               (:REWRITE M2-WHEN-NOT-TYPE-P)
                               (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                               (:REWRITE QUOTEP-TERM-WITH-EX-FROM-RP)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)

                               )))))

   (local
    (use-arithmetic-5 t))

   (local
    (defthm dumb-lemma-2
      (equal (equal (m2 (sum a x))
                    (m2 (sum b x)))
             (equal (m2 a)
                    (m2 b)))
      :hints (("Goal"
               :in-theory (e/d (sum m2 type-fix) ())))))

   (local
    (defthm dumb-lemma-3
      (equal (equal (m2 x)
                    (m2 (sum term x)))
             (equal (m2 term)
                    0))
      :hints (("Goal"
               :in-theory (e/d (m2 sum type-fix) ())))))

   (local
    (defthmd rp-evl-of-ex-from-rp-reverse-2
      (implies (syntaxp (or (atom x)
                            (equal x '(CAR (CDR (EX-FROM-RP TERM))))))
               (equal (rp-evlt x a)
                      (rp-evlt (ex-from-rp x) a)))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp
                                is-rp) ())))))

   (local
    (defthmd dumb-lemma-4
      (equal (EQUAL
              (M2 (SUM (RP-EVLT (CADR (EX-FROM-RP (CADR (EX-FROM-RP TERM))))
                               A)
                       (RP-EVLT (MV-NTH 0
                                       (M2-META-EXTRACT-M2S (CADDR (EX-FROM-RP TERM))))
                               A)))
              (M2 (SUM (RP-EVLT (CADR (EX-FROM-RP TERM)) A)
                       (RP-EVLT (CADDR (EX-FROM-RP TERM)) A))))
             (EQUAL
              (M2 (SUM (RP-EVLT (CADR (EX-FROM-RP (CADR (EX-FROM-RP TERM))))
                               A)
                       (RP-EVLT (MV-NTH 0
                                       (M2-META-EXTRACT-M2S (CADDR (EX-FROM-RP TERM))))
                               A)))
              (M2 (SUM (RP-EVLT (ex-from-rp (CADR (EX-FROM-RP TERM))) A)
                       (RP-EVLT (CADDR (EX-FROM-RP TERM)) A)))))))

   (local
    (defthmd dumb-lemma-5-lemma
      (implies (rp-termp term)
               (implies (equal (ex-from-rp-loose term) ''0)
                        (equal (rp-evlt term a) 0)))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (ex-from-rp-loose-is-ex-from-rp
                                rp-evl-of-ex-from-rp-reverse)
                               (rp-trans))))))

   (local
    (defthm dumb-lemma-5
      (implies (and (or (equal (ex-from-rp-loose (M2-META-FIX-PPS-AUX term))
                               ''0)
                        (equal (ex-from-rp (M2-META-FIX-PPS-AUX term)) ''0))
                    (rp-termp term)
                    (and (m2-meta-formula-checks state)
                         (rp-evl-meta-extract-global-facts :state state)))
               (and (equal (m2 (rp-evlt term a)) 0)
                    (EQUAL (m2 (RP-EVLT (EX-FROM-RP TERM) A)) 0)))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance m2-rp-evl-of-m2-meta-fix-pps-aux)
                     (:instance dumb-lemma-5-lemma
                                (term (M2-META-FIX-PPS-AUX TERM))))
               :in-theory (e/d (ex-from-rp-loose-is-ex-from-rp)
                               (rp-termp
                                EX-FROM-RP-LEMMA1
                                IS-RP-PSEUDO-TERMP
                                INCLUDE-FNC
                                ex-from-rp
                                m2-rp-evl-of-m2-meta-fix-pps-aux))))))

   (local
    (defthm dumb-lemma-5-derived-1
      (b* ((term (EX-FROM-RP (CADR (EX-FROM-RP TERM)))))
        (implies (and (or (equal (ex-from-rp-loose (M2-META-FIX-PPS-AUX term))
                                 ''0)
                          (equal (ex-from-rp (M2-META-FIX-PPS-AUX term)) ''0))
                      (rp-termp term)
                      (and (m2-meta-formula-checks state)
                           (rp-evl-meta-extract-global-facts :state state)))
                 (and (equal (m2 (rp-evlt term a)) 0)
                      (EQUAL (m2 (RP-EVLT (EX-FROM-RP TERM) A)) 0))))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance dumb-lemma-5
                                (term (EX-FROM-RP (CADR (EX-FROM-RP TERM))))))
               :in-theory (e/d ()
                               (rp-termp
                                dumb-lemma-5
                                EVL-OF-EXTRACT-FROM-RP
                                EX-FROM-RP-LEMMA1
                                IS-RP-PSEUDO-TERMP
                                INCLUDE-FNC
                                ex-from-rp
                                m2-rp-evl-of-m2-meta-fix-pps-aux
                                ))))))

   (local
    (defthm dumb-lemma6
      (implies (and (CONSP term)
                    (EQUAL (CAR term) 'p+)
                    (CONSP (CDR term))
                    (CONSP (CDDR term))
                    (NOT (CDDDR term))
                    (m2-meta-formula-checks state)
                    (rp-evl-meta-extract-global-facts :state state)
                    (or (equal (m2 (rp-evlt term a)) 0)
                        (equal (rp-evlt term a) 0)))
               (equal (m2 (SUM (RP-EVLT (EX-FROM-RP (CADR term))
                                       A)
                               (RP-EVLT (CADDR term) A)))
                      0))
      :hints (("Goal"
               :in-theory (e/d ()
                               (
                                rp-termp))))))

   (local
    (defthm dumb-lemma-5-derived-2
      (b* ((term term))
        (implies (and  (CONSP (EX-FROM-RP TERM))
                       (EQUAL (CAR (EX-FROM-RP TERM)) 'p+)
                       (CONSP (CDR (EX-FROM-RP TERM)))
                       (CONSP (CDDR (EX-FROM-RP TERM)))
                       (NOT (CDDDR (EX-FROM-RP TERM)))
                       (equal (ex-from-rp (M2-META-FIX-PPS-AUX term)) ''0)
                       
                       (rp-termp term)
                       (and (m2-meta-formula-checks state)
                            (rp-evl-meta-extract-global-facts :state state)))
                 (and (equal (M2 (SUM (RP-EVLT (EX-FROM-RP (CADR (EX-FROM-RP TERM)))
                                              A)
                                      (RP-EVLT (CADDR (EX-FROM-RP TERM)) A)))
                             0))))
      :hints (("Goal"
               :do-not-induct t
               :use ((:instance dumb-lemma-5))
               :in-theory (e/d ()
                               (rp-termp
                                SUM-COMM-1-WITH-LOOP-STOPPER
                                dumb-lemma-5
                                RP-EVLT-OF-EX-FROM-RP
                                EVL-OF-EXTRACT-FROM-RP
                                EX-FROM-RP-LEMMA1
                                IS-RP-PSEUDO-TERMP
                                INCLUDE-FNC
                                ex-from-rp
                                m2-rp-evl-of-m2-meta-fix-pps-aux
                                ))))))

   (local
    (defthm dumb-lemma7
      (implies (AND (m2-meta-formula-checks STATE)
                    
                    (RP-TERMP TERM)
                    (RP-EVL-META-EXTRACT-GLOBAL-FACTS :STATE STATE)
                    (EQUAL (EX-FROM-RP (M2-META-FIX-PPS-AUX TERM))
                           ''0))
               (equal (m2 (RP-EVLT (M2-META-FIX-PPS-AUX (EX-FROM-RP TERM))
                                  A))
                      0))))

   (defthm m2-rp-evl-of-m2-meta-fix-pps
     (implies (and (m2-meta-formula-checks state)
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (m2 (rp-evlt (m2-meta-fix-pps term) a))
                     (m2 (rp-evlt term a))))
     :otf-flg t
     :hints (("Subgoal *1/2"
              :use ((:instance dumb-lemma-5-derived-1)))

             ("Goal"
              :induct (m2-meta-fix-pps term)
              :do-not-induct t
              :in-theory (e/d (m2-meta-fix-pps
                               rp-evl-of-ex-from-rp-reverse-2
                               dumb-lemma-4
                               ex-from-rp-loose-is-ex-from-rp)
                              (EVL-OF-EXTRACT-FROM-RP
                               rp-trans
                               (:REWRITE RP-EVL-OF-RP-EQUAL-DERIVED)
                               SUM-COMM-1-WITH-LOOP-STOPPER
                               SUM-COMM-2-WITH-LOOP-STOPPER
                               SUM-REORDER
                               rp-evlt-of-ex-from-rp
                               (:DEFINITION RP-TERMP)
                               (:DEFINITION INCLUDE-FNC)
                               (:DEFINITION EX-FROM-RP)
                               (:REWRITE NOT-INCLUDE-RP)
                               (:DEFINITION RP-TERM-LISTP)
                               (:REWRITE IS-IF-RP-TERMP)
                               (:REWRITE
                                ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                               (:REWRITE ACL2::ACL2-NUMBERP-X)
                               (:DEFINITION TRUE-LISTP)
                               (:REWRITE IS-RP-PSEUDO-TERMP)
                               (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2))))))

   (local
    (defthm m2-rp-evl-of-M2-META-EXTRACT-M2S
      (implies (and (m2-meta-formula-checks state)

                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts :state state))
               (equal (m2 (rp-evlt (mv-nth 0 (M2-META-EXTRACT-M2S term)) a))
                      (m2 (rp-evlt term a))))
      :hints (("Goal"
               :expand ((:free (x) (rp-trans (cons 'merge-b+ x)))) 
               :in-theory (e/d (M2-META-EXTRACT-M2S
                                dumb-lemma-4
                                rp-evl-of-ex-from-rp-reverse
                                ex-from-rp-loose-is-ex-from-rp)
                               (EVL-OF-EXTRACT-FROM-RP
                                (:REWRITE RP-EVL-OF-RP-EQUAL-DERIVED)
                                (:DEFINITION RP-TERMP)
                                (:DEFINITION INCLUDE-FNC)
                                (:DEFINITION EX-FROM-RP)
                                (:REWRITE NOT-INCLUDE-RP)
                                (:DEFINITION RP-TERM-LISTP)
                                (:REWRITE IS-IF-RP-TERMP)
                                RP-EVL-OF-VARIABLE
                                --
                                rp-evlt-of-ex-from-rp
                                rp-trans
                                (:REWRITE DEFAULT-CDR)
                                (:REWRITE EX-FROM-SYNP-LEMMA1)
                                (:DEFINITION IS-SYNP$INLINE)
                                (:REWRITE QUOTEP-TERM-WITH-EX-FROM-RP)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE
                                 ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                                (:REWRITE ACL2::ACL2-NUMBERP-X)
                                (:DEFINITION TRUE-LISTP)
                                (:REWRITE IS-RP-PSEUDO-TERMP)
                                SUM-COMM-1-WITH-LOOP-STOPPER
                                (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)))))))

   (defthm rp-evl-of-m2-meta-main
     (implies (and (m2-meta-formula-checks state)
                   
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts :state state))
              (equal (rp-evlt (mv-nth 0 (m2-meta-main term)) a)
                     (rp-evlt term a)))
     :hints (("Goal"
              :in-theory (e/d (m2-meta-main)
                              (m2)))))))

(defthm m2-meta-main-valid-rp-meta-rulep
  (implies (and (m2-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'm2-meta-main
                             :trig-fnc 'm2-new
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp-meta-valid-syntaxp)
                           (rp-termp
                            rp-term-listp
                            m2-meta-main
                            valid-sc)))))

(rp::add-meta-rules
 m2-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'm2-meta-main
        :trig-fnc 'm2-new
        :dont-rw t
        :valid-syntax t)))
