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
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(include-book "../mult-defs")

(local
 (include-book "arithmetic-5/top" :dir :system))

(include-book "pp-order-fncs")

(include-book "pp-flatten-meta")

(local
 (include-book "pp-flatten-meta-syntax-correct"))

(local
 (in-theory (enable n2b f2 m2 d2 p+ b+ ba  pp type-fix merge-pp+)))


(local
 (in-theory (disable rp-trans
                     rp-evlt-of-ex-from-rp)))

(local
 (encapsulate
   nil

   (defthmd pp-sum-0-1
     (equal (pp-sum 0 a b)
            (pp-sum a b)))

   (defthmd pp-sum-0-2
     (equal (pp-sum a 0 b)
            (pp-sum a b)))

   (defthmd pp-sum-nil-2
     (equal (pp-sum a 0 b)
            (pp-sum a b)))

   (defthmd pp-sum-0-3
     (equal (pp-sum a b 0)
            (pp-sum a b)))

   (defthmd pp-sum-nil-3
     (equal (pp-sum a b nil)
            (pp-sum a b)))

   (defthmd hide-x-is-x-all
     (equal (hide x) x)
     :hints (("Goal"
              :expand (hide x))))))

(define ex-from-rp/type-fix (term)
  (case-match term
    (('type-fix x)
     (ex-from-rp/type-fix x))
    (('rp & x)
     (ex-from-rp/type-fix x))
    (& term)))

(define ex-from-type-fix (term)
  :inline t
  (case-match term
    (('type-fix x)
     x)
    (& term)))

(local
 (defthm ex-from-rp/type-fix-of-ex-from-type-fix
   (equal (ex-from-rp/type-fix (ex-from-type-fix term))
          (ex-from-rp/type-fix term))
   :hints (("Goal"
            :induct (ex-from-rp/type-fix term)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp/type-fix
                             ex-from-type-fix) ())))))

(local
 (defthm cons-count-of-ex-from-rp/type-fix-1
   (<= (cons-count (ex-from-rp/type-fix x))
       (cons-count x))
   :hints (("Goal"
            :induct (ex-from-rp/type-fix x)
            :in-theory (e/d (ex-from-rp/type-fix
                             ex-from-rp/type-fix-of-ex-from-type-fix
                             cons-count) ())))))

(local
 (defthm cons-count-of-ex-from-rp-loose
   (<= (cons-count (EX-FROM-RP-LOOSE x))
       (cons-count x))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :induct (EX-FROM-RP-LOOSE x)
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             is-rp-loose
                             EX-FROM-TYPE-FIX
                             cons-count) ())))))

(local
 (defthm cons-count-of-ex-from-rp-loose
   (<= (cons-count (EX-FROM-RP-LOOSE x))
       (cons-count x))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :induct (EX-FROM-RP-LOOSE x)
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             is-rp-loose
                             EX-FROM-TYPE-FIX
                             cons-count) ())))))

(local
 (defthm cons-count-of-dummy-1
   (implies (<= (cons-count x) (cons-count y))
            (<= (cons-count x)
                (+ 2 (cons-count y))))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             is-rp-loose
                             EX-FROM-TYPE-FIX
                             cons-count) ())))))

(local
 (defthm cons-count-of-EX-FROM-RP-LOOSE-EX-FROM-TYPE-FIX
   (<= (cons-count (EX-FROM-RP-LOOSE (EX-FROM-TYPE-FIX x)))
       (cons-count x))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            ;;:induct (ex-from-rp/type-fix x)
            :in-theory (e/d (EX-FROM-RP-LOOSE
                             is-rp-loose
                             EX-FROM-TYPE-FIX
                             cons-count) ())))))

(local
 (defthm cons-count-of-ex-from-type-fix-1
   (<= (cons-count (ex-from-type-fix x))
       (cons-count x))
   :hints (("Goal"
; :induct (ex-from-type-fix x)
            :in-theory (e/d (ex-from-type-fix
                             cons-count) ())))))


(define resolve-pp-sum-order-rec (y z)
  :measure (+ (cons-count y)
              (cons-count z))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig-y (ex-from-type-fix y))
       (y (ex-from-rp/type-fix orig-y))
       (orig-z (ex-from-type-fix z))
       (z (ex-from-rp/type-fix orig-z))
       ((mv car-y last-y)
        (case-match y (('p+ a &) (mv a nil))
          (& (mv y t))))
       ((mv car-z last-z)
        (case-match z (('p+ a &) (mv a nil))
          (& (mv z t)))))
    (cond  ((pp-order car-y car-z)
            (if last-y
                `(p+ ,orig-y ,orig-z)
              (b* ((rest (resolve-pp-sum-order-rec (caddr y) orig-z)))
                (if (equal rest ''0)
                    car-y
                  `(p+ ,car-y ,rest)))))

           ((should-sum-terms-cancel car-y car-z)
            (cond ((and last-z
                        last-y)
                   ''0)
                  (last-z
                   (caddr y))
                  (last-y
                   (caddr z))
                  (t
                   (resolve-pp-sum-order-rec (caddr y)
                                             (caddr z)))))

           (last-z
            `(p+ ,orig-z ,orig-y))

           (t (b* ((rest (resolve-pp-sum-order-rec orig-y (caddr z))))
                (if (equal rest ''0)
                    car-z
                  `(p+ ,car-z ,rest)))))))

(local
 (in-theory (enable ex-from-rp/type-fix-of-ex-from-type-fix)))

(define pp-instance-p (term)
  :inline t
  (b* ((term (ex-from-rp-loose term))
       (term (case-match term (('-- a) a) (& term))))
    (and (consp term)
         (or (eq (car term)
                 'binary-and)
             (eq (car term)
                 'binary-?)
             (eq (car term)
                 'binary-not)
             (eq (car term)
                 'binary-xor)
             (eq (car term)
                 'binary-or)))))

(define is-pp-sum-sorted-cw (term)
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('p+ x y)
       (case-match y
         (('p+ a &)
          (and (or (not (pp-order a x))
                   (cw "Bad order!: ~p0; ~p1 ~%" x a))
               (is-pp-sum-sorted-cw y)))
         (&
          (or (not (pp-order y x))
              (cw "Bad order!: ~p0; ~p1 ~%" x y)))))
      (& t))))

#|(make-flag include-fnc :defthm-macro-name defthm-include-fnc)||#

(define resolve-pp-sum-order-preprocess (x)
  :inline t
  (b* ((x (case-match x (('p+ ''0 e) e) (& x)))
       (x (if (pp-instance-p x) (flatten-pp-main x) x)))
    x))


(defun resolve-pp-sum-order (term)
  (declare (xargs :guard t
                  :verify-guards t))
  (case-match term
    (('merge-pp+ x z)
     (b* ((x (resolve-pp-sum-order-preprocess x))
          (z (resolve-pp-sum-order-preprocess z))
          (res (cond ((equal x ''0)
                      z)
                     ((equal z ''0)
                      x)
                     (t
                      (resolve-pp-sum-order-rec x z))))
          (res
           (case-match res
             (('p+ & &)
              res)
             (''0
              res)
             (&
              `(p+ '0 ,res)))))
       res ;;(mv res dont-rw)
       ))
    (& term ;;(mv term nil)
       )))

(defun resolve-pp-sum-order-main (term)
  (declare (xargs :guard t
                  :verify-guards t))
  (b* ((result (resolve-pp-sum-order term))
       #|(- (if (include-fnc first-res 'type-fix)
       (cw "This result has type-fix in it ~p0. orig ~p1 ~%"
       first-res term)
       nil))||#)
    (mv result t #|dont-rw||#)))

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

(encapsulate
  nil
  (local

   (in-theory (disable
               ex-from-rp
               pp-order
               #|resolve-pp-sum-order-rec-redef||#
               lexorder2
               (:REWRITE ACL2::|(equal (if a b c) x)|)
               (:REWRITE ACL2::|(equal x (if a b c))|))))

  (def-formula-checks
    pp-sum-meta-formal-checks
    (p+ merge-pp+ cons hide
        times2
        minus b+ merge-b+
        merge-pp-and
        merge-pp-or
        binary-not binary-and bitp binary-or binary-? bit-of binary-xor
        f2 m2
        d2 --
        resolve-pp-sum-order-rec
        #|resolve-pp-sum-order-rec-2||#
        resolve-pp-sum-order
        resolve-pp-sum-order-main
        #|resolve-pp-sum-order-dont-rw||#)))

(local
 (defthm pp-sum-meta-formal-checks-implies-pp-flatten-formula-checks
   (implies (pp-sum-meta-formal-checks state)
            (pp-flatten-formula-checks state))
   :hints (("Goal"
            :in-theory (e/d (pp-sum-meta-formal-checks
                             pp-flatten-formula-checks) ())))))

(local
 (in-theory (enable hide-x-is-x-all
                    pp-sum-0-3
                    pp-sum-nil-2
                    pp-sum-0-2
                    pp-sum-0-1 )))

(local
 (defthmd merge-pp+-is-pp+
   (equal (merge-pp+ x y)
          (p+ x y))))

(local
 (defthmd pp-sum-reorder
   (equal (p+ (p+ x y) z)
          (p+ x (p+ y z)))))

(local
 (defthmd pp-sum-comm-1
   (implies (syntaxp (pp-order x y))
            (equal (p+ y x)
                   (p+ x y)))
   :rule-classes ((:rewrite :loop-stopper nil))))

(local
 (defthmd pp-sum-comm-1-any
   (equal (p+ y x)
          (p+ x y))))

(local
 (defthmd pp-sum-comm-2
   (implies (syntaxp (pp-order x y))
            (equal (p+ y (p+ x z))
                   (p+ x (p+ y z))))
   :rule-classes ((:rewrite :loop-stopper nil))))

(local
 (defthmd pp-sum-comm-2-any
   (equal (p+ y (p+ x z))
          (p+ x (p+ y z)))))

(local
 (defthmd  pp-sum-o-is-type-fix
   (and (equal (pp-sum a 0)
               (type-fix a))
        (equal (pp-sum 0 a)
               (type-fix a)))
   :hints (("Goal"
            :in-theory (e/d (pp-sum type-fix) ())))))

(local
 (defthm type-fix-of-pp-sum
   (and (equal (type-fix (pp-sum a b))
               (pp-sum a b))
        (equal (pp-sum a (type-fix b))
               (pp-sum a b))
        (equal (pp-sum (type-fix b) a)
               (pp-sum a b)))))

(local
 (defthm rpp-lemma1
   (implies (equal x (p+ a b))
            (equal (equal x (p+ 0 x)) t))))

(local
 (defthm lemma8
   (implies (EQUAL (EX-FROM-RP X) ''0)
            (equal (RP-EVL X A)
                   0))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp
                             is-rp)
                            (EX-FROM-RP-LEMMA1))))))

(local
 (defthmd rp-evlt-of-ex-from-rp-reverse
   (implies (syntaxp (atom x))
            (equal (rp-evlt x a)
                   (rp-evlt (ex-from-rp x) a)))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp
                             is-rp) ())))))

(local
 (defthm lemma9
   (implies (equal x (pp-sum y (rp-evlt (ex-from-rp z) a)))
            (equal (equal (pp-sum m x)
                          (pp-sum y m (rp-evlt z a)))
                   t))
   :hints (("Goal"
            :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse)
                            (evl-of-extract-from-RP))))))

(local
 (defun should-b+-cancel-aux (x y)
   (if (case-match x (('-- &) t))
       (rp-equal-cnt (cadr x) y 0)
     nil)))

(local
 (defthm eval-of----when-pp-sum-meta-formal-checks
   (implies (and (CONSP X)
                 (EQUAL (CAR X) '--)
                 (CONSP (CDR X))
                 (NOT (CDDR X))
                 (rp-evl-meta-extract-global-facts)
                 (pp-sum-meta-formal-checks state)
                 (syntaxp (or (atom x)
                              (and (equal (car x) 'ex-from-rp)
                                   (consp (cdr x))
                                   (atom (cadr x))))))
            (equal (rp-evlt x a)
                   (-- (rp-evlt (cadr x) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm rp-termp-cadr
   (implies (and (rp-termp term)
                 (consp term)
                 (not (quotep term))
                 (consp (cdr term)))
            (rp-termp (cadr term)))))

(local
 (defthm rp-termp-caddr
   (implies (and (rp-termp term)
                 (consp term)
                 (not (quotep term))
                 (consp (cdr term))
                 (consp (cddr term)))
            (rp-termp (caddr term)))))

(local
 (defthm pp-sum-when-should-b+-cancel-lemma
   (implies (and (should-b+-cancel-aux x y)
                 (rp-termp x)
                 (rp-termp y)
                 (rp-evl-meta-extract-global-facts)
                 (pp-sum-meta-formal-checks state))
            (and (equal (pp-sum (rp-evlt x a)
                                (rp-evlt y a))
                        0)
                 (equal (pp-sum (rp-evlt x a)
                                (rp-evlt y a)
                                b)
                        (pp-sum b 0))
                 (equal (pp-sum (rp-evlt y a)
                                (rp-evlt x a))
                        0)
                 (equal (pp-sum (rp-evlt y a)
                                (rp-evlt x a)
                                b)
                        (pp-sum b 0))))
   :hints (("goal"
            :use ((:instance rp-evlt-of-rp-equal
                             (term1 y)
                             (term2 (cadr x))))
            :in-theory (e/d (is-rp
                             type-fix
                             --
                             ex-from-rp)
                            (rp-termp
                             evl-of-extract-from-rp
                             ex-from-rp
                             (:definition not)
                             b+
                             (:definition fix)
                             (:definition ifix)
                             (:rewrite rp-evl-of-variable)))))))

(local
 (defthm should-b+-cancel-aux-redef
   (equal (should-sum-terms-cancel x y)
          (or (SHOULD-B+-CANCEL-aux x y)
              (SHOULD-B+-CANCEL-aux y x)))
   :hints (("Goal"
            :in-theory (e/d (should-sum-terms-cancel) ())))))

(local
 (defthm pp-sum-when-should-b+-cancel
   (implies (and (should-sum-terms-cancel x y)
                 (rp-termp x)
                 (rp-termp y)
                 (rp-evl-meta-extract-global-facts)
                 (pp-sum-meta-formal-checks state))
            (and (equal (pp-sum (rp-evlt x a)
                                (rp-evlt y a))
                        0)
                 (equal (pp-sum (rp-evlt x a)
                                (rp-evlt y a)
                                b)
                        (pp-sum b 0))
                 (equal (pp-sum (rp-evlt y a)
                                (rp-evlt x a))
                        0)
                 (equal (pp-sum (rp-evlt y a)
                                (rp-evlt x a)
                                b)
                        (pp-sum b 0))))
   :hints (("Goal"
            :use ((:instance rp-evl-of-rp-equal
                             (term1 y)
                             (term2 (cadr x))))
            :in-theory (e/d ()
                            (rp-termp
                             EVL-OF-EXTRACT-FROM-RP
                             EX-FROM-RP
                             (:DEFINITION NOT)
                             b+
                             p+
                             should-sum-terms-cancel
                             SHOULD-B+-CANCEL-aux
                             --
                             (:DEFINITION FIX)
                             (:DEFINITION IFIX)
                             (:REWRITE RP-EVL-OF-VARIABLE)))))))

#|(local
 (defthm type-fix-of-a-is-a-type-fixed-fnc
   (implies (and (rp-evl-meta-extract-global-facts)
                 (pp-sum-meta-formal-checks state)
                 (is-a-type-fixed-fnc term))
            (EQUAL (type-fix (rp-evl term A))
                   (RP-EVL term A)))
   :hints (("Goal"
            :in-theory (e/d (is-a-type-fixed-fnc
                             times2
                             minus)
                            ())))))||#

(local
 (in-theory
  (disable (:DEFINITION ACL2::APPLY$-BADGEP)
           (:DEFINITION SUBSETP-EQUAL)
           (:DEFINITION MEMBER-EQUAL)
           (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
           (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
           (:REWRITE ACL2::RATIONALP-X)
           (:REWRITE ACL2::ACL2-NUMBERP-X)
           (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
           (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
           (:DEFINITION ACL2::WEAK-APPLY$-BADGE-P)
           (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 2)
           (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL))))

(local
 (defthm rp-termp-of-ex-from-rp/type-fix
   (implies (rp-termp term)
            (rp-termp (ex-from-rp/type-fix term)))
   :hints (("Goal"
            :induct (ex-from-rp/type-fix term)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp/type-fix)
                            ((:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                             (:REWRITE
                              ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION NATP)

                             (:REWRITE
                              ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                             ))))))

(local
 (defthm rp-termp-of-ex-from-type-fix
   (implies (rp-termp term)
            (rp-termp (ex-from-type-fix term)))
   :hints (("Goal"
;:induct (ex-from-type-fix term)
            :do-not-induct t
            :in-theory (e/d (ex-from-type-fix)
                            ((:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                             (:REWRITE
                              ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION NATP)

                             (:REWRITE
                              ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                             ))))))

(local
 (defthm rp-termp-resolve-pp-sum-order-rec
   (implies (and (rp-termp x)
                 (rp-termp y))
            (rp-termp (resolve-pp-sum-order-rec x y)))
   :hints (("Goal" :induct (resolve-pp-sum-order-rec x y)
            :in-theory (e/d
                        (RESOLVE-PP-SUM-ORDER-REC)
                        (pp-order
                         SHOULD-B+-CANCEL-AUX-REDEF
                         ex-from-rp))))))

(local
 (defthm eval-of-type-fix-when-pp-sum-meta-formal-checks
   (implies (and (CONSP X)
                 (EQUAL (CAR X) 'type-fix)
                 (CONSP (CDR X))
                 (NOT (CDdR X))
                 (rp-evl-meta-extract-global-facts)
                 (pp-sum-meta-formal-checks state))
            (equal (rp-evlt x a)
                   (type-fix (rp-evlt (cadr x) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans)
                            (type-fix))))))

(local
 (defthm eval-of-pp-sum
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (equal (car term) 'p+)
                 (consp term)
                 (consp (cdr term))
                 (consp (cddr term))
                 (not (cdddr term)))
            (equal (rp-evlt term a)
                   (pp-sum (rp-evlt (cadr term) a)
                           (rp-evlt (caddr term) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) (pp-sum))))))

(local
 (defthm eval-of-merge-pp-sum
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (equal (car term) 'merge-pp+)
                 (consp term)
                 (consp (cdr term))
                 (consp (cddr term))
                 (not (cdddr term)))
            (equal (rp-evlt term a)
                   (merge-pp+ (rp-evlt (cadr term) a)
                              (rp-evlt (caddr term) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) (pp-sum))))))


(local
 (defthm resolve-pp-sum-order-rec-correct-dummy-lemma1-lemma
   (implies (equal (type-fix evl)
                   (PP-SUM y caddr-x))
            (equal (equal (pp-sum cadr-x evl)
                          (PP-SUM y cadr-x
                                  caddr-x))
                   t))))

(local
 (defthm resolve-pp-sum-order-rec-correct-dummy-lemma1
   (implies (and (equal (type-fix evl)
                        (PP-SUM y (RP-EVLT (EX-FROM-RP (CADDR x))  A))))
            (equal (equal (pp-sum (RP-EVLT (cadr x) A) evl)
                          (PP-SUM y (RP-EVLT (CADR x) A)
                                  (RP-EVLT (CADDR x) A)))
                   t))
   :hints (("Goal"
            :do-not '(preprocess)
            :use ((:instance
                   resolve-pp-sum-order-rec-correct-dummy-lemma1-lemma
                   (caddr-x (RP-EVLT (CADDR x) A))
                   (cadr-x (RP-EVLT (CADR x) A))))
            :in-theory (e/d (rp-evlt-of-ex-from-rp)
                            (ex-from-rp
                             CAR-CDR-ELIM
                             resolve-pp-sum-order-rec-correct-dummy-lemma1-lemma
                             pp-sum
                             type-fix))))))

(local
 (defthm eval-of-ex-from-rp/type-fix
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (type-fix (rp-evlt (ex-from-rp/type-fix term) a))
                   (type-fix (rp-evlt term a))))
   :hints (("Goal"
            :induct (ex-from-rp/type-fix term)
            :do-not-induct t
            :in-theory (e/d (ex-from-rp/type-fix
                             rp-trans) ())))))

(local
 (defthm eval-of-ex-from-type-fix
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (type-fix (rp-evlt (ex-from-type-fix term) a))
                   (type-fix (rp-evlt term a))))
   :hints (("Goal"
;:induct (ex-from-type-fix term)
            :in-theory (e/d (ex-from-type-fix) ())))))

(local
 (defthm eval-of-ex-from-type-fix-2
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts))
            (and (equal (pp-sum (rp-evlt (ex-from-type-fix term) a)
                                other)
                        (pp-sum (rp-evlt (ex-from-rp/type-fix term) a)
                                other))
                 (equal (pp-sum other
                                (rp-evlt (ex-from-type-fix term) a))
                        (pp-sum other
                                (rp-evlt (ex-from-rp/type-fix term) a)))))
   :hints (("Goal"
            :in-theory (e/d () (type-fix))))))

(local
 (defthm resolve-pp-sum-order-rec-correct-dummy-lemma2
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (equal (type-fix evl)
                        (PP-SUM cadr-x caddr-x (RP-EVLT (ex-from-rp/type-fix caddr-y) A))))
            (equal (equal (pp-sum cadr-y evl)
                          (pp-sum cadr-x cadr-y caddr-x (rp-evlt caddr-y a)))
                   t))
   :hints (("Goal"
            :use ((:instance eval-of-ex-from-rp/type-fix
                             (term caddr-y)))
            :do-not '(preprocess)
            :in-theory (e/d (rp-evl-of-ex-from-rp
                             ex-from-rp/type-fix
                             pp-sum-comm-2
                             pp-sum
                             type-fix
                             pp-sum-comm-1
                             pp-sum-reorder)
                            (ex-from-rp
                             eval-of-ex-from-rp/type-fix))))))

(local
 (defthmd pp-sum-of-eval-to-to-ex-from-type-fix-rp
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (syntaxp (atom x)))
            (and (equal (pp-sum (rp-evlt x a) y)
                        (pp-sum (rp-evlt (ex-from-rp/type-fix x) a) y))
                 (equal (pp-sum y (rp-evlt x a))
                        (pp-sum y
                                (rp-evlt (ex-from-rp/type-fix x) a)))))
   :hints (("Goal"
            :do-not-induct t
            :induct (ex-from-rp/type-fix x)
            :in-theory (e/d (ex-from-rp/type-fix
                             rp-trans
                             eval-of-type-fix-when-pp-sum-meta-formal-checks)
                            ())))))

(local
 (defthmd type-fix-of-eval-to-to-ex-from-type-fix-rp
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (syntaxp (atom x)))
            (and (equal (equal (type-fix (rp-evlt x a)) m)

                        (equal (type-fix (rp-evlt (ex-from-rp/type-fix x) a))
                               m))))
   :hints (("Goal"
            :do-not-induct t
            :induct (ex-from-rp/type-fix x)
            :in-theory (e/d (ex-from-rp/type-fix
                             rp-trans
                             eval-of-type-fix-when-pp-sum-meta-formal-checks)
                            ())))))

(local
 (defthm resolve-pp-sum-order-rec-correct-dummy-lemma3
   (implies (and (equal (type-fix a)
                        (pp-sum y caddr-x)))
            (equal (equal (pp-sum cadr-x a)
                          (pp-sum y cadr-x caddr-x))
                   t))))

(local
 (defthm resolve-pp-sum-order-rec-correct-dummy-lemma4
   (implies (and (EQUAL 0
                        (PP-SUM y
                                caddr-x)))
            (equal (EQUAL (TYPE-FIX cadr-x)
                          (PP-SUM y
                                  cadr-x
                                  caddr-x))
                   t))))

(local
 (defthm resolve-pp-sum-order-rec-correct
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-termp x)
                 (rp-termp y)
                 (rp-evl-meta-extract-global-facts))
            (equal (type-fix (rp-evlt (resolve-pp-sum-order-rec y x) a))
                   (p+ (rp-evlt y a) (rp-evlt x a))))
   :hints (("Goal"
            :induct (resolve-pp-sum-order-rec y x)
            :do-not-induct t
            :in-theory (e/d (pp-sum-comm-1-any
;rp-evl-of-pp+
                             pp-sum-o-is-type-fix
                             resolve-pp-sum-order-rec
                             pp-sum-comm-2-any
                             ;;rp-evl-of-ex-from-rp-reverse
                             pp-sum-of-eval-to-to-ex-from-type-fix-rp
                             type-fix-of-eval-to-to-ex-from-type-fix-rp
                             pp-sum-reorder)
                            (pp-order p+ type-fix
                                      rp-termp
                                      RP-EVL-OF-VARIABLE
                                      should-sum-terms-cancel
                                      SHOULD-B+-CANCEL-aux-redef
                                      (:REWRITE NOT-INCLUDE-RP)
                                      ex-from-rp
                                      (:DEFINITION INCLUDE-FNC)
                                      (:REWRITE DEFAULT-CDR)
                                      (:REWRITE EX-FROM-SYNP-LEMMA1)
                                      IS-SYNP
                                      (:REWRITE ACL2::SIMPLIFY-SUMS-EQUAL)
                                      (:REWRITE
                                       ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                                      (:REWRITE
                                       ACL2::ACL2-NUMBERP-X)
                                      (:REWRITE PP-SUM-WHEN-SHOULD-B+-CANCEL-LEMMA)
                                      EVL-OF-EXTRACT-FROM-RP))))))

(local
 (defthm lemma100
   (IMPLIES
    (and (consp x)
         (consp (cdr x))
         (not (cddr x))
         (equal (car x) 'type-fix)
         (rp-evl-meta-extract-global-facts)
         (pp-sum-meta-formal-checks state))
    (EQUAL (pp-sum 0 (rp-evlt (cadr x) a))
           (rp-evlt x a)))
   :hints (("Goal"
            :in-theory (e/d (eval-of-type-fix-when-pp-sum-meta-formal-checks) ())))))

(local
 (defthm eval-of-sort-pp-flatten-main-is-correct-2
   (implies (and (force (pp-sum-meta-formal-checks state))
                 (force (valid-sc term a))
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (flatten-pp-main term) a)
                   (rp-evlt term a)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance eval-of-sort-pp-flatten-main-is-correct))
            :in-theory (e/d ()
                            (eval-of-sort-pp-flatten-main-is-correct))))))

(local
 (defthm pp-sum-of-0
   (equal (pp-sum 0 x)
          (type-fix x))))

(local
 (defthm type-fix-of-type-fix
   (equal (type-fix (type-fix x))
          (type-fix x))))

(defthmd when-flattened-is-all-zero
  (implies (and (CONSP (FLATTEN-PP-MAIN x))
                (EQUAL (CAR (FLATTEN-PP-MAIN x))
                       'P+)
                (CONSP (CDR (FLATTEN-PP-MAIN x)))
                (EQUAL (CADR (FLATTEN-PP-MAIN x))
                       ''0)
                (CONSP (CDDR (FLATTEN-PP-MAIN x)))
                (EQUAL (CADDR (FLATTEN-PP-MAIN x))
                       ''0)
                (NOT (CDDDR (FLATTEN-PP-MAIN x)))
                (rp-termp x)
                (valid-sc x a)
                (pp-sum-meta-formal-checks state)
                (rp-evl-meta-extract-global-facts))
           (equal (rp-evlt x a)
                  0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-of-sort-pp-flatten-main-is-correct
                            (term x)))
           :in-theory (e/d () (eval-of-sort-pp-flatten-main-is-correct
                               EVAL-OF-SORT-PP-FLATTEN-MAIN-IS-CORRECT-2)))))

(defthm eval-of-resolve-pp-sum-order-preprocess
  (implies (and (pp-sum-meta-formal-checks state)
                (rp-termp x)
                (valid-sc x a)
                (rp-evl-meta-extract-global-facts))
           (equal (type-fix (rp-evlt (resolve-pp-sum-order-preprocess x)
                                    a))
                  (type-fix (rp-evlt x a))))
  :hints (("goal"
           :in-theory (e/d (resolve-pp-sum-order-preprocess) ()))))

(defthm eval-of-resolve-pp-sum-order-preprocess-2
  (implies (and (pp-sum-meta-formal-checks state)
                (rp-termp x)
                (valid-sc x a)
                (rp-evl-meta-extract-global-facts))
           (and (equal (pp-sum (rp-evlt (resolve-pp-sum-order-preprocess x) a)
                               other)
                       (pp-sum (rp-evlt x a)
                               other))
                (equal (pp-sum other
                               (rp-evlt (resolve-pp-sum-order-preprocess x) a))
                       (pp-sum other
                               (rp-evlt x a)))))
  :hints (("goal"
           :use ((:instance eval-of-resolve-pp-sum-order-preprocess))
           :in-theory (e/d ()
                           (eval-of-resolve-pp-sum-order-preprocess)))))

(defthm rp-termp-of-resolve-pp-sum-order-preprocess
  (implies (and (rp-termp x))
           (rp-termp (resolve-pp-sum-order-preprocess x)))
  :hints (("goal"
           :in-theory (e/d (resolve-pp-sum-order-preprocess) ()))))

(defthmd resolve-pp-sum-order-preprocess-implies-1
  (implies (and (pp-sum-meta-formal-checks state)
                (valid-sc x a)
                (rp-termp x)
                (rp-evl-meta-extract-global-facts)
                (EQUAL (resolve-pp-sum-order-preprocess x) ''0))
           (equal (rp-evlt x a)
                  0))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance eval-of-sort-pp-flatten-main-is-correct
                            (term x))
                 (:instance eval-of-sort-pp-flatten-main-is-correct
                            (term (caddr x))))
           :in-theory (e/d (resolve-pp-sum-order-preprocess)
                           (eval-of-sort-pp-flatten-main-is-correct
                            EVAL-OF-SORT-PP-FLATTEN-MAIN-IS-CORRECT-2
                            type-fix
                            rp-termp
                            valid-sc
                            RP-EVL-OF-VARIABLE)))))

(local
 (encapsulate
   nil

   (local
    (in-theory (e/d (pp-sum-comm-1-any
                     EVAL-OF-TYPE-FIX-WHEN-PP-SUM-META-FORMAL-CHECKS
                     pp-sum-comm-2-any
                     when-flattened-is-all-zero
                     pp-sum-reorder)
                    (p+
                     (:REWRITE EX-FROM-SYNP-LEMMA1)
                     (:REWRITE ACL2::O-P-O-INFP-CAR)
                     (:REWRITE DEFAULT-CDR)
                     (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                     (:DEFINITION EX-FROM-RP)
                     (:DEFINITION RP-TERMP)
                     (:DEFINITION SHOULD-B+-CANCEL-AUX)
                     (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
                     (:REWRITE RP-EQUAL-IS-SYMMETRIC)
                     (:REWRITE
                      ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                     (:DEFINITION RP-EQUAL)
;(:DEFINITION QUOTEP)
                     (:REWRITE ACL2::ACL2-NUMBERP-X)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:DEFINITION RP-TERMP)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:REWRITE PP-SUM-WHEN-SHOULD-B+-CANCEL)
                     (:REWRITE SHOULD-B+-CANCEL-AUX-REDEF)
                     (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
; (:DEFINITION EX-FROM-RP)
                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                     (:DEFINITION INCLUDE-FNC)
                     (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                     (:DEFINITION SUBSETP-EQUAL)
                     (:DEFINITION MEMBER-EQUAL)
                     (:REWRITE
                      ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                     (:REWRITE ACL2::ACL2-NUMBERP-X)
                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:REWRITE ACL2::RATIONALP-X)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                     (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:REWRITE IS-IF-RP-TERMP)
                     (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                     (:REWRITE NOT-INCLUDE-RP)
                     pp-sum-meta-formal-checks
                     rp-termp
                     valid-sc
                     RP-EVL-OF-VARIABLE
                     resolve-pp-sum-order-rec-correct
                     type-fix
                     eval-of-resolve-pp-sum-order-preprocess
                     resolve-pp-sum-order-rec))))

   (defthm resolve-pp-sum-order-correct
     (implies (and (rp-termp x)
                   (valid-sc x a)
                   (pp-sum-meta-formal-checks state)
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt (resolve-pp-sum-order x) a)
                     (rp-evlt x a)))
     :rule-classes :rewrite
     :hints (("Goal"
              :expand ((:free (x) (hide x))
;(:free (x) (pp-sum 0 x))
                       )
              :do-not-induct t
;:in-theory (e/d (resolve-pp-sum-order-rec-correct) ())
              :use ((:instance resolve-pp-sum-order-rec-correct
                               (y (resolve-pp-sum-order-preprocess (CADR X)))
                               (x (resolve-pp-sum-order-preprocess (CADDR X))))
                    (:instance resolve-pp-sum-order-preprocess-implies-1
                               (x (caddr x)))
                    (:instance resolve-pp-sum-order-preprocess-implies-1
                               (x (cadr x)))
                    (:instance eval-of-resolve-pp-sum-order-preprocess
                               (x (cadr x)))
                    (:instance eval-of-resolve-pp-sum-order-preprocess
                               (x (caddr x)))
                    #|(:instance resolve-pp-sum-order-rec-correct
                    (y (cadr x))
                    (x (CADDR X)))||#
                    #|(:instance resolve-pp-sum-order-rec-correct
                    (y (FLATTEN-PP-MAIN (CADR X)))
                    (x (CADDR X)))||#
                    #|(:instance resolve-pp-sum-order-rec-correct
                    (y (CADR X))
                    (x (FLATTEN-PP-MAIN (CADDR X))))||#))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm pp-sum-and-type-fix
   (and (equal (type-fix (pp-sum a b))
               (pp-sum a b))
        (equal  (pp-sum a 0)
                (type-fix a))
        (equal  (pp-sum 0 a)
                (type-fix a))
        (equal (pp-sum (type-fix a) b)
               (pp-sum a b))
        (equal (pp-sum b (type-fix a))
               (pp-sum b a)))))

(local
 (defthmd
   evl-of-extract-from-rp-clear-ex-from-rp
   (implies (syntaxp (include-fnc term 'ex-from-rp))
            (equal (rp-evlt (ex-from-rp term) a)
                   (rp-evlt term a)))
   :hints (("goal"  ))))

(local
 (defthm sum-is-pp-sum
   (equal (sum a b)
          (pp-sum a b))))

(local
 (defthmd times2-is-pp-sum
   (equal (times2 x)
          (pp-sum x x))
   :hints (("Goal"
            :in-theory (e/d (times2) ())))))

(local
 (DEFTHM
   RP-EVL-OF-RP-EQUAL-test
   (IMPLIES (AND (RP-EQUAL TERM1 TERM2)
                 (force (RP-TERMP TERM1))
                 (force (RP-TERMP TERM2)))
            (EQUAL (RP-EVLT TERM1 A)
                   (RP-EVLT TERM2 A)))
   :rule-classes :rewrite))

(local
 (defthm rp-evl-of-resolve-pp-sum-cough-out-terms-lemma1
   (implies (EQUAL (PP-SUm a b) c)
            (equal (pp-sum a b x)
                   (pp-sum c x)))))

(local
 (defthm pp-sum-and-minus
   (and (equal (pp-sum a (- a) b)
               (type-fix b))
        (equal (pp-sum (- a) a b)
               (type-fix b))
        (equal (pp-sum (- a) a)
               0)
        (equal (pp-sum a (- a))
               0))))

(local
 (defthm acl2-numberp-type-fix
   (acl2-numberp (type-fix x))))

#|(defthm rp-evl-of-resolve-pp-sum-cough-out-terms
  (implies (and (pp-sum-meta-formal-checks state)
                (rp-termp term)
                (rp-evl-meta-extract-global-facts))
           (equal (pp-sum (rp-evl (mv-nth 0 (resolve-pp-sum-cough-out-terms term)) a)
                          (rp-evl (mv-nth 1 (resolve-pp-sum-cough-out-terms term)) a))
                  (type-fix (rp-evl term a))))
  :hints (("Subgoal *1/2"
           :use ((:instance RP-EVL-OF-RP-EQUAL
                            (term1 (CADR (EX-FROM-RP TERM)))
                            (term2 (CADR (CADDR (EX-FROM-RP TERM)))))))
          ("Goal"
           :use ((:instance RP-EVL-OF-RP-EQUAL
                            (term2 (CADR (EX-FROM-RP TERM)))
                            (term1 (CADR (CADDR (EX-FROM-RP TERM))))))
           :in-theory (e/d (pp-sum-comm-1-any
                            pp-sum-comm-2-any
                            pp-sum-reorder
                            minus
                            rp-evl-of-ex-from-rp-reverse
                            times2-is-pp-sum
                            evl-of-extract-from-rp-clear-ex-from-rp)
                           (type-fix
                            p+
                            EVL-OF-EXTRACT-FROM-RP
                            type-p
                            RP-EVL-OF-VARIABLE
                            (:REWRITE SHOULD-B+-CANCEL-AUX-REDEF)
                            (:REWRITE PP-SUM-WHEN-SHOULD-B+-CANCEL)
                            (:DEFINITION SHOULD-B+-CANCEL-AUX)
                            (:REWRITE
                             ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                            b+
                            rp-termp
                            rp-equal-cnt
                            rp-equal
                            ex-from-rp
                            include-fnc)))))||#

(local
 (defthm integerp-pp-sum-and-type-fix
   (and (integerp (pp-sum a b))
        (integerp (type-fix a)))))

#|(local
 (defthm RESOLVE-PP-SUM-COUGH-OUT-TERMS-returns-integerp-term-when-coughs
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-termp term)
                 (NOT (EQUAL (MV-NTH 1 (RESOLVE-PP-SUM-COUGH-OUT-TERMS TERM))
                             ''0))
                 (rp-evl-meta-extract-global-facts))
            (INTEGERP (RP-EVL TERM A)))
   :hints (("Goal"
            :in-theory (e/d (pp-sum-comm-1-any
                             pp-sum-comm-2-any
                             pp-sum-reorder
                             minus
                             rp-evl-of-ex-from-rp-reverse
                             times2-is-pp-sum
                             evl-of-extract-from-rp-clear-ex-from-rp)
                            (type-fix
                             p+
                             EVL-OF-EXTRACT-FROM-RP
                             type-p
                             RP-EVL-OF-VARIABLE
                             (:REWRITE SHOULD-B+-CANCEL-AUX-REDEF)
                             (:REWRITE PP-SUM-WHEN-SHOULD-B+-CANCEL)
                             (:DEFINITION SHOULD-B+-CANCEL-AUX)
                             (:REWRITE
                              ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                             b+
                             rp-termp
                             rp-equal-cnt
                             rp-equal
                             ex-from-rp
                             include-fnc))))))||#

#|(local
 (defthm rp-evl-of-resolve-pp-sum-cough-out-terms-main
   (implies (and (pp-sum-meta-formal-checks state)
                 (rp-termp term)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evl (mv-nth 0 (resolve-pp-sum-cough-out-terms-main term)) a)
                   (rp-evl term a)))
   :hints (("Goal"
            :in-theory (e/d ()
                            (p+
                             resolve-pp-sum-cough-out-terms
                             rp-equal-cnt
                             rp-equal
                             ex-from-rp
                             include-fnc))))))||#

;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (encapsulate
   nil

   (local
    (defthm rp-termp-implies-rp-termp-ex-from-rp
      (implies (rp-termp term)
               (rp-termp (ex-from-rp term)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm rp-termp-implies-1
      (implies (and (rp-termp term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term))
               (rp-termp (cadr term)))))

   (local
    (defthm rp-termp-implies-2
      (implies (and (rp-termp term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    (consp term))
               (rp-termp (caddr term)))))

   #|(local
   (defthm rp-termp-EX-FROM-TYPE-FIX-IN-PP+
   (implies (rp-termp term)
   (rp-termp (EX-FROM-TYPE-FIX-IN-PP+ term)))
   :hints (("Goal"
   :in-theory (e/d (EX-FROM-TYPE-FIX-IN-PP+) ())))))||#

   #|(local
   (defthm rp-termp-EX-FROM-TYPE-FIX
   (implies (rp-termp term)
   (rp-termp (ex-from-type-fix term)))
   :hints (("Goal"
   :in-theory (e/d (ex-from-type-fix) ())))))||#

   #|(local
   (defthm rp-termp-CLEAR-PP+-FROM-ZEROS-aux
   (implies (and (rp-termp term1))
   (rp-termp
   (mv-nth 0 (clear-pp+-from-zeros-aux term1 dont-rw))))
   :hints (("Goal"
   :in-theory (e/d () (PP-ORDER
   ex-from-rp))))))||#

   (defthm rp-termp-RESOLVE-PP-SUM-ORDER
     (implies (rp-termp term)
              (rp-termp
               (resolve-pp-sum-order term)))
     :hints (("Goal"
              :in-theory (e/d ()
                              (
                               resolve-pp-sum-order-rec)))))

   #|(local
   (defthm rp-termp-resolve-pp-sum-cough-out-terms
   (implies (rp-termp term)
   (and (rp-termp  (mv-nth 0 (resolve-pp-sum-cough-out-terms
   term)))
   (rp-termp  (mv-nth 1 (resolve-pp-sum-cough-out-terms
   term)))))
   :hints (("Goal"
   :in-theory (e/d () (EX-FROM-RP
   (:DEFINITION RP-EQUAL)
   (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
   (:REWRITE NOT-INCLUDE-RP)
   (:DEFINITION INCLUDE-FNC)
   (:REWRITE
   ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
   (:REWRITE ACL2::ACL2-NUMBERP-X)
   (:REWRITE ACL2::RATIONALP-X)
   (:DEFINITION RP-EQUAL-CNT)))))))||#

   #|(local
   (defthm rp-termp-resolve-pp-sum-cough-out-terms-main
   (implies (rp-termp term)
   (rp-termp  (mv-nth 0 (resolve-pp-sum-cough-out-terms-main
   term))))))||#

   (defthm rp-termp-resolve-pp-sum-order-main
     (implies (rp-termp term)
              (rp-termp (mv-nth 0 (resolve-pp-sum-order-main term))))
     :hints (("Goal"
              :in-theory (e/d () (RESOLVE-PP-SUM-ORDER
                                  )))))))

(defthm rp-evl-of-resolve-pp-sum-order-main
  (implies (and (pp-sum-meta-formal-checks state)
                (rp-termp term)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (equal (rp-evlt (mv-nth 0 (resolve-pp-sum-order-main term)) a)
                  (rp-evlt term a)))
  :hints (("Goal"
           :in-theory (e/d () (resolve-pp-sum-order
                               )))))

#|(local
 (encapsulate
   nil

   (local
    (defthm all-falist-consistent-implies-all-falist-consistent-ex-from-rp
      (implies (all-falist-consistent term)
               (all-falist-consistent (ex-from-rp term)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm all-falist-consistent-implies-1
      (implies (and (all-falist-consistent term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term))
               (all-falist-consistent (cadr term)))))

   (local
    (defthm all-falist-consistent-implies-2
      (implies (and (all-falist-consistent term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    (consp term))
               (all-falist-consistent (caddr term)))))

   (local
    (defthm all-falist-consistent-ex-from-rp/type-fix
      (implies (all-falist-consistent x)
               (all-falist-consistent (ex-from-rp/type-fix x)))
      :hints (("Goal"
               :induct (ex-from-rp/type-fix x)
               :in-theory (e/d (ex-from-rp/type-fix) ())))))

   (local
    (defthm all-falist-consistent-ex-from-type-fix
      (implies (all-falist-consistent x)
               (all-falist-consistent (ex-from-type-fix x)))
      :hints (("Goal"
; :induct (ex-from-type-fix x)
               :in-theory (e/d (ex-from-type-fix) ())))))

   (local
    (defthm all-falist-consistent-RESOLVE-PP-SUM-ORDER-rec
      (implies (and (all-falist-consistent term1)
                    (all-falist-consistent term2))
               (all-falist-consistent
                (resolve-pp-sum-order-rec term1 term2)))
      :hints (("Goal"
               :in-theory (e/d (resolve-pp-sum-order-rec)
                               (PP-ORDER
                                ex-from-rp
                                SHOULD-B+-CANCEL-AUX-REDEF
                                (:DEFINITION INCLUDE-FNC)
                                (:REWRITE ACL2::ACL2-NUMBERP-X)
                                (:REWRITE
                                 ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                                (:REWRITE
                                 NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)))))))

   #|(local
   (defthm all-falist-consistent-EX-FROM-TYPE-FIX-IN-PP+
   (implies (all-falist-consistent term)
   (all-falist-consistent (EX-FROM-TYPE-FIX-IN-PP+ term)))
   :hints (("Goal"
   :in-theory (e/d (EX-FROM-TYPE-FIX-IN-PP+) ())))))||#

   #|(local
   (defthm all-falist-consistent-EX-FROM-TYPE-FIX
   (implies (all-falist-consistent term)
   (all-falist-consistent (ex-from-type-fix term)))
   :hints (("Goal"
   :in-theory (e/d (ex-from-type-fix) ())))))||#

   #|(local
   (defthm all-falist-consistent-CLEAR-PP+-FROM-ZEROS-aux
   (implies (and (all-falist-consistent term1))
   (all-falist-consistent
   (mv-nth 0 (clear-pp+-from-zeros-aux term1 dont-rw))))
   :hints (("Goal"
   :in-theory (e/d () (PP-ORDER
   ex-from-rp))))))||#

   (local
    (defthm all-falist-consistent-RESOLVE-PP-SUM-ORDER-PREPROCESS
      (implies (all-falist-consistent term)
               (all-falist-consistent
                (RESOLVE-PP-SUM-ORDER-PREPROCESS term)))
      :hints (("Goal"
               :in-theory (e/d (RESOLVE-PP-SUM-ORDER-PREPROCESS)
                               (#|CLEAR-PP+-FROM-ZEROS-aux||#
                                resolve-pp-sum-order-rec))))))

   (local
    (defthm all-falist-consistent-RESOLVE-PP-SUM-ORDER
      (implies (all-falist-consistent term)
               (all-falist-consistent
                (resolve-pp-sum-order term)))
      :hints (("Goal"
               :in-theory (e/d ()
                               (#|CLEAR-PP+-FROM-ZEROS-aux||#
                                resolve-pp-sum-order-rec))))))

   #|(local
   (defthm all-falist-consistent-resolve-pp-sum-cough-out-terms
   (implies (all-falist-consistent term)
   (and (all-falist-consistent  (mv-nth 0 (resolve-pp-sum-cough-out-terms
   term)))
   (all-falist-consistent  (mv-nth 1 (resolve-pp-sum-cough-out-terms
   term)))))
   :hints (("Goal"
   :in-theory (e/d () (EX-FROM-RP
   (:DEFINITION RP-EQUAL)
   (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
   (:REWRITE DEFAULT-CAR)
   (:REWRITE DEFAULT-CDR)
   (:REWRITE
   ACL2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
   (:REWRITE ACL2::SIMPLIFY-SUMS-EQUAL)
   (:REWRITE NOT-INCLUDE-RP)
   (:DEFINITION INCLUDE-FNC)
   (:REWRITE
   ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
   (:REWRITE ACL2::ACL2-NUMBERP-X)
   (:REWRITE ACL2::RATIONALP-X)
   (:DEFINITION RP-EQUAL-CNT)))))))||#

   #|(local
   (defthm all-falist-consistent-resolve-pp-sum-cough-out-terms-main
   (implies (all-falist-consistent term)
   (and (all-falist-consistent (mv-nth 0 (resolve-pp-sum-cough-out-terms-main
   term)))))
   :hints (("goal"
   :in-theory (e/d () (ex-from-rp
   (:definition rp-equal)
   resolve-pp-sum-cough-out-terms
   (:rewrite rp-equal-cnt-is-rp-equal)
   (:rewrite default-car)
   (:rewrite default-cdr)
   (:rewrite
   acl2::reduce-multiplicative-constant-equal)
   (:rewrite acl2::simplify-sums-equal)
   (:rewrite not-include-rp)
   (:definition include-fnc)
   (:rewrite
   acl2::simplify-products-gather-exponents-equal)
   (:rewrite acl2::acl2-numberp-x)
   (:rewrite acl2::rationalp-x)
   (:definition rp-equal-cnt)))))))||#

   (defthm all-falist-consistent-resolve-pp-sum-order-main
     (implies (all-falist-consistent term)
              (all-falist-consistent (mv-nth 0 (resolve-pp-sum-order-main term))))
     :hints (("goal"
              :in-theory (e/d () (resolve-pp-sum-order
                                  #|resolve-pp-sum-cough-out-terms-main||#)))))))||#

#|(local
 (encapsulate
   nil

   (local
    (defthm rp-syntaxp-implies-rp-syntaxp-ex-from-rp-term
      (implies (rp-syntaxp term)
               (rp-syntaxp (ex-from-rp term)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm rp-syntaxp-implies-1
      (implies (and (rp-syntaxp term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term)
                    (Not (is-rp term)))
               (rp-syntaxp (cadr term)))))

   (local
    (defthm rp-syntaxp-implies-2
      (implies (and (rp-syntaxp term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    (consp term))
               (rp-syntaxp (caddr term)))))

   #|(local
   (defthm rp-syntaxp-EX-FROM-TYPE-FIX-IN-PP+
   (implies (rp-syntaxp term)
   (rp-syntaxp (EX-FROM-TYPE-FIX-IN-PP+ term)))
   :hints (("Goal"
   :in-theory (e/d (EX-FROM-TYPE-FIX-IN-PP+) ())))))||#

   #|(local
   (defthm rp-syntaxp-EX-FROM-TYPE-FIX
   (implies (rp-syntaxp term)
   (rp-syntaxp (ex-from-type-fix term)))
   :hints (("Goal"
   :in-theory (e/d (ex-from-type-fix) ())))))||#

   #|(local
   (defthm rp-syntaxp-clear-pp+-from-zeros-aux
   (implies (and (rp-syntaxp term1))
   (rp-syntaxp (mv-nth 0
   (clear-pp+-from-zeros-aux term1 dont-rw))))
   :hints (("goal"
   :in-theory (e/d () (pp-order
   ex-from-rp))))))||#

   #|(local
   (defthm rp-syntaxp-CLEAR-PP+-FROM-ZEROS
   (implies (and (rp-syntaxp term1))
   (rp-syntaxp
   (mv-nth 0
   (clear-pp+-from-zeros term1 dont-rw))))
   :hints (("Goal"
   :in-theory (e/d () (PP-ORDER
   CLEAR-PP+-FROM-ZEROS-aux
   ex-from-rp))))))||#

   (local
    (defthm rp-syntaxp-lemma1
      (implies (and (RP-SYNTAXP TERM1)
                    (not (quotep (ex-from-rp/type-fix TERM1)))
                    (CONSP (CDR (ex-from-rp/type-fix TERM1))))
               (RP-SYNTAXP (CADR (ex-from-rp/type-fix TERM1))))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp/type-fix
                                is-rp) ())))))

   (local
    (defthm RP-SYNTAXP-ex-from-rp/type-fix
      (implies (RP-SYNTAXP x)
               (RP-SYNTAXP (ex-from-rp/type-fix x)))
      :hints (("Goal"
               :induct (ex-from-rp/type-fix x)
               :in-theory (e/d (ex-from-rp/type-fix) ())))))

   (local
    (defthm RP-SYNTAXP-ex-from-type-fix
      (implies (RP-SYNTAXP x)
               (RP-SYNTAXP (ex-from-type-fix x)))
      :hints (("Goal"
; :induct (ex-from-type-fix x)
               :in-theory (e/d (ex-from-type-fix) ())))))

   (local
    (defthm rp-syntaxp-RESOLVE-PP-SUM-ORDER-REC
      (implies (and (rp-syntaxp term1)
                    (rp-syntaxp term2))
               (rp-syntaxp
                (resolve-pp-sum-order-rec term1 term2)))
      :hints (("Goal"
               :in-theory (e/d (resolve-pp-sum-order-rec)
                               (PP-ORDER
                                #|CLEAR-PP+-FROM-ZEROS-aux||#
                                ex-from-rp

                                (:DEFINITION INCLUDE-FNC)
                                (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE
                                 ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                                (:REWRITE ACL2::ACL2-NUMBERP-X)
                                SHOULD-B+-CANCEL-AUX-REDEF))))))

   (local
    (defthm rp-syntaxp-RESOLVE-PP-SUM-ORDER-PREPROCESS
      (implies (rp-syntaxp term)
               (rp-syntaxp
                (RESOLVE-PP-SUM-ORDER-PREPROCESS term)))
      :hints (("Goal"
               :in-theory (e/d (RESOLVE-PP-SUM-ORDER-PREPROCESS)
                               (#|CLEAR-PP+-FROM-ZEROS-aux||#
                                resolve-pp-sum-order-rec))))))

   (local
    (defthm rp-syntaxp-RESOLVE-PP-SUM-ORDER
      (implies (rp-syntaxp term)
               (rp-syntaxp
                (resolve-pp-sum-order term)))
      :hints (("Goal"
               :in-theory (e/d ()
                               (#|CLEAR-PP+-FROM-ZEROS-aux||#
                                #|CLEAR-PP+-FROM-ZEROS||#
                                resolve-pp-sum-order-rec))))))

   (local
    (defthm rp-syntaxp-lemma2
      (implies (and (RP-SYNTAXP TERM)
                    (not (quotep term))
                    (consp term)
                    (consp (cdr term)))
               (rp-syntaxp (cadr term)))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp
                                is-rp) ())))))

   #|(local
   (defthm rp-syntaxp-resolve-pp-sum-cough-out-terms
   (implies (rp-syntaxp term)
   (and (rp-syntaxp  (mv-nth 0 (resolve-pp-sum-cough-out-terms
   term)))
   (rp-syntaxp  (mv-nth 1 (resolve-pp-sum-cough-out-terms
   term)))) )
   :hints (("goal"
   :in-theory (e/d () (ex-from-rp
   (:definition rp-equal)
   (:rewrite rp-equal-cnt-is-rp-equal)
   (:rewrite default-car)
   (:rewrite default-cdr)
   (:rewrite
   acl2::reduce-multiplicative-constant-equal)
   (:rewrite acl2::simplify-sums-equal)
   (:definition include-fnc)
   (:rewrite
   acl2::simplify-products-gather-exponents-equal)
   (:rewrite acl2::acl2-numberp-x)
   (:rewrite acl2::rationalp-x)
   (:definition rp-equal-cnt)))))))||#

   #|(local
   (defthm rp-syntaxp-resolve-pp-sum-cough-out-terms-main
   (implies (rp-syntaxp term)
   (and (rp-syntaxp  (mv-nth 0 (resolve-pp-sum-cough-out-terms-main
   term)))) )
   :hints (("Goal"
   :in-theory (e/d () (EX-FROM-RP
   (:DEFINITION RP-EQUAL)
   (:REWRITE RP-EQUAL-CNT-IS-RP-EQUAL)
   (:REWRITE DEFAULT-CAR)
   resolve-pp-sum-cough-out-terms
   (:REWRITE DEFAULT-CDR)
   (:REWRITE
   ACL2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
   (:REWRITE ACL2::SIMPLIFY-SUMS-EQUAL)
   (:DEFINITION INCLUDE-FNC)
   (:REWRITE
   ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
   (:REWRITE ACL2::ACL2-NUMBERP-X)
   (:REWRITE ACL2::RATIONALP-X)
   (:DEFINITION RP-EQUAL-CNT)))))))||#

   (defthm rp-syntaxp-RESOLVE-PP-SUM-ORDER-main
     (implies (rp-syntaxp term)
              (rp-syntaxp
               (mv-nth 0 (resolve-pp-sum-order-main term))))
     :hints (("Goal"
              :in-theory (e/d ()
                              (#|CLEAR-PP+-FROM-ZEROS-aux||#
                               resolve-pp-sum-order
                               #|resolve-pp-sum-cough-out-terms-main||#
                               #|CLEAR-PP+-FROM-ZEROS||#
                               resolve-pp-sum-order-rec)))))))||#

(local
 (encapsulate
   nil

   (local
    (defthm valid-sc-implies-valid-sc-ex-from-rp-term
      (implies (valid-sc term a)
               (valid-sc (ex-from-rp term) a))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm valid-sc-implies-1
      (implies (and (valid-sc term a)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term)
                    (Not (is-rp term)))
               (valid-sc (cadr term) a))))

   (local
    (defthm valid-sc-implies-2
      (implies (and (valid-sc term a)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    ;;(rp-syntaxp x)
                    (Not (is-rp term))
                    (Not (is-if term))
                    (consp term))
               (valid-sc (caddr term) a))
      :hints (("Goal"
               ;;:expand (VALID-SC TERM A)
               :in-theory (e/d (ex-from-rp) ())))))

   (local
    (defthm valid-sc-implies-3-lemma
      (implies (and (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                  A)
                    (is-rp term))
               (EVAL-AND-ALL (CONTEXT-FROM-RP (CADDR TERM) NIL)
                             A))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (eval-and-all
                                context-from-rp) ())))))

   (local
    (defthm valid-sc-implies-3
      (implies (and (valid-sc term a)
                    (consp (cdr term))
                    (consp (cddr term))
                    (is-rp-loose term)
                    (consp term))
               (valid-sc (caddr term) a))
      :hints (("Goal"
               :do-not-induct t
               :cases ((is-rp term)
                       (and (is-rp term)
                            (is-rp (caddr term))))
               :expand (valid-sc term a)
               :use ((:instance VALID-SC-EX-FROM-RP-2
                                (term (caddr term))))
               :in-theory (e/d (ex-from-rp is-rp is-rp-loose
                                           is-if)
                               (EX-FROM-RP-LEMMA1
                                VALID-SC-EX-FROM-RP-2
                                (:DEFINITION INCLUDE-FNC)
                                valid-sc))))))

   #|(in-theory (disable resolve-b+-order))||#

   (local
    (defthm valid-sc-ex-from-rp/type-fix
      (implies (and (valid-sc x a))
               (valid-sc (ex-from-rp/type-fix x) a))
      :hints (("Goal"
               :induct (ex-from-rp/type-fix x)
               :do-not-induct t
               :in-theory (e/d (ex-from-rp/type-fix
                                is-rp-loose
                                valid-sc
                                is-if
                                is-rp
                                )
                               (EX-FROM-RP-LEMMA1))))))

   (local
    (defthm valid-sc-ex-from-type-fix
      (implies (and (valid-sc x a))
               (valid-sc (ex-from-type-fix x) a))
      :hints (("Goal"
;:induct (ex-from-type-fix x)
               :do-not-induct t
               :in-theory (e/d (ex-from-type-fix
                                is-rp-loose
                                valid-sc
                                is-if
                                is-rp
                                )
                               (EX-FROM-RP-LEMMA1))))))

   (local
    (defthm valid-sc-RESOLVE-PP-SUM-ORDER-REC
      (implies (and (valid-sc x a)
                    (valid-sc y a))
               (valid-sc (resolve-pp-sum-order-rec x y) a))
      :hints (("Goal"
               :do-not-induct t
               :induct (resolve-pp-sum-order-rec x y)
               :in-theory (e/d (is-if
                                resolve-pp-sum-order-rec
                                is-rp)
                               (INCLUDE-FNC
                                SHOULD-B+-CANCEL-AUX-REDEF
                                (:DEFINITION EVAL-AND-ALL)
                                (:REWRITE
                                 ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                                (:REWRITE ACL2::ACL2-NUMBERP-X)
                                (:REWRITE LEMMA8)

                                (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE EX-FROM-SYNP-LEMMA1)
                                (:REWRITE DEFAULT-CDR)
                                (:REWRITE ACL2::O-P-O-INFP-CAR)
                                (:REWRITE VALID-SC-CADR)
                                (:REWRITE VALID-SC-IMPLIES-3)
                                (:REWRITE VALID-SC-CADDR)
                                (:REWRITE
                                 ACL2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                                pp-order))))))


   (local
    (defthm valid-sc-RESOLVE-PP-SUM-ORDER-PREPROCESS
      (implies (valid-sc term a)
               (valid-sc (RESOLVE-PP-SUM-ORDER-PREPROCESS term) a))
      :hints (("goal"
               :expand ((:free (x rest)
                               (valid-sc (cons x rest) a)))
               :in-theory (e/d (is-if is-rp RESOLVE-PP-SUM-ORDER-PREPROCESS)
                               (#|clear-pp+-from-zeros-aux||#
                                valid-sc))))))

   (local
    (defthm valid-sc-resolve-pp-sum-order
      (implies (valid-sc term a)
               (valid-sc (resolve-pp-sum-order term) a))
      :hints (("goal"
               :expand ((:free (x rest)
                               (valid-sc (cons x rest) a)))
               :in-theory (e/d (is-if is-rp)
                               (#|clear-pp+-from-zeros-aux||#
                                resolve-pp-sum-order-rec
                                valid-sc))))))

   (defthm valid-sc-resolve-pp-sum-order-main
     (implies (valid-sc term a)
              (valid-sc (mv-nth 0 (resolve-pp-sum-order-main term)) a))
     :hints (("goal"
              :in-theory (e/d (is-if is-rp)
                              (#|clear-pp+-from-zeros-aux||#
                               #|resolve-pp-sum-cough-out-terms-main||#
                               resolve-pp-sum-order
                               resolve-pp-sum-order-rec)))))))

(defthm resolve-pp-sum-order-valid-rp-meta-rulep
  (implies (and (pp-sum-meta-formal-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'resolve-pp-sum-order-main
                             :trig-fnc 'merge-pp+
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            RP-TERM-LISTP
                            
                            resolve-pp-sum-order-main
                            VALID-SC
                            resolve-assoc-eq-vals-rec
                            resolve-pp-sum-order)))))

(rp::add-meta-rules
 pp-sum-meta-formal-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'resolve-pp-sum-order-main
        :trig-fnc 'merge-pp+
        :dont-rw t
        :valid-syntax t)))

(in-theory (disable (:e rp::merge-pp+)
                    (:e rp::p+)))
