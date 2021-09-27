
; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "../bits-sbits")

(local
 (in-theory (enable bits-sbits-no-syntaxp)))

(local
 (in-theory (disable 4vec-zero-ext-is-bits)))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(define has-bitp-rp (term)
  :hints
  (("goal" :in-theory (e/d (rp::is-rp) nil)))
  :guard-hints
  (("goal" :in-theory (e/d (rp::is-rp) nil)))
  (if (rp::is-rp term)
      (or (equal (cadr term) ''bitp)
          (has-bitp-rp (caddr term)))
      nil))

(define 4vec-rsh-of-meta (term)
  (case-match term
    (('4vec-rsh ('quote s1) x)
     (b* ((?x-orig x)
          (x (rp::ex-from-rp x)))
       (case-match x
         (('4vec-concat$ ('quote s2) a b)
          (cond ((not (and (natp s1)
                           (natp s2)))
                 (progn$
                  (cw "unexpected instances of 4vec-rsh of 4vec-concat$ ~%")
                  (hard-error '4vec-rsh-of-meta "error" nil)
                  (mv term nil)))
                ((<= s2 s1)
                 (4vec-rsh-of-meta `(4vec-rsh ',(- s1 s2) ,b)))
                (t
                 (mv `(4vec-concat$ ',(- s2 s1)
                                    (bits ,a ',s1 ',(- s2 s1))
                                    ,b)
                     `(nil t (nil t t t) t)))))
         (('4vec-rsh ('quote s2) a)
          (cond ((not (and (natp s1)
                           (natp s2)))
                 (progn$
                  (cw "unexpected instances of 4vec-rsh of 4vec-rsh ~%")
                  (hard-error '4vec-rsh-of-meta "error" nil)
                  (mv term nil)))
                (t
                 (mv `(4vec-rsh ',(+ s2 s1) ,a)
                     `(nil t t)))))
         (&
          (cond ((and (has-bitp-rp x-orig)
                      (posp s1))
                 (mv ''0 ''t))
                (t 
                 (mv term `(nil t t))))))))
    (& (progn$
        (cw "Warning. Unexpected instances in 4vec-rsh-of-meta. Shift amount is not quoted.~%")
        (mv term nil)))))

(encapsulate
  nil

  (local
   (in-theory (e/d ()
                   (convert-4vec-concat-to-4vec-concat$
                    4vec-zero-ext-is-4vec-concat
                    4vec-part-select-is-bits))))

  (rp::def-formula-checks
   4vec-rsh-of-formula-checks
   (;4vec-rsh-of-meta
    bits
    bitp
    4vec-rsh
    4vec-concat$
    4vec-concat)))

(local
 (encapsulate
   nil

   (defthm rp-termp-of-4vec-rsh-of-meta
     (implies (rp::rp-termp term)
              (rp::rp-termp (mv-nth 0 (4vec-rsh-of-meta term))))
     :hints (("Goal"
              :in-theory (e/d (4vec-rsh-of-meta) ()))))

   (defthm dont-rw-syntaxp-of-4vec-rsh-of-meta
     (implies (rp::dont-rw-syntaxp term)
              (rp::dont-rw-syntaxp (mv-nth 1 (4vec-rsh-of-meta term))))
     :hints (("Goal"
              :in-theory (e/d (4vec-rsh-of-meta) ()))))))


(local
 (encapsulate
   nil

   (local
    (defthmd rp-evlt-of-ex-from-rp-reverse
      (implies (syntaxp (or (atom x)
                            (Not (equal (car x)
                                        'rp::ex-from-rp))))
               (equal (rp-evlt x a)
                      (rp-evlt (rp::ex-from-rp x) a)))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))
   (local
    (defthmd rp-evlt-of-ex-from-rp
      (implies t
               (equal (rp-evlt (rp::ex-from-rp x) a)
                      (rp-evlt x a)))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthmd rp-evlt-of-ex-from-rp-reverse-caddr
      (implies (syntaxp (equal term 'term))
               (equal (rp-evlt (caddr term) a)
                      (rp-evlt (rp::ex-from-rp (caddr term)) a)))
      :hints (("Goal"
               :in-theory (e/d (rp-evlt-of-ex-from-rp) ())))))


   (local
    (defthm rp-evl-of-ex-from-rp
      (EQUAL (RP-EVL (RP::EX-FROM-RP X) A)
             (RP-EVL X A))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp
                                rp::is-rp) ())))))
   
   (local
    (defthm eval-of-4vec-rsh-when-4vec-rsh-of-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '4vec-rsh)
                    (CONSP (CDR X))
                    (CONSP (CDdR X))
                    (not (CDddR X))
                    (and (rp-evl-meta-extract-global-facts)
                         (4vec-rsh-of-formula-checks state)))
               (and (equal (rp-evlt x a)
                           (4vec-rsh (rp-evlt (cadr x) a)
                                     (rp-evlt (caddr x) a)))
                    (equal (rp-evlt (rp::ex-from-rp x) a)
                           (4vec-rsh (rp-evlt (cadr x) a)
                                     (rp-evlt (caddr x) a)))
                    (equal (rp-evl x a)
                           (4vec-rsh (rp-evl (cadr x) a)
                                     (rp-evl (caddr x) a)))
                    (equal (rp-evl (rp::ex-from-rp x) a)
                           (4vec-rsh (rp-evl (cadr x) a)
                                     (rp-evl (caddr x) a)))))
      :hints (("Goal"
               :in-theory (e/d (rp-evlt-of-ex-from-rp) (rp::ex-from-rp))))))

   (local
    (defthm eval-of-4vec-concat$-when-4vec-rsh-of-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '4vec-concat$)
                    (CONSP (CDR X))
                    (CONSP (CDdR X))
                    (CONSP (CDddR X))
                    (not (CDdddR X))

                    (and (rp-evl-meta-extract-global-facts)
                         (4vec-rsh-of-formula-checks state)))
               (and (equal (rp-evlt x a)
                           (4vec-concat$ (rp-evlt (cadr x) a)
                                         (rp-evlt (caddr x) a)
                                         (rp-evlt (cadddr x) a)))
                    (equal (rp-evlt (rp::ex-from-rp x) a)
                           (4vec-concat$ (rp-evlt (cadr x) a)
                                         (rp-evlt (caddr x) a)
                                         (rp-evlt (cadddr x) a)))
                    (equal (rp-evl x a)
                           (4vec-concat$ (rp-evl (cadr x) a)
                                         (rp-evl (caddr x) a)
                                         (rp-evl (cadddr x) a)))
                    (equal (rp-evl (rp::ex-from-rp x) a)
                           (4vec-concat$ (rp-evl (cadr x) a)
                                         (rp-evl (caddr x) a)
                                         (rp-evl (cadddr x) a)))))
      :hints (("Goal"
               :in-theory (e/d (rp-evlt-of-ex-from-rp) (rp::ex-from-rp))))))

   (local
    (defthm eval-of-bits-when-4vec-rsh-of-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) 'bits)
                    (CONSP (CDR X))
                    (CONSP (CDdR X))
                    (CONSP (CDddR X))
                    (not (CDdddR X))

                    (and (rp-evl-meta-extract-global-facts)
                         (4vec-rsh-of-formula-checks state)))
               (and (equal (rp-evlt x a)
                           (bits (rp-evlt (cadr x) a)
                                         (rp-evlt (caddr x) a)
                                         (rp-evlt (cadddr x) a)))
                    (equal (rp-evlt (rp::ex-from-rp x) a)
                           (bits (rp-evlt (cadr x) a)
                                         (rp-evlt (caddr x) a)
                                         (rp-evlt (cadddr x) a)))
                    (equal (rp-evl x a)
                           (bits (rp-evl (cadr x) a)
                                         (rp-evl (caddr x) a)
                                         (rp-evl (cadddr x) a)))
                    (equal (rp-evl (rp::ex-from-rp x) a)
                           (bits (rp-evl (cadr x) a)
                                         (rp-evl (caddr x) a)
                                         (rp-evl (cadddr x) a)))))
      :hints (("Goal"
               :in-theory (e/d (rp-evlt-of-ex-from-rp) (rp::ex-from-rp))))))

   (local
    (defthm EX-FROM-RP-of-not-rp
      (implies (and (consp x)
                    (not (equal (car x) 'rp::rp)))
               (equal (rp::ex-from-rp x)
                      x))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp
                                rp::is-rp) ())))))



   (local
    (defthmd has-bitp-rp-implies-lemma
      (implies (and (has-bitp-rp term)
                    (4vec-rsh-of-formula-checks state)
                    (rp-evl-meta-extract-global-facts)
                    (rp::eval-and-all (rp::context-from-rp term nil) a))
               (bitp (rp-evlt term a)))
      :hints (("goal"
               :induct (has-bitp-rp term)
               :do-not-induct t
               :in-theory (e/d (has-bitp-rp
                                rp::is-rp
                                rp::is-if
                                rp::eval-and-all
                                rp::context-from-rp)
                               (bitp
                                ;;rp::ex-from-rp-lemma1
                                rp::valid-sc))))))
   
   (defthm HAS-BITP-RP-implies
     (implies (and (rp-evl-meta-extract-global-facts)
                   (4vec-rsh-of-formula-checks state)
                   (rp::valid-sc term a)
                   (HAS-BITP-RP term))
              (and (bitp (rp-evlt term a))
                   ;;(bitp (rp-evl term a))
                   (bitp (rp-evlt (rp::ex-from-rp term) a))))
     :hints (("Goal"
              :induct (HAS-BITP-RP term)
              :expand ((rp::valid-sc term a))
              :do-not-induct t
              :in-theory (e/d (has-bitp-rp
                               has-bitp-rp-implies-lemma
                               rp::is-rp
                               rp::is-if
                              )
                              (bitp
                               rp-trans
                               ;;rp::valid-sc
                               )))))

   

   (local
    (defthm rp-evlt-of-quoted
      (implies (quotep x)
               (equal (rp-evlt x a)
                      (cadr x)))))
   
   (defthm rp-evl-of-4vec-rsh-of-meta
     (implies (and (rp-evl-meta-extract-global-facts)
                   (4vec-rsh-of-formula-checks state)
                   (rp::valid-sc term a))
              (equal (rp-evlt (mv-nth 0 (4vec-rsh-of-meta term)) a)
                     (rp-evlt term a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (4vec-rsh-of-meta term)
              :in-theory (e/d (4vec-rsh-of-meta
                               rp::is-rp
                               rp::is-if
                               rp-evlt-of-ex-from-rp-reverse-caddr)
                              (natp
                               bitp
                               rp-trans
                               rp-trans-lst
                               RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               RP::RP-EVLT-OF-EX-FROM-RP
                               rp::ex-from-rp)))))))

(local
 (defthm valid-sc-4vec-rsh-of-meta
   (implies (rp::valid-sc term a)
            (rp::valid-sc (mv-nth 0 (4vec-rsh-of-meta term)) a))
   :hints (("Goal"
            :in-theory (e/d (4vec-rsh-of-meta
                             rp::is-if
                             rp::is-rp) ())))))

#|(defthm valid-rp-meta-rulep-4vec-rsh-of-formula-checks
  (implies (and (rp-evl-meta-extract-global-facts)
                (4vec-rsh-of-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc '4vec-rsh-of-meta
                             :trig-fnc '4vec-rsh
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                           (rp::RP-TERMP
                            rp::VALID-SC)))))||#

#|(rp::add-meta-rules 4vec-rsh-of-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc '4vec-rsh-of-meta
                                :trig-fnc '4vec-rsh
                                :dont-rw t
                                :valid-syntax t)))||#

(rp::add-meta-rule
 :meta-fnc 4vec-rsh-of-meta
 :trig-fnc 4vec-rsh
 :formula-checks 4vec-rsh-of-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))
