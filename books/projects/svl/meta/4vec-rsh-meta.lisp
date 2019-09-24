
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
          (mv term `(nil t t))))))
    (& (progn$
        (cw "unexpected instances in 4vec-rsh-of-meta ~%")
        (hard-error '4vec-rsh-of-meta "error" nil)
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
   (4vec-rsh-of-meta
    bits
    4vec-rsh
    4vec-concat$
    4vec-concat)))

(local
 (encapsulate
   nil

   (defthm pseudo-termp2-of-4vec-rsh-of-meta
     (implies (rp::pseudo-termp2 term)
              (rp::pseudo-termp2 (mv-nth 0 (4vec-rsh-of-meta term))))
     :hints (("Goal"
              :in-theory (e/d (4vec-rsh-of-meta) ()))))

   (defthm rp-syntaxp-of-4vec-rsh-of-meta
     (implies (rp::rp-syntaxp term)
              (rp::rp-syntaxp (mv-nth 0 (4vec-rsh-of-meta term))))
     :hints (("Goal"
              :in-theory (e/d (4vec-rsh-of-meta) ()))))

   (defthm all-falist-consistent-of-4vec-rsh-of-meta
     (implies (rp::all-falist-consistent term)
              (rp::all-falist-consistent (mv-nth 0 (4vec-rsh-of-meta term))))
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
    (defthmd rp-evl-of-ex-from-rp-reverse
      (implies (syntaxp (or (atom x)
                            (Not (equal (car x)
                                        'rp::ex-from-rp))))
               (equal (rp-evl x a)
                      (rp-evl (rp::ex-from-rp x) a)))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))
   (local
    (defthmd rp-evl-of-ex-from-rp
      (implies t
               (equal (rp-evl (rp::ex-from-rp x) a)
                      (rp-evl x a)))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthmd rp-evl-of-ex-from-rp-reverse-caddr
      (implies (syntaxp (equal term 'term))
               (equal (rp-evl (caddr term) a)
                      (rp-evl (rp::ex-from-rp (caddr term)) a)))
      :hints (("Goal"
               :in-theory (e/d (rp-evl-of-ex-from-rp) ())))))


   (local
    (defthm eval-of-4vec-rsh-when-4vec-rsh-of-formula-checks
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '4vec-rsh)
                    (CONSP (CDR X))
                    (CONSP (CDdR X))
                    (not (CDddR X))

                    (and (rp-evl-meta-extract-global-facts)
                         (4vec-rsh-of-formula-checks state)))
               (and (equal (rp-evl x a)
                           (4vec-rsh (rp-evl (cadr x) a)
                                     (rp-evl (caddr x) a)))
                    (equal (rp-evl (rp::ex-from-rp x) a)
                           (4vec-rsh (rp-evl (cadr x) a)
                                     (rp-evl (caddr x) a)))))
      :hints (("Goal"
               :in-theory (e/d (rp-evl-of-ex-from-rp) (rp::ex-from-rp))))))

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
               (and (equal (rp-evl x a)
                           (4vec-concat$ (rp-evl (cadr x) a)
                                         (rp-evl (caddr x) a)
                                         (rp-evl (cadddr x) a)))
                    (equal (rp-evl (rp::ex-from-rp x) a)
                           (4vec-concat$ (rp-evl (cadr x) a)
                                         (rp-evl (caddr x) a)
                                         (rp-evl (cadddr x) a)))))
      :hints (("Goal"
               :in-theory (e/d (rp-evl-of-ex-from-rp) (rp::ex-from-rp))))))

   (local
    (defthm EX-FROM-RP-of-not-rp
      (implies (and (consp x)
                    (not (equal (car x) 'rp::rp)))
               (equal (rp::ex-from-rp x)
                      x))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp
                                rp::is-rp) ())))))

   (defthm rp-evl-of-4vec-rsh-of-meta
     (implies (and (rp-evl-meta-extract-global-facts)
                   (4vec-rsh-of-formula-checks state))
              (equal (rp-evl (mv-nth 0 (4vec-rsh-of-meta term)) a)
                     (rp-evl term a)))
     :hints (("Goal"
              :in-theory (e/d (4vec-rsh-of-meta
                               rp-evl-of-ex-from-rp-reverse-caddr)
                              (natp
                               rp::ex-from-rp)))))))

(local
 (defthm valid-sc-4vec-rsh-of-meta
   (implies (rp::valid-sc term a)
            (rp::valid-sc (mv-nth 0 (4vec-rsh-of-meta term)) a))
   :hints (("Goal"
            :in-theory (e/d (4vec-rsh-of-meta
                             rp::is-if
                             rp::is-rp) ())))))



(defthm valid-rp-meta-rulep-4vec-rsh-of-formula-checks
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
                           (rp::PSEUDO-TERMP2
                            rp::PSEUDO-TERM-LISTP2
                            rp::RP-SYNTAXP
                            rp::VALID-SC)))))

(rp::add-meta-rules 4vec-rsh-of-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc '4vec-rsh-of-meta
                                :trig-fnc '4vec-rsh
                                :dont-rw t
                                :valid-syntax t)))
