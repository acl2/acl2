; RP-REWRITER

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
(include-book "../rp-rewriter")
(include-book "local-lemmas")
(include-book "proof-functions")
(include-book "aux-function-lemmas")

(include-book "proof-function-lemmas")

(encapsulate
  nil
  (local
   (defthm consp-extract-from-rp
     (implies (consp (ex-from-rp term))
              (consp term))))

  (local
   (defthm extract-from-rp-acl2-count
     (implies (consp term)
              (< (acl2-count (cdr (ex-from-rp term)))
                 (acl2-count term)))))

  (local
   (defthm consp-ex-from-rp-loose
     (implies (consp (ex-from-rp-loose term))
              (consp term))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp-loose
                               is-rp-loose) ())))))

  (local
   (defthm ex-from-rp-loose-acl2-count
     (implies (consp term)
              (< (acl2-count (cdr (ex-from-rp-loose term)))
                 (acl2-count term)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp-loose
                               is-rp-loose) ())))))

  (make-flag rp-equal-cnt :defthm-macro-name defthm-rp-equal-cnt)
  (make-flag rp-equal :defthm-macro-name defthm-rp-equal)
  (make-flag rp-equal-loose :defthm-macro-name defthm-rp-equal-loose))

(local (in-theory (disable rp-lhs rp-rhs rp-hyp)))

(local
 (in-theory (disable is-synp  extract-from-synp
                     should-term-be-in-cons put-term-in-cons)))

(local
 (defthm consp-extract-from-rp
   (implies (consp (ex-from-rp term))
            (consp term))
   :hints (("Goal" :in-theory (enable ex-from-rp)))))

(local
 (defthm consp-extract-from-synp
   (implies (consp (ex-from-synp term))
            (consp term))
   :hints (("Goal" :in-theory (enable is-synp extract-from-synp)))))

(defthm-rp-equal
  (defthm rp-equal-reflexive
    (implies (equal term1 term2)
             (rp-equal term1 term2))
    :flag rp-equal)

  (defthm rp-equal-subterms-reflexive
    (implies (equal subterm1 subterm2)
             (rp-equal-subterms subterm1 subterm2))
    :flag rp-equal-subterms))

(defthm evl-of-extract-from-rp
  (equal (rp-evl (ex-from-rp term) a)
         (rp-evl term a))
  :hints (("Goal"
           :in-theory (enable is-rp ex-from-rp))))

(defthm evl-of-extract-from-rp-loose
  (equal (rp-evl (ex-from-rp-loose term) a)
         (rp-evl term a))
  :hints (("Goal"
           :in-theory (enable is-rp-loose ex-from-rp-loose))))

(defthmd evl-of-extract-from-rp-loose-reverse
  (implies (syntaxp (atom term))
           (equal (rp-evl term a)
                  (rp-evl (ex-from-rp-loose term) a)))
  :hints (("Goal"
           :use ((:instance evl-of-extract-from-rp-loose))
           :in-theory (disable evl-of-extract-from-rp-loose ))))

(defthm evl-of-extract-from-synp
  (equal (rp-evl (ex-from-synp term) a)
         (rp-evl term a))
  :hints (("Goal"
           :in-theory (enable is-synp extract-from-synp))))

(local
 (defthm extract-from-rp-equal-to-evl
   (implies (equal (ex-from-rp term1)
                   (ex-from-rp term2))
            (equal (equal (rp-evl term1 a)
                          (rp-evl term2 a))
                   t))
   :hints (("goal"
            :induct (ex-from-rp term2)
            :in-theory (enable is-rp ex-from-rp)))))

(local
 (defthm extract-from-rp-equal-to-evl-loose
   (implies (equal (ex-from-rp-loose term1)
                   (ex-from-rp-loose term2))
            (equal (equal (rp-evl term1 a)
                          (rp-evl term2 a))
                   t))
   :hints (("goal"
            :induct (ex-from-rp-loose term2)
            :in-theory (enable is-rp-loose ex-from-rp-loose)))))

(local
 (defthm extract-from-rp-equal-to-evl-2
   (implies (EQUAL (rp-evl (EX-FROM-RP TERM1) a)
                   (rp-evl (EX-FROM-RP TERM2) a))
            (equal (EQUAL (RP-EVL TERM1 A)
                          (RP-EVL TERM2 A))
                   t))
   :hints (("Goal"
            :in-theory (e/d (is-rp ex-from-rp)
                            (NOT-INCLUDE-RP))))))

(local
 (defthm extract-from-rp-equal-to-evl-2-loose
   (implies (EQUAL (rp-evl (ex-from-rp-loose TERM1) a)
                   (rp-evl (ex-from-rp-loose TERM2) a))
            (equal (EQUAL (RP-EVL TERM1 A)
                          (RP-EVL TERM2 A))
                   t))
   :hints (("Goal"
            :in-theory (e/d (is-rp-loose ex-from-rp-loose)
                            (NOT-INCLUDE-RP))))))

(local
 (defthm extract-from-synp-equal-to-evl-1
   (implies (EQUAL (EXTRACT-FROM-SYNP TERM1)
                   (EXTRACT-FROM-SYNP TERM2))
            (equal (EQUAL (RP-EVL TERM1 A)
                          (RP-EVL TERM2 A))
                   t))
   :hints (("Goal"
            :in-theory (enable is-synp extract-from-synp)))))

(local
 (defthm evl-of-is-synp
   (IMPLIES  (IS-SYNP TERM1)
             (EQUAL (RP-EVL TERM1 A) T))
   :hints (("Goal" :in-theory (enable is-synp)))))

(local
 (defthm evl-of-is-synp-and-is-rp
   (IMPLIES  (and (or (is-rp term1)
                      (is-rp-loose term1))
                  (IS-SYNP (caddr term1)))
             (EQUAL (RP-EVL TERM1 A) T))
   :hints (("Goal" :in-theory (enable is-synp
                                      is-rp
                                      IS-RP-LOOSE)))))

(local
 (defthm extract-from-synp-and-rp-equal-to-evl-1-lemma1
   (IMPLIES (AND (or (IS-RP TERM1)
                     (is-rp-loose TERM1))
                 (IS-SYNP (CADDR TERM1))
                 (IS-RP TERM2)
                 (EQUAL ''T (CADDR TERM2)))
            (equal (EQUAL T (RP-EVL TERM2 A))
                   t))
   :hints (("Goal" :in-theory (enable is-rp
                                      is-rp-loose
                                      is-synp)))))

(local
 (defthm extract-from-synp-and-rp-equal-to-evl-1
   (implies (EQUAL (EX-FROM-SYNP (EX-FROM-RP TERM1))
                   (EX-FROM-SYNP (EX-FROM-RP TERM2)))
            (equal (EQUAL (RP-EVL TERM1 A)
                          (RP-EVL TERM2 A))
                   t))
   :hints (("Goal"
            :cases (;(is-synp (EX-FROM-RP TERM1))
;(is-synp (EX-FROM-RP TERM2))
                    (is-rp term1)
                    (is-rp term2)
                    )
            :in-theory (disable is-rp is-synp)))))

(local
 (defthm extract-from-synp-equal-to-evl-2
   (implies (EQUAL (rp-evl (ex-from-synp TERM1) a)
                   (rp-evl (ex-from-synp TERM2) a))
            (equal (EQUAL (RP-EVL TERM1 A)
                          (RP-EVL TERM2 A))
                   t))
   :hints (("Goal"
            :in-theory (enable extract-from-synp)))))

(defthm ex-from-rp-lemma1
  (implies (or (is-rp term)
               (is-rp-loose term))
           (equal (rp-evl (caddr term) a)
                  (rp-evl term a)))
  :hints (("Goal" :in-theory (enable is-rp
                                     is-rp-loose))))

(defthm evl-of-extract-from-rp-2
  (implies (and (or (is-rp term)
                    (is-rp-loose term))
                (rp-evl (caddr term) a))
           (rp-evl term a))
  :hints (("Goal"
           :use (ex-from-rp-lemma1)
           :in-theory '())))

(defthm ex-from-synp-lemma1
  (implies (is-synp term)
           (equal (rp-evl term a)
                  t))
  :hints (("Goal" :in-theory (enable is-synp))))

(defthm is-rp-pseudo-termp
  (implies (and (rp-termp term)
                (or (is-rp term)
                    (is-rp-loose term)))
           (rp-termp (caddr term)))
  :hints (("Goal" :in-theory (enable is-rp
                                     is-rp-loose))))

(defthm rp-termp-should-term-be-in-cons-lhs
  (implies (and (should-term-be-in-cons lhs term)
                (rp-termp lhs))
           (and (rp-termp (cadr lhs))
                (rp-termp (car lhs))
                (rp-termp (caddr lhs))))
  :hints (("Goal" :in-theory (enable should-term-be-in-cons))))

(defthm rp-termp-should-term-be-in-cons-term
  (implies (and (rp-termp term))
           (and (rp-termp (cadr (put-term-in-cons term)))
                (rp-termp (car (put-term-in-cons term)))
                (rp-termp (caddr (put-term-in-cons term)))))
  :hints (("Goal" :in-theory (enable put-term-in-cons))))

(defthm rp-termp-ex-from-rp
  (implies (rp-termp term)
           (and (rp-termp (ex-from-rp term))
                (rp-termp (ex-from-rp-loose term))))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp-loose
                            ex-from-rp
                            is-rp-loose
                            is-rp) ()))))


(encapsulate
  nil
  (local
   (defthm pseudo-termp-and-rp-evl-list
     (implies (and (rp-termp term1)
                   (rp-termp term2)
                   (consp term1)
                   (consp term2)
                   (not (quotep term1))
                   (equal (car term1) (car term2)) ;;same function symbols
                   (equal (rp-evl-lst (cdr term1) a) ;;params evaluate to the same
                          (rp-evl-lst (cdr term2) a)))
              (equal (equal (rp-evl term1 a)
                            (rp-evl term2 a))
                     t))
     :hints (("Goal" :in-theory (enable rp-evl-of-fncall-args)))))

  (local
   (defthm lemma1
     (implies (and (equal (rp-evl-lst (cdr term1) a)
                          (rp-evl-lst (cdr term2) a))
                   (equal (car term1) (car term2))
                   (consp term1)
                   (not (equal (car term1) 'quote))
                   (not (equal (car term2) 'quote))
                   (syntaxp (lexorder term1 term2))
                   (consp term2))
              (equal (rp-evl term1 a)
                     (rp-evl term2 a)))
     :hints (("goal" :in-theory (enable rp-evl-of-fncall-args)))))

  (local
   (defthmd lemma2
     (implies (quotep term)
              (equal (unquote term)
                     (rp-evl term a)))))
  #|(local
   (defthm lemma3
     (implies (and (not (equal (caddr term2) term2))
                   (not (is-rp-loose (caddr term2)))
                   (is-rp-loose term2)
                   (consp (caddr term2))
                   (equal (car (caddr term2)) 'quote)
                   (consp (cdr (caddr term2)))
                   (not (cddr (caddr term2)))
                   (rp-termp term2))
              (equal (cadr (caddr term2))
                     (rp-evl term2 a)))
     :instructions (:promote (:dive 1)
                             (:rewrite lemma2)
                             :top
                             :bash :s)))||#

  (local
   (in-theory (disable rp-evl-of-variable)))

  (defthm-rp-equal
    (defthm rp-evl-of-rp-equal
      (implies (and (rp-termp term1)
                    (rp-termp term2)
                    (rp-equal term1 term2))
               (equal (equal (rp-evl term1 a)
                             (rp-evl term2 a))
                      t))
      :flag rp-equal)

    (defthm rp-evl-of-rp-equal-subterms
      (implies (and (rp-equal-subterms subterm1 subterm2)
                    (rp-term-listp subterm1)
                    (rp-term-listp subterm2))
               (equal (equal (rp-evl-lst subterm1 a)
                             (rp-evl-lst subterm2 a))
                      t))
      :flag rp-equal-subterms))

  (defthm-rp-equal-loose
    (defthm rp-evl-of-rp-equal-loose
      (implies (and (rp-termp term1)
                    (rp-termp term2)
                    (rp-equal-loose term1 term2))
               (equal (equal (rp-evl term1 a)
                             (rp-evl term2 a))
                      t))
      :flag rp-equal-loose)

    (defthm rp-evl-of-rp-equal-loosesubterms
      (implies (and (rp-equal-loose-subterms subterm1 subterm2)
                    (rp-term-listp subterm1)
                    (rp-term-listp subterm2))
               (equal (equal (rp-evl-lst subterm1 a)
                             (rp-evl-lst subterm2 a))
                      t))
      :flag rp-equal-loose-subterms)))



(defthm-rp-equal
  (defthm rp-equal-is-symmetric
    (equal (rp-equal term2 term1)
           (rp-equal term1 term2))
    :flag rp-equal)
  (defthm rp-equal-subterms-is-symmetric
    (equal (rp-equal-subterms subterm2 subterm1)
           (rp-equal-subterms subterm1 subterm2))
    :flag rp-equal-subterms))

(encapsulate
  nil
  (local
   (in-theory (disable ex-from-rp ex-from-synp )))

  (local
   (defthm lemma1
     (implies (rp-equal2 term term2)
              (iff (consp (ex-from-synp (ex-from-rp term)))
                   (consp (ex-from-synp (ex-from-rp term2)))))
     :hints (("goal"
              :in-theory (enable ex-from-rp ex-from-synp)))))

  (local
   (defthm lemma1-2
     (implies (rp-equal term1 term2)
              (and #|(iff (consp (ex-from-rp-loose term1))
               (consp (ex-from-rp-loose term2)))||#
               (iff (consp (ex-from-rp term1))
                    (consp (ex-from-rp term2)))
               (iff (consp (ex-from-synp (ex-from-rp term1)))
                    (consp (ex-from-synp (ex-from-rp term2))))))
     :rule-classes :forward-chaining
     :hints (("goal" :in-theory (enable ex-from-rp
                                        ex-from-rp-loose
                                        is-rp
                                        is-rp-loose
                                        ex-from-synp)))))

  (local
   (defthm lemma3 (implies (and (acl2::flag-is 'rp-equal2)
                                (not (consp (ex-from-synp (ex-from-rp term2))))
                                (rp-equal term1 term2))
                           (equal (equal (ex-from-synp (ex-from-rp term1))
                                         (ex-from-synp (ex-from-rp term2)))
                                  t))
     :hints (("goal" :expand (rp-equal term1 term2)))))
  (local
   (defthm lemma4
     (implies (and (not (consp (ex-from-synp (ex-from-rp term1))))
                   (rp-equal term1 term2))
              (equal (ex-from-synp (ex-from-rp term1))
                     (ex-from-synp (ex-from-rp term2))))
     :hints (("goal"
              :use (:instance lemma1-2)
              :expand (rp-equal term1 term2)
              :in-theory (disable lemma1-2)))))
  (local
   (defthm lemma5
     (implies
      (and (consp (ex-from-synp (ex-from-rp term1)))
           (not (should-term-be-in-cons (ex-from-synp (ex-from-rp term2))
                                        (ex-from-synp (ex-from-rp term1))))
           (not (equal (car (ex-from-synp (ex-from-rp term1)))
                       'quote))
           (not (equal (car (ex-from-synp (ex-from-rp term2)))
                       'quote))
           (not (equal (car (ex-from-synp (ex-from-rp term1)))
                       (car (ex-from-synp (ex-from-rp term2))))))
      (not (rp-equal term1 term2)))
     :hints (("goal" :expand (rp-equal term1 term2)
              :in-theory (enable ex-from-synp)))))
  (local
   (defthm lemma6
     (implies (not (iff (is-synp (ex-from-rp term1))
                        (is-synp (ex-from-rp term2))))
              (not (rp-equal term1 term2)))
     :hints (("goal" :in-theory (enable is-synp)
              :expand ((rp-equal term1 term2)
                       (rp-equal-subterms (cdr (ex-from-rp term1))
                                          (cdr (ex-from-rp term2)))
                       (rp-equal-subterms (cddr (ex-from-rp term1))
                                          (cddr (ex-from-rp term2)))
                       (rp-equal-subterms (cdddr (ex-from-rp term1))
                                          (cdddr (ex-from-rp term2))))))))
  (local
   (defthm lemma7
     (implies (rp-equal term1 term2)
              (rp-equal-subterms (cdr (ex-from-synp (ex-from-rp term1)))
                                 (cdr (ex-from-synp (ex-from-rp term2)))))
     :hints (("goal" :in-theory (enable  ex-from-synp)))))

  (local
   (defthm lemma8
     (implies (not (equal (car (ex-from-synp (ex-from-rp term1)))
                          (car (ex-from-synp (ex-from-rp term2)))))
              (not (rp-equal term1 term2)))
     :hints (("goal" :in-theory (enable ex-from-synp)
              :expand ((rp-equal term1 term2)
                       (rp-equal-subterms (cdr (ex-from-rp term1))
                                          (cdr (ex-from-rp term2))))))))

  (local
   (defthm lemma9-lemma1
     (implies (and (equal (car a) (car b))
                   (consp b)
                   (equal (cdr a) (cdr b))
                   (consp a))
              (equal a b))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma9-lemma2
     (implies (and (equal a b)
                   (is-synp a))
              (is-synp b))))

  (local
   (defthm lemma9-lemma
     (implies (and (consp b)
                   (equal (car a) (car b))
                   (equal (cdr a) (cdr b))
                   (is-synp a))
              (is-synp b))
     :hints (("goal" :in-theory (disable is-synp-implies)
              :use ((:instance is-synp-implies (term a)))))))

  (local
   (defthm lemma9-lemma3
     (implies (and (consp (ex-from-rp term2))
                   (not (equal (car (ex-from-rp term1)) 'quote))
                   (equal (car (ex-from-rp term1))
                          (car (ex-from-rp term2)))
                   (consp (cdr (ex-from-rp term1)))
                   (consp (cdr (ex-from-rp term2)))
                   (rp-equal (cadr (ex-from-rp term1))
                             (cadr (ex-from-rp term2)))
                   (rp-equal-subterms (cddr (ex-from-rp term1))
                                      (cddr (ex-from-rp term2)))
                   (is-synp (ex-from-rp term1)))
              (is-synp (ex-from-rp term2)))
     :hints (("goal" :in-theory (enable is-synp)
              :expand
              ((rp-equal-subterms (cddr (ex-from-rp term1))
                                  (cddr (ex-from-rp term2)))
               (rp-equal-subterms (cdddr (ex-from-rp term1))
                                  (cdddr (ex-from-rp term2))))))))

  (local
   (defthm lemma9
     (implies (and (rp-equal term1 term2)
                   (consp (ex-from-synp (ex-from-rp term1)))
                   (equal (car (ex-from-synp (ex-from-rp term1)))
                          'quote))
              (equal (equal (ex-from-synp (ex-from-rp term1))
                            (ex-from-synp (ex-from-rp term2)))
                     t))
     :hints (("goal"
              :in-theory (enable ex-from-synp)
              :expand ((rp-equal term1 term2)
                       (rp-equal-subterms (cdr (ex-from-rp term1))
                                          (cdr (ex-from-rp term2))))))))

  (local
   (defthm lemma10
     (implies (should-term-be-in-cons (ex-from-synp (ex-from-rp term2))
                                      (ex-from-synp (ex-from-rp term1)))
              (not (rp-equal term1 term2)))
     :hints (("goal" :in-theory (enable should-term-be-in-cons
                                        ex-from-synp)))))

  (local
   (defthm lemma11
     (implies (should-term-be-in-cons (ex-from-synp (ex-from-rp term1))
                                      (ex-from-synp (ex-from-rp term2)))
              (not (rp-equal term1 term2)))
     :hints
     (("goal" :in-theory (enable is-synp should-term-be-in-cons)
       :expand (;(ex-from-synp (ex-from-rp term1))
                (rp-equal term1 term2))))))

  #|(defthm lemma4
  (implies (or (and (not (is-synp (ex-from-rp term1)))
  (is-synp (ex-from-rp term2)))
  (and  (is-synp (ex-from-rp term1))
  (not (is-synp (ex-from-rp term2)))))
  (not (rp-equal term1 term2)))
  :hints (("goal" :in-theory (enable )
  :expand (rp-equal term1 term2))))||#

  (defthm-rp-equal2
    (defthm rp-equal-implies-rp-equal2
      (implies (rp-equal term1 term2)
               (rp-equal2 term1 term2))
      :flag rp-equal2)
    (defthm rp-equal-subterms-implies-rp-equal2-subterms
      (implies (rp-equal-subterms subterm1 subterm2)
               (rp-equal2-subterms subterm1 subterm2))
      :flag rp-equal2-subterms)))

(encapsulate
  nil

  (local
   (in-theory (disable ex-from-synp ex-from-rp)))

  (local
   (in-theory (disable should-term-be-in-cons-lemma4
                       should-term-be-in-cons-lemma2)))

  (local
   (defthm lemma1
     (implies (rp-equal2 term1 term2)
              (iff (consp (ex-from-synp (ex-from-rp term1)))
                   (consp (ex-from-synp (ex-from-rp term2)))))
     :hints (("Goal" :in-theory (enable ex-from-rp ex-from-synp)))))

  (local
   (defthm lemma2
     (implies (and (EQUAL (RP-EVL-LST (CDR (EX-FROM-SYNP (EX-FROM-RP TERM1)))
                                      A)
                          (RP-EVL-LST (CDR (EX-FROM-SYNP (EX-FROM-RP TERM2)))
                                      A))
                   (CONSP (EX-FROM-SYNP (EX-FROM-RP TERM1)))
                   (CONSP (EX-FROM-SYNP (EX-FROM-RP TERM2)))
                   (NOT (EQUAL (CAR (EX-FROM-SYNP (EX-FROM-RP TERM2)))
                               'QUOTE))
                   (NOT (EQUAL (CAR (EX-FROM-SYNP (EX-FROM-RP TERM1)))
                               'QUOTE))
                   (syntaxp (and (equal term1 'term1)
                                 (equal term2 'term2)))
                   (EQUAL (CAR (EX-FROM-SYNP (EX-FROM-RP TERM1)))
                          (CAR (EX-FROM-SYNP (EX-FROM-RP TERM2)))))
              (equal (rp-evl (EX-FROM-SYNP (EX-FROM-RP TERM1)) a)
                     (rp-evl (EX-FROM-SYNP (EX-FROM-RP TERM2)) a)))
     :rule-classes :rewrite
     :hints (("Goal" :in-theory (e/d (rp-evl-of-fncall-args)
                                     (EVL-OF-EXTRACT-FROM-RP
                                      EVL-OF-EXTRACT-FROM-SYNP))))))

  (local
   (defthm lemma4
     (implies (SHOULD-TERM-BE-IN-CONS rule-lhs term)
              (AND (QUOTEP TERM)
                   (CONSP (UNQUOTE TERM))
                   (CASE-MATCH RULE-LHS (('CONS & &) T)
                     (& NIL))
                   (equal (car (put-term-in-cons term))
                          (car rule-lhs))))
     :hints (("Goal" :in-theory (enable put-term-in-cons should-term-be-in-cons)))))

  (local
   (defthm lemma5
     (implies (and (rp-termp term1)
                   (syntaxp (and (equal term1 'term1)
                                 (equal term2 'term2)))
                   (rp-termp term2))
              (equal (equal (rp-evl term1 a)
                            (rp-evl term2 a))
                     (equal (rp-evl (EX-FROM-SYNP (EX-FROM-RP TERM1)) a)
                            (rp-evl (EX-FROM-SYNP (EX-FROM-RP TERM2)) a))))))

  (local
   (defthm lemma6
     (implies (and (quotep term)
                   (consp (unquote term)))
              (and (equal (rp-evl (put-term-in-cons term) a)
                          (rp-evl term a))))
     :hints (("Goal" :in-theory (enable put-term-in-cons)))))

  (local
   (defthm lemma7
     (implies (and (rp-termp term)
                   (quotep term)
                   (consp (unquote term)))
              (rp-term-listp (cdr (put-term-in-cons term))))
     :hints (("Goal" :in-theory (enable put-term-in-cons)))))

  (local
   (in-theory (disable EVL-OF-EXTRACT-FROM-RP
                       EVL-OF-EXTRACT-FROM-SYNP)))

  (local
   (defthm lemma8-lemma0
     (equal (equal (list a b)
                   (list c d))
            (and (equal a c)
                 (equal b d)))))

  (local
   (defthm lemma8-lemma1
     (equal (equal (list a b)
                   (list c d))
            (equal (cons a b)
                   (cons c d)))))

  (local
   (defthm lemma8
     (implies (and (should-term-be-in-cons lhs term)
                   (equal (rp-evl-lst (cdr (put-term-in-cons term)) a)
                          (rp-evl-lst (cdr lhs) a))
                   (syntaxp (or
                             (and (equal term '(EX-FROM-SYNP (EX-FROM-RP TERM1)))
                                  (equal lhs '(EX-FROM-SYNP (EX-FROM-RP
                                                             TERM2))))
                             (and (equal term '(EX-FROM-SYNP (EX-FROM-RP TERM2)))
                                  (equal lhs '(EX-FROM-SYNP (EX-FROM-RP TERM1)))))))
              (and (equal (car (put-term-in-cons term))
                          (car lhs))
                   (equal (rp-evl term a)
                          (rp-evl lhs a))))
     :hints (("Goal" :in-theory (enable
                                 rp-evl-of-fncall-args
                                 should-term-be-in-cons
                                 put-term-in-cons)))))

  (local
   (defthm lemma9
     (implies (and (should-term-be-in-cons lhs term)
                   (rp-termp lhs))
              (rp-term-listp (cdr lhs)))
     :hints (("Goal" :in-theory (enable should-term-be-in-cons)))))

  (local
   (defthm lemma10
     (implies (and (consp term)
                   (not (EQUAL (CAR TERM) 'QUOTE))
                   (rp-termp term))
              (rp-term-listp (cdr term)))))

  (local
   (defthm lemma11
     (implies (and (should-term-be-in-cons term1 term2)
                   (equal  (rp-evl (cadr term1) a)
                           (rp-evl (cadr (put-term-in-cons term2)) a))
                   (equal  (rp-evl (caddr term1) a)
                           (rp-evl (caddr (put-term-in-cons term2)) a)))
              (equal (equal (rp-evl term1 a)
                            (rp-evl term2 a))
                     t))
     :hints (("Goal" :in-theory (enable put-term-in-cons
                                        should-term-be-in-cons)))))

  (local
   (defthm lemma11-2
     (implies (and (should-term-be-in-cons term1 term2)
                   (equal  (rp-evl (cadr term1) a)
                           (rp-evl (cadr (put-term-in-cons term2)) a))
                   (equal  (rp-evl (caddr term1) a)
                           (rp-evl (caddr (put-term-in-cons term2)) a)))
              (equal (equal (rp-evl term2 a)
                            (rp-evl term1 a))
                     t))
     :hints (("Goal" :in-theory (enable put-term-in-cons
                                        should-term-be-in-cons)))))

  (local
   (in-theory (disable is-cons)))

  (local
   (defthm lemma12-1
     (implies (and
               (RP-TERMP term1)
               (is-cons term1))
              (RP-TERMP (CADDR term1)))
     :hints (("Goal" :in-theory (enable is-cons  )))))

  (local
   (defthm lemma12-2
     (implies (and
               (RP-TERMP term)
               (QUOTEP TERM)
               (CONSP (UNQUOTE TERM)))
              (RP-TERMP (CADDR (PUT-TERM-IN-CONS term))))
     :hints (("Goal"  :in-theory (enable PUT-TERM-IN-CONS  )))))

  (local
   (defthm lemma13
     (implies (and (SHOULD-TERM-BE-IN-CONS rule-lhs term)
                   t)
              (AND (QUOTEP TERM)
                   (CONSP (UNQUOTE TERM))
                   (is-cons rule-lhs)))
     :hints (("Goal" :in-theory (enable is-cons should-term-be-in-cons)))))

  (defthm-rp-equal2
    (defthm rp-evl-of-rp-equal2
      (implies (and (rp-termp term1)
                    (rp-termp term2)
                    (rp-equal2 term1 term2))
               (equal (equal (rp-evl term1 a)
                             (rp-evl term2 a))
                      t))
      :flag rp-equal2)

    (defthm rp-evl-of-rp-equal2-subterms
      (implies (and (rp-equal2-subterms subterm1 subterm2)
                    (rp-term-listp subterm1)
                    (rp-term-listp subterm2))
               (equal (equal (rp-evl-lst subterm1 a)
                             (rp-evl-lst subterm2 a))
                      t))
      :flag rp-equal2-subterms)))

(defthm rp-equal2-of-ex-from-rp
  (implies (rp-termp term)
           (equal (rp-equal2 term1 (ex-from-rp term2))
                  (rp-equal2 term1 term2)))
  :hints (("Goal" :in-theory (disable ex-from-synp)
           :do-not-induct t
           :expand ((rp-equal2 term1 (ex-from-rp term2))
                    (rp-equal2 term1 term2)))))

(defthm-rp-equal2
  (defthm rp-equal2-reflexive
    (implies (equal term1 term2)
             (rp-equal2 term1 term2))
    :flag rp-equal2)

  (defthm rp-equal2-subterms-reflexive
    (implies (equal subterm1 subterm2)
             (rp-equal2-subterms subterm1 subterm2))
    :flag rp-equal2-subterms))

(defthm-rp-equal2
  (defthm rp-equal2-booleanp
    (booleanp (rp-equal2 term1 term2))
    :flag rp-equal2)
  (defthm rp-equal2-subterms-booleanp
    (booleanp (rp-equal2-subterms subterm1 subterm2))
    :flag rp-equal2-subterms))

#|(encapsulate
  nil
  (local
   (include-book "measure-lemmas"))
  (defun
    flag2-rp-equal2
    (flag term1 term2 subterm1 subterm2)
    (declare (xargs :non-executable t :mode :logic))
    (declare
     (xargs :verify-guards nil
            :normalize nil
            :measure (case flag (rp-equal2 (cons-count term2))
                       (otherwise (cons-count subterm2)))
            :hints nil
            :well-founded-relation o<
            :mode :logic)
     (ignorable term1 term2 subterm1 subterm2))
    (prog2$
     (acl2::throw-nonexec-error
      'flag2-rp-equal2
      (list flag term1 term2 subterm1 subterm2))
     (cond
      ((equal flag 'rp-equal2)
       ((lambda
         (term1 term2)
         ((lambda
           (term1 term2)
           ((lambda
             (term2 term1)
             ((lambda
               (term2 term1)
               (if
                (consp term1)
                (if
                 (consp term2)
                 (if
                  (should-term-be-in-cons term2 term1)
                  ((lambda
                    (nterm term2)
                    (if (flag2-rp-equal2 'rp-equal2
                                         (car (cdr nterm))
                                         (car (cdr term2))
                                         nil nil)
                        (flag2-rp-equal2 'rp-equal2
                                         (car (cdr (cdr nterm)))
                                         (car (cdr (cdr term2)))
                                         nil nil)
                        'nil))
                   (put-term-in-cons term1)
                   term2)
                  (if
                   (should-term-be-in-cons term1 term2)
                   ((lambda
                     (nterm term1)
                     (if (flag2-rp-equal2 'rp-equal2
                                          (car (cdr term1))
                                          (car (cdr nterm))
                                          nil nil)
                         (flag2-rp-equal2 'rp-equal2
                                          (car (cdr (cdr term1)))
                                          (car (cdr (cdr nterm)))
                                          nil nil)
                         'nil))
                    (put-term-in-cons term2)
                    term1)
                   (if
                    (quotep term1)
                    (equal term1 term2)
                    (if (quotep term2)
                        (equal term1 term2)
                        (if (equal (car term1) (car term2))
                            (flag2-rp-equal2 'rp-equal2-subterms
                                             nil nil (cdr term1)
                                             (cdr term2))
                            'nil)))))
                 'nil)
                (equal term1 term2)))
              (extract-from-synp term2)
              term1))
            (ex-from-rp term2)
            term1))
          (extract-from-synp term1)
          term2))
        (ex-from-rp term1)
        term2))
      (t (if (consp subterm1)
             (if (consp subterm2)
                 (if (flag2-rp-equal2 'rp-equal2
                                      (car subterm1)
                                      (car subterm2)
                                      nil nil)
                     (flag2-rp-equal2 'rp-equal2-subterms
                                      nil nil (cdr subterm1)
                                      (cdr subterm2))
                     'nil)
                 'nil)
             (equal subterm1 subterm2)))))))||#

(encapsulate
  nil

  (local
   (in-theory (disable ex-from-synp)))

  (local
   (defthm rp-equal2-lemma1
     (implies (should-term-be-in-cons term1 term2)
              (not (should-term-be-in-cons term2 term1)))
     :hints (("Goal" :in-theory (enable should-term-be-in-cons)))))

  (defthm-rp-equal2
    (defthm rp-equal2-is-symmetric
      (equal (rp-equal2 term2 term1)
             (rp-equal2 term1 term2))
      :flag rp-equal2)
    (defthm rp-equal2-subterms-is-symmetric
      (equal (rp-equal2-subterms subterm2 subterm1)
             (rp-equal2-subterms subterm1 subterm2))
      :flag rp-equal2-subterms)
    :hints (("Goal" :expand ((rp-equal2 term2 term1)
                             (rp-equal2-subterms subterm2 subterm1)))))

  #|(skip-proofs
  ;; necessary for def-equiv
  (defthm-rp-equal2
  (defthm rp-equal2-transitive
  (implies (and (rp-equal2 term0 term1)
  (rp-equal2 term1 term2))
  (rp-equal2 term0 term2))
  :flag rp-equal2)

  (defthm rp-equal2-subterms2-transitive
  (implies (and (rp-equal2-subterms subterm0 subterm1)
  (rp-equal2-subterms subterm1 subterm2))
  (rp-equal2-subterms subterm0 subterm2))
  :flag rp-equal2-subterms)

;:hints (("Goal" :induct (flag2-rp-equal2 flag term0 term1 term2 subterm0 ; ; ; ; ; ; ; ; ; ; ; ; ;
;                                        subterm1 subterm2))) ; ; ; ; ; ; ; ; ; ; ; ; ;
  ))||#

  )

#|(local
(defequiv rp-equal2))||#

#|(local
(defequiv rp-equal2-subterms))||#

(defthm-rp-equal-cnt
  (defthm rp-equal-cnt-is-rp-equal
    (equal (rp-equal-cnt term1 term2 cnt)
           (rp-equal term1 term2 ))
    :flag rp-equal-cnt)
  (defthm rp-equal-cnt-subterms-is-rp-equal-subterms
    (equal (rp-equal-cnt-subterms subterm1 subterm2 cnt)
           (rp-equal-subterms subterm1 subterm2 ))
    :flag rp-equal-cnt-subterms))
