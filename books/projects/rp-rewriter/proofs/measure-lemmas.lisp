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

(include-book "../aux-functions")

(local
 (in-theory (disable EX-FROM-SYNP
                     should-term-be-in-cons
                     PUT-TERM-IN-CONS
                     EX-FROM-rp
                     ex-from-rp-loose
                     is-synp )))

(defthm measure-lemma1
  (and (implies (CONSP (EX-FROM-RP TERM))
                (consp term))
       (implies (CONSP (ex-from-rp-loose TERM))
                (consp term)))
  :hints (("Goal" :in-theory (enable ex-from-rp
                                     ex-from-rp-loose))))

(defthm measure-lemma1-2
  (and (implies (CONSP (cdr (EX-FROM-RP TERM)))
                (consp (cdr term)))
       (implies (CONSP (cdr (ex-from-rp-loose TERM)))
                (consp (cdr term))))
  :hints (("Goal" :in-theory (enable
                              is-rp
                              is-rp-loose
                              ex-from-rp
                              ex-from-rp-loose))))

(defthm equality-measure-lemma1
  (implies (and (< a b)
                (< b c))
           (< a c)))

(defthm m-measure-lemma1
  (IMPLIES (AND  (CONSP SUBTERM2))
           (< (CONS-COUNT (CAR SUBTERM2))
              (CONS-COUNT SUBTERM2)))
  :hints (("Goal" :in-theory (enable cons-count))))

(defthm m-measure-lemma2
  (IMPLIES (AND (CONSP SUBTERM2))
           (< (CONS-COUNT (CDR SUBTERM2))
              (CONS-COUNT SUBTERM2)))
  :hints (("Goal" :in-theory (enable cons-count))))

(defthm measure-lemma3
  (<= (cons-count (ex-from-synp term))
      (cons-count term))
  :hints (("Goal"
           :in-theory (enable is-synp ex-from-rp  ex-from-synp))))

(defthm measure-lemma4
  (and (<= (cons-count (ex-from-rp term))
           (cons-count term)))
  :hints (("Goal"
           :induct (ex-from-rp term)
           :in-theory (enable ex-from-rp-loose
                              is-synp ex-from-rp  ex-from-synp))))

(defthm measure-lemma4-v2
  (<= (cons-count (ex-from-rp-loose term))
      (cons-count term))
  :hints (("Goal"
           :induct (ex-from-rp-loose term)
           :in-theory (enable ex-from-rp-loose
                              is-synp ex-from-rp  ex-from-synp))))

(defthm equality-measure-lemma2
  (implies (and (<= a b)
                (<= b c))
           (<= a c)))

(defthm measure-lemma5
  (and (<= (cons-count (ex-from-synp (ex-from-rp term)))
           (cons-count term)))
  :hints (("Goal"
           :use ((:instance equality-measure-lemma2
                            (a (CONS-COUNT (EX-FROM-SYNP (ex-from-rp TERM))))
                            (B (CONS-COUNT (ex-from-rp TERM)))
                            (c (CONS-COUNT TERM))))
           :in-theory (disable equality-measure-lemma2)
           :do-not-induct t)))

(defthm measure-lemma5-v2
  (and (<= (cons-count (ex-from-synp (ex-from-rp-loose term)))
           (cons-count term)))
  :hints (("Goal"
           :use ((:instance equality-measure-lemma2
                            (a (CONS-COUNT (EX-FROM-SYNP (ex-from-rp-loose TERM))))
                            (B (CONS-COUNT (ex-from-rp-loose TERM)))
                            (c (CONS-COUNT TERM))))
           :in-theory (disable equality-measure-lemma2)
           :do-not-induct t)))

(defthm measure-lemma6
  (implies (and (consp a)
                (<= (cons-count a)
                    (cons-count b)))
           (< (cons-count (cdr a))
              (cons-count b))))

(defthm measure-lemma6-5
  (implies (and (consp a)
                (<= (cons-count a) (cons-count b)))
           (< (cons-count (car a))
              (cons-count b))))

(defthm measure-lemma7
  (implies (and (consp a)
                (consp (cdr a))
                (consp (cddr a))
                (<= (cons-count a)
                    (cons-count b)))
           (< (cons-count (CADDR a))
              (cons-count b))))

(defthm measure-lemma7-2
  (implies (and (consp a)
                (consp (cdr a))
                (consp (cddr a))
                (<= (cons-count a)
                    (cons-count b)))
           (< (cons-count (CADR a))
              (cons-count b)))
  :hints (("Goal" :in-theory (enable cons-count))))

(defthm m-measure-lemma3
  (implies
   (and (consp (ex-from-synp (ex-from-rp term2)))
        (should-term-be-in-cons (ex-from-synp (ex-from-rp term2)) term1))
   (< (cons-count (caddr (ex-from-synp (ex-from-rp term2))))
      (cons-count term2)))
  :hints (("Goal"
           :use ((:instance measure-lemma7
                            (a (EX-FROM-SYNP (EX-FROM-RP TERM2)))
                            (b term2)))
           :do-not-induct t
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma7)))))

(defthm m-measure-lemma3-v2
  (implies
   (and (consp (ex-from-synp (ex-from-rp-loose term2)))
        (should-term-be-in-cons (ex-from-synp (ex-from-rp-loose term2)) term1))
   (< (cons-count (caddr (ex-from-synp (ex-from-rp-loose term2))))
      (cons-count term2)))
  :hints (("Goal"
           :use ((:instance measure-lemma7
                            (a (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))
                            (b term2)))
           :do-not-induct t
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma7)))))

(defthm m-measure-lemma3-2
  (implies
   (and (consp (ex-from-synp (ex-from-rp term2)))
        (should-term-be-in-cons (ex-from-synp (ex-from-rp term2)) term1))
   (< (cons-count (cadr (ex-from-synp (ex-from-rp term2))))
      (cons-count term2)))
  :hints (("Goal"
           :use ((:instance measure-lemma7-2
                            (a (EX-FROM-SYNP (EX-FROM-RP TERM2)))
                            (b term2)))
           :do-not-induct t
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma7-2)))))

(defthm m-measure-lemma3-2-v2
  (implies
   (and (consp (ex-from-synp (ex-from-rp-loose term2)))
        (should-term-be-in-cons (ex-from-synp (ex-from-rp-loose term2)) term1))
   (< (cons-count (cadr (ex-from-synp (ex-from-rp-loose term2))))
      (cons-count term2)))
  :hints (("Goal"
           :use ((:instance measure-lemma7-2
                            (a (EX-FROM-SYNP (ex-from-rp-loose TERM2)))
                            (b term2)))
           :do-not-induct t
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma7-2)))))

(defthm m-measure-lemma4
  (and (implies
        (and (consp (ex-from-synp (ex-from-rp term2))))
        (< (cons-count (cdr (ex-from-synp (ex-from-rp term2))))
           (cons-count term2)))
       (implies
        (and (consp (ex-from-synp (ex-from-rp-loose term2))))
        (< (cons-count (cdr (ex-from-synp (ex-from-rp-loose term2))))
           (cons-count term2)))))

(defthm measure-lemma8
  (implies (and (quotep term)
                (consp (unquote term)))
           (< (cons-count (caddr (put-term-in-cons term)))
              (cons-count term)))
  :hints (("Goal" :in-theory (enable put-term-in-cons))))

(defthm measure-lemma8-2
  (implies (and (quotep term)
                (consp (unquote term)))
           (< (cons-count (cadr (put-term-in-cons term)))
              (cons-count term)))
  :hints (("Goal" :in-theory (enable cons-count
                                     put-term-in-cons))))

(defthm equality-measure-lemma3
  (implies (and (< a b)
                (<= b c))
           (< a c)))

(defthm m-measure-lemma5
  (IMPLIES
   (AND (CONSP (EX-FROM-SYNP (EX-FROM-RP TERM2)))
        (SHOULD-TERM-BE-IN-CONS term1 (EX-FROM-SYNP (EX-FROM-RP TERM2))))
   (< (CONS-COUNT (CADDR (PUT-TERM-IN-CONS (EX-FROM-SYNP (EX-FROM-RP TERM2)))))
      (CONS-COUNT TERM2)))
  :hints (("Goal"
           :use ((:instance measure-lemma8
                            (term (EX-FROM-SYNP (EX-FROM-RP TERM2)))))
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma8
                            cons-count))
           :do-not-induct t)))

(defthm m-measure-lemma5-v2
  (IMPLIES
   (AND (CONSP (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))
        (SHOULD-TERM-BE-IN-CONS term1 (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2))))
   (< (CONS-COUNT (CADDR (PUT-TERM-IN-CONS (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))))
      (CONS-COUNT TERM2)))
  :hints (("Goal"
           :use ((:instance measure-lemma8
                            (term (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))))
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma8
                            cons-count))
           :do-not-induct t)))

(defthm m-measure-lemma5-2
  (IMPLIES
   (AND (CONSP (EX-FROM-SYNP (EX-FROM-RP TERM2)))
        (SHOULD-TERM-BE-IN-CONS term1 (EX-FROM-SYNP (EX-FROM-RP TERM2))))
   (< (CONS-COUNT (CADR (PUT-TERM-IN-CONS (EX-FROM-SYNP (EX-FROM-RP TERM2)))))
      (CONS-COUNT TERM2)))
  :hints (("Goal"
           :use ((:instance measure-lemma8-2
                            (term (EX-FROM-SYNP (EX-FROM-RP TERM2)))))
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma8-2
                            cons-count))
           :do-not-induct t)))

(defthm m-measure-lemma5-2-v2
  (IMPLIES
   (AND (CONSP (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))
        (SHOULD-TERM-BE-IN-CONS term1 (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2))))
   (< (CONS-COUNT (CADR (PUT-TERM-IN-CONS (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))))
      (CONS-COUNT TERM2)))
  :hints (("Goal"
           :use ((:instance measure-lemma8-2
                            (term (EX-FROM-SYNP (EX-FROM-RP-LOOSE TERM2)))))
           :in-theory (e/d (should-term-be-in-cons)
                           (measure-lemma8-2
                            cons-count))
           :do-not-induct t)))

(defthm m-measure-lemma6
  (implies (is-if term)
           (and (< (CONS-COUNT (CADDDR TERM))
                   (CONS-COUNT TERM))
                (< (CONS-COUNT (CADDR TERM))
                   (CONS-COUNT TERM))
                (< (CONS-COUNT (CADR TERM))
                   (CONS-COUNT TERM))))
  :hints (("Goal" :in-theory (enable cons-count
                                     is-if))))

(defthm m-measure-lemma7
  (and (IMPLIES (IS-RP TERM)
                (< (CONS-COUNT (EX-FROM-RP TERM))
                   (CONS-COUNT TERM)))
       )
  :hints (("Goal" :in-theory (enable ex-from-rp
                                     ex-from-rp-loose
                                     is-rp
                                     is-rp-loose))))

(defthm m-measure-lemma7-v2
  (and (IMPLIES (IS-RP-LOOSE TERM)
                (< (CONS-COUNT (EX-FROM-RP-LOOSE TERM))
                   (CONS-COUNT TERM)))
       )
  :hints (("Goal" :in-theory (enable ex-from-rp
                                     ex-from-rp-loose
                                     is-rp
                                     is-rp-loose))))

(defthm measure-lemma10
  (implies (is-return-last term)
           (< (cons-count (cadddr term))
              (cons-count term)))
  :hints (("Goal"
           :in-theory (e/d (is-return-last
                            cons-count) ()))))

(in-theory (disable  cons-count))

(defthm cons-count-is-positive
  (<= 0 (cons-count x)))

(defthm consp-cons-count
  (implies (consp x)
           (< 0 (cons-count x))))

(defthm consp-cons-count-cdr
  (implies (consp x)
           (< (cons-count (cdr x))
              (cons-count x))))

(encapsulate
  nil
  (local
   (include-book "arithmetic-5/top" :dir :system))

  (defthm equality-measure-lemma4
    (implies (and (acl2-numberp x)
                  (acl2-numberp y))
             (equal (< (+ a x)
                       (+ a y))
                    (< x y))))

  (defthm equality-measure-lemma5
    (implies (and (acl2-numberp x))
             (equal (< a
                       (+ a x))
                    (< 0 x)))))

(defthm integerp-cons-count
  (integerp (cons-count x)))

(defthm o-p-cons-count
  (O-P (CONS-COUNT TERM)))

(defthm cons-count-car-subterms
  (IMPLIES (NOT (ATOM SUBTERMS))
           (O< (CONS-COUNT (CAR SUBTERMS))
               (CONS-COUNT SUBTERMS))))

(defthm cons-count-cdr-subterms
  (IMPLIES (AND (NOT (ATOM SUBTERMS)))
           (O< (CONS-COUNT (CDR SUBTERMS))
               (CONS-COUNT SUBTERMS))))

(defthm is-if-cons-count
  (implies (and (IS-IF TERM)
                (NOT (ATOM TERM))
                (NOT (EQ (CAR TERM) 'QUOTE)))
           (and (O< (CONS-COUNT (CADR TERM))
                    (CONS-COUNT TERM))
                (O< (CONS-COUNT (CADDDR TERM))
                    (CONS-COUNT TERM))
                (O< (CONS-COUNT (CADDR TERM))
                    (CONS-COUNT TERM))))
  :hints (("Goal"
           :in-theory (e/d (is-if) ()))))

(defthm is-rp-cons-count
  (and (IMPLIES (AND (NOT (ATOM TERM))
                     (NOT (EQ (CAR TERM) 'QUOTE))
                     (IS-RP TERM))
                (O< (CONS-COUNT (EX-FROM-RP TERM))
                    (CONS-COUNT TERM)))
       (IMPLIES (AND (NOT (ATOM TERM))
                     (NOT (EQ (CAR TERM) 'QUOTE))
                     (is-rp-loose TERM))
                (O< (CONS-COUNT (EX-FROM-RP-LOOSE TERM))
                    (CONS-COUNT TERM))))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            ex-from-rp-loose
                            is-rp
                            is-rp-loose)
                           ()))))

(defthm m-measure-lemma8
  (and (implies (consp (ex-from-rp x))
                (< (cons-count (cdr (ex-from-rp x)))
                   (cons-count x)))
       (implies (consp (ex-from-rp-loose x))
                (< (cons-count (cdr (ex-from-rp-loose x)))
                   (cons-count x)))))

(defthm m-measure-lemma9
  (and (implies (consp (ex-from-rp x))
                (< (cons-count (car (ex-from-rp x)))
                   (cons-count x)))
       (implies (consp (ex-from-rp-loose x))
                (< (cons-count (car (ex-from-rp-loose x)))
                   (cons-count x)))))

(defthm equality-measure-lemma6
  (implies (and (< a b)
                (< x y))
           (< (+ a x)
              (+ b y))))

(defthm equality-measure-lemma7
  (IMPLIES (AND (<= A B) (< X Y))
           (< (+ A X) (+ B Y))))

(defthm equality-measure-lemma8
  (implies (and (< a b)
                (<= x y))
           (< (+ x a)
              (+ b y))))

(defthm m-measure-lemma10
  (and (< (cons-count x)
          (cons-count (list x y)))
       (< (cons-count x)
          (cons-count (list y x))))
  :hints (("Goal"
           :in-theory (e/d (cons-count) ()))))

(defthm m-measure-lemma11
  (IMPLIES (CONSP X)
           (and (< (CONS-COUNT (CADR X))
                   (CONS-COUNT X))
                (< (CONS-COUNT (CAdDR X))
                   (CONS-COUNT X))
                (< (CONS-COUNT (CAddDR X))
                   (CONS-COUNT X))
                (< (CONS-COUNT (CddDR X))
                   (CONS-COUNT X))))
  :hints (("Goal"
           :in-theory (e/d (cons-count) ()))))

(defthm m-measure-lemma12
      (implies (and (consp (ex-from-rp term))
                    (Not (equal (car (ex-from-rp term))
                           'rp))
                    (consp (cdr (ex-from-rp term)))
                    (consp (cddr (ex-from-rp term)))
                    (consp (cdddr (ex-from-rp term)))
                    (not (cddddr (ex-from-rp term))))
               (o< (cons-count (cadddr (ex-from-rp term)))
                   (cons-count term)))
      :hints (("goal"
               :in-theory (e/d (cons-count ex-from-rp
                                           is-rp) ()))))


(defthm measure-lemma-cadr-ex-from-rp
   (implies (and (consp (ex-from-rp term))
                 (consp (cdr (ex-from-rp term))))
            (o< (cons-count (cadr (ex-from-rp term)))
                (cons-count term)))
   :hints (("goal"
	    :in-theory (e/d (ex-from-rp cons-count) ()))))


;;;;;;;;;;;;;;;;;;;;

(defun cons-countw (x val)
  (if (atom x)
      val
    (+ (cons-countw (car x) val)
       (cons-countw (cdr x) val))))

(defthm count-lambdas-is-if
  (implies (is-if term)
           (equal (count-lambdas term)
                  (+ (count-lambdas (cadr term))
                     (count-lambdas (caddr term))
                     (count-lambdas (cadddr term)))))
  :hints (("Goal"
           :expand ((count-lambdas term))
           :in-theory (e/d (is-if is-lambda is-lambda-strict) ()))))

(defthm count-lambdas-is-rp
  (and (implies (IS-RP TERM)
                (EQUAL (COUNT-LAMBDAS (EX-FROM-RP TERM))
                       (COUNT-LAMBDAS TERM))))
  :hints (("Goal"
           :in-theory (e/d (is-rp
                            is-rp-loose
                            is-lambda-strict is-lambda
                            ex-from-rp
                            ex-from-rp-loose)
                           ((:REWRITE MEASURE-LEMMA1))))))

(defthm count-lambdas-not-is-lambda
  (implies (and (not (is-lambda-strict term))
                (consp term)
                (not (quotep term)))
           (equal (COUNT-LAMBDAS-lst (cdr term))
                  (COUNT-LAMBDAS term))))

(defthm natp-cons-countw
  (implies (natp val)
           (natp (cons-countw x val))))

(defthm posp-cons-countw
  (implies (posp val)
           (posp (cons-countw x val))))

(defthm sum-with-positive
  (implies (posp x)
           (< y
              (+ x y))))

(defthm sum-with-positive-lemma1
  (implies (and (posp y)
                (natp x))
           (< x
              (+ x y))))

(defthm cons-countw-car
  (implies (and (posp val)
                (consp x))
           (< (CONS-COUNTW (CAR X) val)
              (CONS-COUNTW x val)))
  :hints (("Goal"
           :expand ((CONS-COUNTW x val))
           :in-theory (e/d (sum-with-positive
                            sum-with-positive-lemma1)
                           (CONS-COUNTW)))))

(defthm cons-countw-cdr
  (implies (and (posp val)
                (consp x))
           (< (cons-countw (cdr x) val)
              (cons-countw x val)))
  :hints (("Goal"
           :expand ((cons-countw x val))
           :in-theory (e/d (sum-with-positive) (cons-countw)))))

(defthm natp-sum-of-two
  (implies (and (natp a)
                (natp b))
           (natp (+ a b))))

(defthm sum-with-positive-lemma2
  (implies (posp (+ x y))
           (and (< z
                   (+ x y z))
                (< z
                   (+ x z y)))))

(defthm sum-with-positive-lemma3
  (implies (and (< a x)
                (natp z)
                (natp y))
           (< a
              (+ x y z))))

(defthm posp-of-sum-of-pos-and-natp
  (implies (and (posp x)
                (natp y))
           (and (posp (+ x y))
                (posp (+ y x)))))

(defthm cons-countw-lemma1
  (implies (and (posp l)
                (posp w)
                (< l w))
           (and (< (cons-countw (cdr x) w)
                   (+ l (cons-countw X w)))
                (< (cons-countw (car x) w)
                   (+ l (cons-countw X w)))))
  :hints (("Goal"
           :cases ((consp x))
           :expand ((cons-countw X w)
                    (cons-countw nil W))
           :in-theory (e/d (sum-with-positive-lemma2
                            posp)
                           (cons-countw)))))

(local
 (defthm cons-countw-local-lemma1
   (implies (atom x)
            (equal (cons-countw x w)
                   w))
   :hints (("Goal"
            :in-theory (e/d (cons-countw) ())))))

(defthm cons-countw-lemma2
  (implies (and (posp l)
                (posp w)
                (consp x)
                (< l w))
           (and (< (+ l (cons-countw (cdr X) w))
                   (cons-countw x w))
                (< (+ l (cons-countw (car X) w))
                   (cons-countw x w))))
  :hints (("Goal"
           :cases ((consp (car x)) (consp (cdr x)))
           :expand ((cons-countw X w))
           :in-theory (e/d (sum-with-positive-lemma2
                            cons-countw
                            posp)
                           (measure-lemma1
                            (:rewrite equality-measure-lemma6)
                            (:type-prescription cons-countw)
                            (:rewrite equality-measure-lemma6)
                            measure-lemma1-2
                            (:type-prescription member-equal))))))

(in-theory (disable cons-countw))

#|(defthm count-lambdas-beta-reduce-lambda-exprBETA-REDUCE-TERM
  (implies (is-lambda-strict term)
           (< (count-lambdas (beta-reduce-lambda-expr term))
              (count-lambdas term)))
  :hints (("Goal"
           :in-theory (e/d (is-lambda
                            is-lambda-strict
                            acl2::beta-reduce-lambda-expr
                            acl2::beta-reduce-term)
()))))||#

(defthm cons-count-cons
  (equal (cons-count (cons x y))
         (+ (cons-count x)
            (cons-count y)))
  :hints (("Goal"
           :in-theory (e/d (cons-count) ()))))

(defthm cons-count-atom
  (implies (atom x)
           (equal (cons-count x)
                  1))
  :hints (("Goal"
           :in-theory (e/d (cons-count) ()))))

(defthm cons-cons-caddr-caddr
  (implies (and (CONSP term)
                (CONSP (CDR term))
                (CONSP (CDDR term))
                (CONSP (CADDR term))
                (CONSP (CDR (CADDR term)))
                (CONSP (CDDR (CADDR term)))
                (NOT (CDDDR (CADDR term)))
                (<= (cons-count term)
                    (cons-count term2)))
           (< (CONS-COUNT (CADDR (CADDR term)))
              (CONS-COUNT TERM2)))
  :hints (("Goal"
           :in-theory (e/d (cons-count) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory measure-lemmas
  '(measure-lemma1
    measure-lemma1-2
    equality-measure-lemma1
    m-measure-lemma1
    m-measure-lemma2
    measure-lemma3
    measure-lemma4
    measure-lemma4-v2
    equality-measure-lemma2
    measure-lemma5
    measure-lemma5-v2
    measure-lemma6
    measure-lemma6-5
    measure-lemma7
    measure-lemma7-2
    m-measure-lemma3
    m-measure-lemma3-v2
    m-measure-lemma3-2
    m-measure-lemma3-2-v2
    m-measure-lemma4
    measure-lemma8
    measure-lemma8-2
    equality-measure-lemma3
    m-measure-lemma5
    m-measure-lemma5-v2
    m-measure-lemma5-2
    m-measure-lemma5-2-v2
    m-measure-lemma6
    m-measure-lemma7
    m-measure-lemma7-v2
    measure-lemma10
    cons-count-is-positive
    consp-cons-count
    consp-cons-count-cdr
    equality-measure-lemma4
    equality-measure-lemma5
    integerp-cons-count
    o-p-cons-count
    cons-count-car-subterms
    cons-count-cdr-subterms
    is-if-cons-count
    is-rp-cons-count
    m-measure-lemma8
    m-measure-lemma9
    equality-measure-lemma6
    equality-measure-lemma7
    equality-measure-lemma8
    m-measure-lemma10
    m-measure-lemma11
    m-measure-lemma12
    measure-lemma-cadr-ex-from-rp

    cons-count-atom
    cons-count-cons

    cons-cons-caddr-caddr

    natp-cons-countw
    posp-cons-countw
    cons-countw-car
    sum-with-positive
    sum-with-positive-lemma1
    sum-with-positive-lemma2
    sum-with-positive-lemma3
    posp-of-sum-of-pos-and-natp
    cons-countw-cdr
    natp-sum-of-two
    cons-countw-lemma1
    cons-countw-lemma2

    ;;    count-lambdas-beta-reduce-lambda-expr
    count-lambdas-is-if
    count-lambdas-is-rp))

(defmacro use-measure-lemmas (flg)
  (if flg
      `(in-theory (e/d (measure-lemmas)
                       (EX-FROM-SYNP
                        should-term-be-in-cons
                        PUT-TERM-IN-CONS
                        EX-FROM-rp
                        is-synp)))
    `(in-theory (e/d (EX-FROM-SYNP
                      should-term-be-in-cons
                      PUT-TERM-IN-CONS
                      EX-FROM-rp
                      is-synp )
                     (measure-lemmas)))))

(in-theory (disable measure-lemmas))
