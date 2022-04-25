; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

(define equal-of-if-with-constants-aux1 (term)
  :returns is-booleanp
  (cond ((atom term)
         nil)
        ((and (quotep term)
              (consp (cdr term)))
         (booleanp (unquote term)))
        ((case-match term (('equal & &) t))
         t)
        ((is-if term)
         (and (equal-of-if-with-constants-aux1 (caddr term))
              (equal-of-if-with-constants-aux1 (cadddr term))))
        (t nil)))


         

(define equal-of-if-with-constants-aux (term const)
  :returns (mv (res rp-termp :hyp (rp-termp term))
               valid
               dont-rw)
  :guard-hints (("Goal"
                 :in-theory (e/d (is-if) ())))
  (cond
   ((atom term)
    (mv ''nil  nil nil))
   ((and (quotep term)
         (consp (cdr term)))
    (mv `',(equal (unquote term) const)  t t))
   
   ((Is-if term)
    (b* ((test (cadr term))
         (then (caddr term))
         (else (cadddr term))
         (booleanp-test (equal-of-if-with-constants-aux1 test))
         ((Unless booleanp-test)
          (mv ''nil  nil nil))
         ((mv then-res  then-valid then-dont-rw)
          (equal-of-if-with-constants-aux then const))
         ((mv else-res  else-valid else-dont-rw)
          (equal-of-if-with-constants-aux else const))
         ((unless (and then-valid else-valid))
          (mv ''nil  nil nil))
         ((when (and (equal then-res ''nil)
                     (equal else-res ''nil)))
          (mv ''nil  t t)))
      (mv `(if ,test ,then-res ,else-res)
          t
          `(if t ,then-dont-rw ,else-dont-rw))))
   (t (mv ''nil nil nil))))

(define equal-of-if-with-constants ((term))
  :returns (mv (res rp-termp :hyp (rp-termp term))
               dont-rw)
  (case-match term
    (('equal ('if & & &) ('quote x))
     (b* (((mv res  valid dont-rw)
           (equal-of-if-with-constants-aux (cadr term)
                                          x)))
       (if valid
           (mv res dont-rw)
         (mv term nil))))
    (('equal ('quote x) ('if & & &))
     (b* (((mv res  valid dont-rw)
           (equal-of-if-with-constants-aux (caddr term)
                                          x)))
       (if valid
           (mv res dont-rw)
         (mv term nil))))
    (&
     (mv term nil))))


(local
 (defthm rp-evlt-of-if
   (equal (rp-evlt `(if ,x ,y ,z) a)
          (if (rp-evlt x a)
              (rp-evlt y a)
            (rp-evlt z a)))))

(local
 (defthm rp-evlt-of-if-2
   (implies (is-if term)
            (equal (rp-evlt term a)
                   (if (rp-evlt (cadr term) a)
                       (rp-evlt (caddr term) a)
                     (rp-evlt (cadddr term) a))))))

(local
 (defthm rp-evlt-of-equal
   (equal (rp-evlt `(equal ,x ,y) a)
          (equal (rp-evlt x a)
                 (rp-evlt y a)))))

(local
 (defret booleanp-of-equal-of-if-with-constants-aux
   (implies is-booleanp
            (booleanp (rp-evlt term a)))
   :fn equal-of-if-with-constants-aux1
   :hints (("Goal"
            :in-theory (e/d (equal-of-if-with-constants-aux1)
                            ())))))
 

(local
 (defret eval-of-equal-of-if-with-constants-aux
  (implies (and valid)
           (equal (rp-evlt res a)
                  (rp-evlt `(equal ,term ',const) a)))
  :fn equal-of-if-with-constants-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (equal-of-if-with-constants-aux term const)
           :in-theory (e/d (equal-of-if-with-constants-aux)
                           (cons-equal
                            rp-termp
                            rp-trans
                            rp-trans-lst))))))

(local
 (defret valid-of-equal-of-if-with-constants-aux
  (implies (valid-sc term a)
           (valid-sc res a))
  :fn equal-of-if-with-constants-aux
  :hints (("Goal"
           :do-not-induct t
           :induct (equal-of-if-with-constants-aux term const)
           :in-theory (e/d (is-if
                            equal-of-if-with-constants-aux)
                           (cons-equal
                            rp-termp
                            rp-trans
                            rp-trans-lst))))))


(local
 (defthm rp-evlt-of-equal2
   (implies (case-match term (('equal & &) t))
            (equal (rp-evlt term a)
                   (equal (rp-evlt (cadr term) a)
                          (rp-evlt (caddr term) a))))))

(rp::add-meta-rule
 :meta-fnc equal-of-if-with-constants 
 :trig-fnc equal
 :valid-syntaxp t
 :returns (mv term dont-rw)
 :hints (("Goal"
          :in-theory (e/d (equal-of-if-with-constants)
                          (;;RP-EVL-OF-EQUAL-CALL
                           is-if
                           rp-trans
                           rp-trans-lst
                           EX-FROM-RP-LEMMA1
                           EVL-OF-EXTRACT-FROM-RP-2)))))
