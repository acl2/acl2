; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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

(include-book "rp-rw-lemmas")

(encapsulate
  nil

  (local
   (in-theory (disable DUMB-NEGATE-LIT2)))

  (local
   (defthm lemma5
     (implies (and (subsetp small big)
                   (eval-and-all big a))
              (eval-and-all small a))))

  (local
   (include-book "std/lists/top" :dir :system))

  (local
   (defthm lemma1
     (implies (not (equal (car term) 'if))
              (not (is-if term)))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (defthm ext-side-cond-implies
    (implies (EVAL-SC (EXT-SIDE-CONDITIONS TERM CONTEXT)
                      A)
             (EVAL-SC (EXT-SIDE-CONDITIONS (EX-FROM-RP TERM)
                                           CONTEXT)
                      A))
    :hints (("Goal"
             :induct (EX-FROM-RP TERM)
             :in-theory (e/d (is-rp ex-from-rp) ()))))

  (defthm eval-sc-lemma
    (implies (and (eval-and-all context a)
                  (syntaxp (equal context 'context)))
             (equal (eval-sc (cons (cons context x) y) a)
                    (eval-sc (cons (cons nil x) y) a))))

  (local
   (defthm lemma2
     (implies (and (NOT (RP-EVL BAD-CONTEXT A))
                   (MEMBEr BAD-CONTEXT CONTEXT))
              (not (EVAL-AND-ALL CONTEXT A)))))

  (local
   (defthm-ext-side-conditions
     (defthmd ex-and-eval-sc-lemma1-lemma
       (implies (and (member bad-context context)
                     (not (rp-evl bad-context a)))
                (EVAL-SC (EXT-SIDE-CONDITIONS term context) A))
       :flag ext-side-conditions)
     (defthmd ex-and-eval-sc-lemma1-lemma-subterms
       (implies (and (member bad-context context)
                     (not (rp-evl bad-context a)))
                (EVAL-SC (EXT-SIDE-CONDITIONS-SUBTERMS subterms context) A))
       :flag ext-side-conditions-subterms)))

  (local
   (defthm lemma3
     (implies (and (NOT (RP-EVL bad-context A)))
              (EVAL-SC (EXT-SIDE-CONDITIONS term
                                            (CONS bad-context CONTEXT))
                       A))
     :hints (("Goal"
              :use (:instance ex-and-eval-sc-lemma1-lemma
                              (context (CONS bad-context CONTEXT)))
              :in-theory (e/d () ())))))


  (local
   (include-book "measure-lemmas"))

  (defun
      flag-for-ext-side-conditions2 (flag term subterms small-context context)
    (declare (xargs :verify-guards nil
                    :measure (if (equal flag 'ext-side-conditions)
                                 (cons-count term)
                               (cons-count subterms))
                    :guard (and (pseudo-termp2 term)
                                (pseudo-term-listp2 context)))
             (ignorable small-context))
    (if (equal flag 'ext-side-conditions)
        (cond
         ((or (atom term) (quotep term)) nil)
         ((is-if term)
          (b*
              ((if-context (cadr term))
               (not-if-context (dumb-negate-lit2 if-context)))
            (append
             (flag-for-ext-side-conditions2 'ext-side-conditions
                                            (cadr term)
                                            nil
                                            small-context
                                            context)
             (flag-for-ext-side-conditions2 'ext-side-conditions
                                            (caddr term)
                                            nil
                                            (cons if-context small-context)
                                            (cons if-context context))
             (flag-for-ext-side-conditions2 'ext-side-conditions
                                            (cadddr term)
                                            nil
                                            (cons not-if-context small-context)
                                            (cons not-if-context context)))))
         ((is-rp term)
          (b* (((mv rp-context term-without-rp)
                (extract-from-rp-with-context term nil)))
            (cons (cons context rp-context)
                  (flag-for-ext-side-conditions2 'ext-side-conditions
                                                 term-without-rp
                                                 nil
                                                 small-context
                                                 context))))
         (t (flag-for-ext-side-conditions2 'ext-side-conditions-subterms
                                           nil
                                           (cdr term)
                                           small-context
                                           context)))
      (if (atom subterms)
          nil
        (append (flag-for-ext-side-conditions2 'ext-side-conditions
                                               (car subterms)
                                               nil
                                               small-context
                                               context)
                (flag-for-ext-side-conditions2 'ext-side-conditions-subterms
                                               nil
                                               (cdr subterms)
                                               small-context
                                               context)))))

  (defthm-ext-side-conditions
    (defthm ex-and-eval-sc-lemma1
      (implies (and (pseudo-termp2 term)
                    (eval-and-all context a)
                    (subsetp small-context context)
                    (EX-AND-EVAL-SC TERM small-context A))
               (EX-AND-EVAL-SC term context a))
      :flag ext-side-conditions)
    (defthm ex-and-eval-sc-lemma1-subterms
      (implies (and (eval-and-all context a)
                    (pseudo-term-listp2 subterms)
                    (subsetp small-context context)
                    (ex-and-eval-sc-subterms subterms small-context A))
               (ex-and-eval-sc-subterms subterms context a))
      :flag ext-side-conditions-subterms)
    :hints (("Goal"
             :induct (flag-for-ext-side-conditions2 FLAG TERM SUBTERMS small-context CONTEXT)
             :expand ((EXT-SIDE-CONDITIONS TERM NIL))
             :in-theory (e/d () (NOT
                                 INCLUDE-FNC
                                 EX-FROM-RP
                                 DUMB-NEGATE-LIT2
                                 )))))

  (defthm ex-and-eval-sc-lemma1-with-nil
    (implies (and (pseudo-termp2 term)
                  (eval-and-all context a)
                  (EX-AND-EVAL-SC TERM nil A))
             (EX-AND-EVAL-SC term context a))
    :hints (("Goal"
             :use (:instance
                   ex-and-eval-sc-lemma1
                   (small-context nil))

             :in-theory (e/d () (ex-and-eval-sc-lemma1)))) ))
