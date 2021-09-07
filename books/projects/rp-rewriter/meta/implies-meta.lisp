; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Regents of the University of Texas
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

(include-book "../meta-rule-macros")

(include-book "../misc")

(local
 (include-book "../proofs/rp-rw-lemmas"))

(local
 (include-book "../proofs/extract-formula-lemmas"))

(local
 (include-book "../proofs/rp-correct"))

;; as a back up, add the definition rule
(add-rp-rule implies :outside-in t)

(define implies-meta (term dont-rw)
  :verify-guards nil
  :returns (mv (res-term)
               (dont-rw))
  (case-match term
    (('implies p q)
     (b* (((when (cons-count-compare term 2000))
           (mv term dont-rw)) ;; when term is too large, exit and let the outside-in
          ;; definition rule take  care of it so we don't  try working with big
          ;; terms.
          (context (rp-extract-context p))
          (q (attach-sc-from-context context q)))
       (mv `(if ,p (if ,q 't 'nil) 't)
           `(nil ,(dont-rw-car (dont-rw-cdr dont-rw))
                 (nil ,(dont-rw-car (dont-rw-cdr (dont-rw-cdr dont-rw))) t t)
                 t)))) 
    (& (mv term dont-rw))))

#|(local
 (defthm true-listp-of-ATTACH-SC-FROM-CONTEXT
   (implies (TRUE-LISTP TERM)
            (TRUE-LISTP (MV-NTH 0
                                (ATTACH-SC-FROM-CONTEXT term
                                                        TERM2))))
   :hints (("Goal"
            :in-theory (e/d (ATTACH-SC-FROM-CONTEXT) ())))))||#


(verify-guards implies-meta)

;; (implies-meta `(implies (if (bitp x) (integerp (fn z)) 'nil)
;;                         (foo x (fn z))))

(local
 (defret rp-termp-of-<fn>
   (implies (rp-termp term)
            (rp-termp res-term))
   :fn implies-meta
   :hints (("Goal"
            :in-theory (e/d (implies-meta) ())))))

(local
 (defret rp-evlt-of-<fn>
   (implies t
            (and (equal (rp-evlt res-term a)
                        (rp-evlt term a))))
   :fn implies-meta
   :hints (("Goal"
            :in-theory (e/d (implies-meta is-rp is-if)
                            (rp-termp))))))


(local
 (defret valid-sc-and-rp-evlt-of-<fn>
   (implies (and (valid-sc term a)
                 (rp-termp term))
            (valid-sc res-term a))
   :fn implies-meta
   :hints (("Goal"
            :in-theory (e/d (implies-meta is-rp is-if)
                            (rp-termp
                             is-falist))))))


(rp::add-meta-rule
 :meta-fnc implies-meta
 :trig-fnc implies
 :valid-syntaxp t
 :outside-in t
 :returns (mv term dont-rw))
