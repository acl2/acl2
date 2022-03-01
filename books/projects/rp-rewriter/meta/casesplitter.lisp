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

(include-book "../meta-rule-macros")

(include-book "../misc")

(local
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(define casesplitter-aux ((term rp-termp)
                          (cases rp-term-listp))
  :returns (res-term rp-termp :hyp (and (rp-termp term)
                                        (rp-term-listp cases)))
  (if (atom cases)
      term
    (casesplitter-aux `(if ,(car cases)
                           ,term
                         ,term)
                      (cdr cases))))

(define casesplitter ((term rp-termp)
                      (rp-state))
  :guard-hints (("Goal"
                 :in-theory (e/d (RP-STATEP) ())))
  :stobjs (rp-state)
  (b* ((cases (casesplitter-cases rp-state))
       (cases (ex-from-rp-all2-lst cases)))
    (casesplitter-aux term cases)))



(local
 (defret casesplitter-aux-correct
   (implies (and (valid-sc term a)
                 (valid-sc-subterms cases a))
            (and (valid-sc res-term a)
                 (equal (rp-evlt res-term a)
                        (rp-evlt term a))))
   :fn casesplitter-aux
   :hints (("Goal"
            :in-theory (e/d (casesplitter-aux
                             is-if
                             is-rp
                             )
                            ())))))


(add-preprocessor
 :processor-fnc casesplitter
 :hints (("Goal"
          :in-theory (e/d (casesplitter
                           RP-STATEP)
                          ()))))
                  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Casesplit from context

(defthmd implies-redef-with-casesplit-from-context-trig
  (equal (implies p q)
         (if p (casesplit-from-context-trig (if q t nil)) t))
  :hints (("Goal"
           :in-theory (e/d (casesplit-from-context-trig
                            implies)
                           ()))))

(add-rp-rule implies-redef-with-casesplit-from-context-trig
             :outside-in t)
  

(define casesplit-from-context-getcases-aux (term)
  :returns res
  (case-match term
    (('if a b c)
     (if (and (quotep b)
              (quotep c))
         nil
       (append (list a)
               (casesplit-from-context-getcases-aux b)
               (casesplit-from-context-getcases-aux c))))
    (& nil))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (rp-termp term)
             (rp-term-listp res))))

(define casesplit-from-context-getcases (context)
  :Returns res
  (if (atom context)
      nil
    (append (casesplit-from-context-getcases-aux (car context))
            (casesplit-from-context-getcases (cdr context))))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (rp-term-listp context)
             (rp-term-listp res))))


(define casesplit-from-context-aux ((term)
                                    (dont-rw)
                                    (cases))
  :returns (mv (res-term rp-termp :hyp (and (rp-termp term)
                                            (rp-term-listp cases)))
               dont-rw) 
  (if (atom cases)
      (mv term dont-rw)
    (casesplit-from-context-aux `(if ,(car cases)
                                     ,term
                                   ,term)
                                `(nil t ,dont-rw ,dont-rw)
                                (cdr cases))))


(define casesplit-from-context (term dont-rw context)
  :Returns (mv res dont-rw)
  (case-match term
    (('casesplit-from-context-trig term)
     (b* ((cases (ex-from-rp-all2-lst (casesplit-from-context-getcases context)))
          (dont-rw (dont-rw-car (dont-rw-cdr dont-rw)))
          ((mv term dont-rw)
           (casesplit-from-context-aux term dont-rw cases)))
       (mv term dont-rw)))
    (& (mv term dont-rw))))

(local
 (defret casesplit-from-context-aux-correct
   (implies (and (valid-sc term a)
                 (valid-sc-subterms cases a))
            (and (valid-sc res-term a)
                 (equal (rp-evlt res-term a)
                        (rp-evlt term a))))
   :fn casesplit-from-context-aux
   :hints (("Goal"
            :in-theory (e/d (casesplit-from-context-aux
                             is-if
                             is-rp
                             )
                            ())))))

(rp::add-meta-rule
 :meta-fnc casesplit-from-context
 :trig-fnc casesplit-from-context-trig
 :valid-syntaxp t
 :outside-in t
 :returns (mv term dont-rw)
 :hints (("Goal"
          :in-theory (e/d (casesplit-from-context
                           CASESPLIT-FROM-CONTEXT-TRIG)
                          ()))))
       


