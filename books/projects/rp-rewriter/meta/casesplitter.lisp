; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Regents of the University of Texas
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

(include-book "../meta-rule-macros")

(include-book "../misc")

(local
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(local
 (include-book "../proofs/rp-equal-lemmas"))

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
       (cases (ex-from-rp-all2-lst cases))
       (cases (reverse cases)))
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


