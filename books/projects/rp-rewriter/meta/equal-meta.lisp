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
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(include-book "../eval-functions")

(include-book "../meta-rule-macros")

(local
 (include-book "../proofs/measure-lemmas"))

(local
 (include-book "../proofs/rp-equal-lemmas"))

(defund rp-equal-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('equal a b)
     (if (rp-equal a b)
         (mv ''t t)
       (mv term `(nil t t))))
    (& (mv term nil))))

(defund rp-equal-cnt-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('equal a b)
     (if (rp-equal-cnt a b 3)
         (mv ''t t)
       (mv term `(nil t t))))
    (& (mv term nil))))

(def-formula-checks-default-evl
 rp-evl
 (strip-cars *small-evl-fncs*))

(rp::add-meta-rule
 :meta-fnc rp-equal-meta
 :trig-fnc equal
 :valid-syntaxp t
 :returns (mv term dont-rw)
 :disabledp t
 :hints (("Goal"
          :in-theory (e/d (rp-equal-meta) ()))))

(rp::add-meta-rule
 :meta-fnc rp-equal-cnt-meta
 :trig-fnc equal
 :valid-syntaxp t
 :returns (mv term dont-rw)
 :hints (("Goal"
          :in-theory (e/d (RP-EQUAL-CNT-META) ()))))
