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
     (if (rp-equal  a b)
         (mv ''t t)
       (mv term `(nil t t))))
    (& (mv term nil))))

(local
 (defthm rp-valid-termp-rp-equal-meta
   (implies (rp-termp term)
            (rp-termp (mv-nth 0 (rp-equal-meta term))))
   :hints (("Goal"
            :in-theory (e/d (rp-equal-meta) ())))))

(def-formula-checks-default-evl
 rp-evl
 (strip-cars *small-evl-fncs*))

(def-formula-checks
 rp-equal-meta-formula-checks
 (rp-equal-meta
  equal))

(local
 (defthm rp-evl-of-rp-equal-meta
   (implies (rp-termp term)
            (equal (rp-evlt (mv-nth 0 (rp-equal-meta term)) a)
                   (rp-evlt term a)))
   :hints (("Goal"
            :in-theory (e/d (rp-equal-meta)
                            ())))))

(local
 (defthm valid-sc-of-rp-equal-meta
   (implies (valid-sc term a)
            (valid-sc (mv-nth 0 (rp-equal-meta term)) a))
   :hints (("Goal"
            :in-theory (e/d (rp-equal-meta)
                            ())))))

(defthm dont-rw-syntaxp-rp-equal-meta
  (dont-rw-syntaxp (mv-nth 1  (rp-equal-meta term)))
  :hints (("Goal"
           :in-theory (e/d (rp-equal-meta) ()))))

(defthm rp-equal-meta-is-valid-rp-meta-rulep
  (implies (and (rp-equal-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'rp-equal-meta
                             :trig-fnc 'equal
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            rp-equal-meta
                            RP-TERMP
                            VALID-SC)))))
(rp::add-meta-rules
 rp-equal-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'rp-equal-meta
        :trig-fnc 'equal
        :dont-rw t
        :valid-syntax t)))
