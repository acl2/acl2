; MULTIPLIER RULES

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

(include-book "fnc-defs")

(defun s-of-c-trig-meta (term)
  (case-match term
    (('s-of-c-trig x)
     (case-match x
       (('s ''nil c/d)
        (mv c/d t))
       (& (mv x t))))
    (& (mv term t))))

(def-formula-checks
  s-of-c-trig-meta-checks
  (s-of-c-trig-meta))


(skip-proofs
 (defthm s-of-c-trig-meta-valid-rp-meta-rulep
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (s-of-c-trig-meta-checks state))
            (let ((rule (make rp-meta-rule-rec
                              :fnc 's-of-c-trig-meta
                              :trig-fnc 's-of-c-trig
                              :dont-rw t
                              :valid-syntax t)))
              (and (valid-rp-meta-rulep rule state)
                   (rp-meta-valid-syntaxp-sk rule state))))
   :otf-flg t
   :hints (("Goal"
            :in-theory (e/d (rp-meta-valid-syntaxp)
                            (rp-termp
                             rp-term-listp
                             valid-sc))))))

(rp::add-meta-rules
 s-of-c-trig-meta-checks
 (list
  (make rp-meta-rule-rec
        :fnc 's-of-c-trig-meta
        :trig-fnc 's-of-c-trig
        :dont-rw t
        :valid-syntax t)))
