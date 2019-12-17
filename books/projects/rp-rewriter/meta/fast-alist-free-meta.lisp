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

(defund fast-alist-free-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('fast-alist-free ('falist ('quote fast-alist) alist))
     (progn$
      (fast-alist-free fast-alist)
      (mv alist t)))
    (('fast-alist-free alist)
     (mv alist t))
    (&
     (mv term nil))))

(def-formula-checks-default-evl
 rp-evl
 (strip-cars *small-evl-fncs*))

(def-formula-checks
 fast-alist-free-meta-formula-checks
 (fast-alist-free
  fast-alist-free-meta))


(local
 (defthm valid-sc-fast-alist-free-rp-meta
   (implies (valid-sc term a)
            (valid-sc (mv-nth 0 (fast-alist-free-meta term)) a))
   :hints (("Goal"
            :in-theory (e/d (fast-alist-free-meta is-rp is-if) ())))))

(local
 (defthm rp-termp-fast-alist-free-rp-meta
   (implies (rp-termp term)
            (rp-termp (mv-nth 0 (fast-alist-free-meta term))))
   :hints (("Goal" :in-theory (enable fast-alist-free-meta)))))


(local
 (defthm rp-evl-of-fast-alist-free-meta
   (implies (and (fast-alist-free-meta-formula-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal
             (rp-evlt (mv-nth 0 (fast-alist-free-meta term)) a)
             (rp-evlt term a)))
   :hints (("Goal"
            :in-theory (e/d (fast-alist-free-meta) ())))))



(local
 (defthm dont-rw-syntaxp-fast-alist-free-meta
   (dont-rw-syntaxp (mv-nth 1 (fast-alist-free-meta term)))
   :hints (("Goal"
            :in-theory (e/d (DONT-RW-SYNTAXP
                             fast-alist-free-meta)
                            ())))))


(defthm fast-alist-free-meta-is-valid-rp-meta-rulep
  (implies (and (fast-alist-free-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'fast-alist-free-meta
                             :trig-fnc 'fast-alist-free
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            fast-alist-free-meta
                            RP-TERM-LISTP
                            
                            VALID-SC)))))


(rp::add-meta-rules
 fast-alist-free-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'fast-alist-free-meta
        :trig-fnc 'fast-alist-free
        :dont-rw t
        :valid-syntax t)))
