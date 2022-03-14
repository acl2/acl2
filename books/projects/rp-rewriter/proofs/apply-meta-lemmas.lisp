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

; Lemmas regarding the meta rules that could be added to the rewriter.

(in-package "RP")

(include-book "../rp-rewriter")
(include-book "aux-function-lemmas")
(include-book "proof-function-lemmas")
(include-book "rp-state-functions-lemmas")
(include-book "proof-functions")

(defthm rp-rw-meta-rule-main-valid-eval
  (implies (and (rp-termp term)
                (rp-term-listp context)
                (valid-sc term a)
                (valid-sc-subterms context a)
                (eval-and-all context a)
                (rp-evl-meta-extract-global-facts)
                (rp-formula-checks state)
                (rp-statep rp-state))
           (b* (((mv ?term-changed res-term ?dont-rw ?res-rp-state)
                 (rp-rw-meta-rule-main term rule dont-rw context limit rp-state state)))
             (and (valid-sc res-term a)
                  (equal (rp-evlt res-term a)
                         (rp-evlt term a)))))
  :hints (("Goal"
           :in-theory (e/d (rp-rw-meta-rule-main) ()))))

(defthm rp-rw-meta-rule-main-valid-rp-termp
  (implies (and (rp-termp term)
                (rp-term-listp context)
                (rp-statep rp-state))
           (b* (((mv ?term-changed res-term ?dont-rw ?rp-state)
                 (rp-rw-meta-rule-main term rule dont-rw context limit rp-state state)))
             (rp-termp res-term)))
  :hints (("Goal"
           :in-theory (e/d (rp-rw-meta-rule-main) ()))))

(defthm rp-rw-meta-rule-main-valid-dont-rw-syntaxp
  (implies t
           (b* (((mv ?term-changed ?res-term ?dont-rw ?rp-state)
                 (rp-rw-meta-rule-main term rule dont-rw context limit rp-state state)))
             (dont-rw-syntaxp dont-rw)))
  :hints (("Goal"
           :in-theory (e/d (rp-rw-meta-rule-main) ()))))

(defthm rp-rw-meta-rule-main-valid-rp-state-preservedp
  (implies (rp-statep rp-state)
           (b* (((mv ?term-changed ?res-term ?dont-rw res-rp-state)
                 (rp-rw-meta-rule-main term rule dont-rw context limit rp-state state)))
             (rp-state-preservedp rp-state res-rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-rw-meta-rule-main) ()))))

#|(defthm rp-statep-rp-rw-meta-rule-main
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 3 (rp-rw-meta-rule-main term rule dont-rw context rp-state state))))
  :hints (("Goal"
           :in-theory (e/d (rp-rw-meta-rule-main
                            rp-stat-add-to-rules-used-meta-cnt
                            RP-STATE-PUSH-META-TO-RW-STACK
                            RP-STATEP)
                           ()))))||#

(defthm valid-rp-state-syntaxp-implies-rp-statep
  (implies (valid-rp-state-syntaxp rp-state)
           (rp-statep rp-state))
  :hints (("Goal"
           :in-theory (e/d (valid-rp-state-syntaxp) ()))))

(defthm valid-rp-state-syntaxp-rp-rw-meta-rule-main
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (mv-nth 3 (rp-rw-meta-rule-main term rule
                                                                   dont-rw context limit rp-state state))))
  :hints (("Goal"
           :in-theory (e/d (rp-rw-meta-rule-main
                            ;;rp-stat-add-to-rules-used-meta-cnt
                            ;;RP-STATE-PUSH-META-TO-RW-STACK
                            )
                           (RP-STATEP)))))

(defthm valid-rp-statep-rp-rw-meta-rule-main
  (implies (and (valid-rp-statep rp-state)
                (rp-statep rp-state))
           (valid-rp-statep (mv-nth 3 (rp-rw-meta-rule-main term rule dont-rw
                                                            context limit rp-state state))))
  :hints (("Goal"
           :in-theory (e/d (;;rp-stat-add-to-rules-used-meta-cnt
                            ;;RP-STATE-PUSH-META-TO-RW-STACK
                            ;;valid-rp-statep
                            )
                           (RP-STATEP
                            valid-rp-statep)))))
