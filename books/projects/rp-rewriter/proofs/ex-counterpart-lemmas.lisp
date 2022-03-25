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

(include-book "../rp-rewriter")
(include-book "aux-function-lemmas")
(include-book "proof-functions")
(include-book "rp-state-functions-lemmas")

(defthm pseudo-termp-rp-ex-counterpart
  (implies (rp-termp term)
           (rp-termp
            (mv-nth 0 (rp-ex-counterpart term rp-state state))))
  :hints (("Goal" :in-theory (enable rp-ex-counterpart))))

(defthm rp-ex-counterpart-return-rp-statep
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1 (rp-ex-counterpart term rp-state
                                                   state))))
  :hints (("Goal"
           :in-theory (e/d (rp-ex-counterpart
                            rp-statep
                            increment-rw-stack-size
                            rp-stat-add-to-rules-used)
                           ()))))


(defthm rp-ex-counterpart-return-valid-rp-state-syntaxp
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (mv-nth 1 (rp-ex-counterpart term rp-state
                                                                state))))
  :hints (("Goal"
           :expand (rp-ex-counterpart term rp-state
                                      state)
           :use ((:instance rp-ex-counterpart-return-rp-statep)
                 (:instance valid-rp-state-syntaxp-aux-necc
                            (key (valid-rp-state-syntaxp-aux-witness
                                  (mv-nth 1 (rp-ex-counterpart term rp-state
                                                               state))))))
           :in-theory (e/d (rp-ex-counterpart
                            ;;INCREMENT-RW-STACK-SIZE
                            ;;RP-STAT-ADD-TO-RULES-USED
                            ;;valid-rp-state-syntaxp
                            )
                           (rp-statep
                            RULES-USED-PUT
                            UPDATE-RW-STACK-SIZE
                            MAGIC-EV-FNCALL-WRAPPER
                            RW-STACK-SIZE
                            (:REWRITE DEFAULT-CAR)
                            (:TYPE-PRESCRIPTION RP-STATEP)
                            (:REWRITE DEFAULT-CDR)
                            (:TYPE-PRESCRIPTION RULE-LIST-SYNTAXP)
;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION O<)
                            GET-GLOBAL
                            GLOBAL-TABLE
                            ;;UPDATE-RULES-USED
                            )))))

(defthm rp-ex-counterpart-return-valid-rp-statep
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (mv-nth 1 (rp-ex-counterpart term rp-state
                                                         state))))
  :hints (("Goal"
           :expand (rp-ex-counterpart term rp-state
                                      state)
           :use ((:instance valid-rp-statep-necc
                            (key (valid-rp-statep-witness
                                  (mv-nth 1 (rp-ex-counterpart term rp-state
                                                               state))))))
           :in-theory (e/d (rp-ex-counterpart
                            valid-rp-statep
                            valid-rp-state-syntaxp)
                           (rp-statep
                            UPDATE-RW-STACK-SIZE
                            MAGIC-EV-FNCALL-WRAPPER
                            RW-STACK-SIZE
                            VALID-RULESP
                            RULES-ALIST-OUTSIDE-IN-GET
                            RULES-ALIST-INSIDE-OUT-GET
                            (:REWRITE DEFAULT-CAR)
                            (:TYPE-PRESCRIPTION RP-STATEP)
                            (:REWRITE DEFAULT-CDR)
                            (:TYPE-PRESCRIPTION RULE-LIST-SYNTAXP)
;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION O<)
                            (:DEFINITION BITP)
                            (:DEFINITION NATP)
                            (:DEFINITION NFIX)
                            (:DEFINITION NOT)
                            GET-GLOBAL
                            GLOBAL-TABLE
                            RULES-USED-PUT
                           ;; UPDATE-RULES-USED
                            )))))


(defthm valid-sc-rp-ex-counterpart
  (implies (valid-sc term a)
           (valid-sc
            (mv-nth 0 (rp-ex-counterpart term rp-state state))
            a))
  :hints (("Goal"
           :in-theory (e/d (
                            rp-ex-counterpart) ()))))

(local
 (defthm lemma1
   (implies (and (rp-term-listp subterms)
                 (quote-listp subterms))
            (equal (RP-EVLt-LST subterms A)
                   (UNQUOTE-ALL subterms)))))

(local
 (defthm lemma3
   (implies (and (rp-term-listp subterms)
                 (quote-listp subterms))
            (equal (RP-EVL-LST subterms A)
                   (UNQUOTE-ALL subterms)))
   :hints (("Goal"
            :induct (UNQUOTE-ALL subterms)
            :do-not-induct t
            :in-theory (e/d () ())))))

(defthm rp-evl-of-rp-ex-counterpart
  (implies
   (and (rp-termp term)
        (rp-evl-meta-extract-global-facts :state state))
   (equal (rp-evlt
           (mv-nth 0 (rp-ex-counterpart term  rp-state state)) a)
          (rp-evlt term a)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((is-falist term))
           :in-theory (e/d (rp-ex-counterpart
                            rp-evl-of-fncall-args)
                           ()))))
