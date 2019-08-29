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
(local (include-book "local-lemmas"))
(local (include-book "aux-function-lemmas"))
(include-book "proof-functions")
(local (include-book "proof-function-lemmas"))
(local (include-book "rp-equal-lemmas"))
(local (include-book "apply-bindings-lemmas"))
(local (include-book "match-lhs-lemmas"))
(local (include-book "rp-rw-lemmas"))

(in-theory (disable rp-iff-flag rp-lhs rp-rhs rp-hyp))


(local
 (encapsulate
   nil
   (local
    (defthm lemma1
      (implies (and (consp term)
                    (consp (cdr term))
                    (consp (cddr term))
                    (not (equal (car term) 'quote))
                    (pseudo-termp2 term))
               (and (pseudo-termp2 (caddr term))
                    (pseudo-termp2 (cadr term))))))

   (local
    (defthm lemma2
      (implies (and (consp term)
                    (consp (cdr term))
                    (consp (cddr term))
                    (not (equal (car term) 'quote))
                    (all-falist-consistent term))
               (and (all-falist-consistent (caddr term))
                    (all-falist-consistent (cadr term))))))

   (local
    (defthm lemma3
      (implies (and (consp term)
                    (consp (cdr term))
                    (consp (cddr term))
                    (not (equal (car term) 'quote))
                    (rp-syntaxp term))
               (and (rp-syntaxp (caddr term))
                    (rp-syntaxp (cadr term))))
      :hints (("Goal"
               :in-theory (e/d (is-rp) ())))))

   (local
    (defthm lemma4
      (implies (and (valid-sc term a)
                    (consp term)
                    (consp (cdr term))
                    (consp (cddr term))
                    (equal (car term) 'implies))
               (and (valid-sc (cadr term) a)
                    (valid-sc (caddr term) a)))
      :hints (("Goal"
               :expand ((VALID-SC TERM A))
               :in-theory (e/d (is-if is-rp) ())))))

   (defthm rp-rw-aux-is-correct-lemma
     (implies (and (valid-termp term nil a)
                   (not (include-fnc term 'rp))
                   (alistp a)
                   (rp-evl-meta-extract-global-facts :state state)
                   (valid-rp-meta-rule-listp meta-rules state)
                   (rp-meta-valid-syntax-listp meta-rules state)
                   (symbol-alistp exc-rules)
                   (valid-rules-alistp rules-alist))
              (iff (rp-evl
                    (mv-nth 0 (rp-rw-aux term rules-alist exc-rules meta-rules rp-state state)) a)
                   (rp-evl term a)))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term term #|(REMOVE-RETURN-LAST TERM)||#)
                               (dont-rw nil)
                               (context nil)
                               (limit (NTH *RW-STEP-LIMIT* RP-STATE))
                               (iff-flg t))
                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (CADR term #|(REMOVE-RETURN-LAST TERM)||#))
                               (dont-rw nil)
                               (context nil)
                               (limit (NTH *RW-STEP-LIMIT* RP-STATE))
                               (iff-flg t))
                    (:instance rp-evl-and-side-cond-consistent-of-rp-rw
                               (term (CADDR term #|(REMOVE-RETURN-LAST TERM)||#))
                               (dont-rw nil)
                               (context (RP-EXTRACT-CONTEXT
                                         (MV-NTH 0
                                                 (RP-RW (CADR term #|(REMOVE-RETURN-LAST TERM)||#)
                                                        NIL NIL (NTH *RW-STEP-LIMIT* RP-STATE)
                                                        RULES-ALIST EXC-RULES
                                                        meta-rules T rp-state STATE))))
                               (limit (NTH *RW-STEP-LIMIT* RP-STATE))
                               (iff-flg t)
                               (rp-state (MV-NTH 1
                                             (RP-RW (CADR term #|(REMOVE-RETURN-LAST TERM)||#)
                                                    NIL NIL (NTH *RW-STEP-LIMIT* RP-STATE)
                                                    RULES-ALIST EXC-RULES
                                                    meta-rules T rp-state STATE)))))
;:expand ((:free (context) (CONTEXT-SYNTAXP context)))
              :in-theory (e/d (;rp-evl-of-remove-from-last
                               context-syntaxp-implies
                               )
                              (rp-rw
                               valid-sc
                               valid-rules-alistp
                               RP-EVL-of-variable
                               valid-rp-meta-rule-listp
                               EVAL-AND-ALL
                               rp-evl-and-side-cond-consistent-of-rp-rw

                               ALL-FALIST-CONSISTENT
                               ALL-FALIST-CONSISTENT-LST
                               CONTEXT-SYNTAXP
                               INCLUDE-FNC
                               PSEUDO-TERMP2
                               TRUE-LISTP
                               
                               ;remove-return-last
                               beta-search-reduce)))))))

(defthmd no-rp-no-falist-term-implies-valid-termp
  (implies (valid-term-syntaxp term)
           (valid-termp term nil a))
  :hints (("Goal"
           :in-theory (e/d (EXT-SIDE-CONDITIONS ALL-FALIST-CONSISTENT
                                                is-falist is-rp) ()))))

(encapsulate
  nil
  (local
   (defthm lemma1
     (implies (valid-term-syntaxp term)
              (not (include-fnc term 'rp)))
     :hints (("Goal"
              :in-theory (e/d (valid-term-syntaxp) ())))))

  (defthmd rp-rw-aux-is-correct
    (implies (and (valid-term-syntaxp term)
                  (symbol-alistp exc-rules)
                  (alistp a)
                  (rp-evl-meta-extract-global-facts :state state)
                  (rp-meta-valid-syntax-listp meta-rules state)
                  (valid-rp-meta-rule-listp meta-rules state)
                  (valid-rules-alistp rules-alist))
             (iff (rp-evl (mv-nth 0 (rp-rw-aux term rules-alist exc-rules meta-rules rp-stat state)) a)
                  (rp-evl term a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (no-rp-no-falist-term-implies-valid-termp)
                             (rp-rw
                              rp-rw-aux
                              valid-rules-alistp
                              valid-term-syntaxp
                              valid-termp
                              remove-return-last
                              beta-search-reduce))))))
