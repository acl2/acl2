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

(include-book "../rp-state-functions")
(include-book "aux-function-lemmas")
(include-book "proof-functions")

(local
 (in-theory (enable rp-statep)))

(defthm rp-state-push-to-try-to-rw-stack-is-rp-statep
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                  rp-context
                                                                  rp-state))))
  :hints (("Goal"
           :in-theory (e/d (rp-state-push-to-try-to-rw-stack)
                           ()))))

(defthm rules-alist-outside-in-get-and-insideout-get-cancel1
  (and (equal (rules-alist-outside-in-get key (update-rw-stack-size v rp-state))
              (rules-alist-outside-in-get key rp-state))
       (equal (rules-alist-outside-in-get key (update-rw-stack v rp-state))
              (rules-alist-outside-in-get key rp-state))
       (equal (rules-alist-outside-in-get key (update-rule-frame-cnts v rp-state))
              (rules-alist-outside-in-get key rp-state))
       (equal (rules-alist-outside-in-get key (update-rules-used v rp-state))
              (rules-alist-outside-in-get key rp-state))

       (equal (rules-alist-inside-out-get key (update-rw-stack-size v rp-state))
              (rules-alist-inside-out-get key rp-state))
       (equal (rules-alist-inside-out-get key (update-rw-stack v rp-state))
              (rules-alist-inside-out-get key rp-state))
       (equal (rules-alist-inside-out-get key (update-rule-frame-cnts v rp-state))
              (rules-alist-inside-out-get key rp-state))
       (equal (rules-alist-inside-out-get key (update-rules-used v rp-state))
              (rules-alist-inside-out-get key rp-state))
       )
  :hints (("goal"
           :in-theory (e/d (rules-alist-outside-in-get
                            rules-alist-inside-out-get)
                           ()))))

#|(local
 (defthm valid-rp-statep-expand
   (implies (syntaxp (not (equal rp-state 'rp-state)))
            (equal (valid-rp-statep rp-state)
                   (let
                    ((key (valid-rp-statep-witness rp-state)))
                    (or
                     (not (symbolp key))
                     (and
                      (valid-rulesp (rules-alist-outside-in-get key rp-state))
                      (valid-rulesp (rules-alist-inside-out-get key
                                                                rp-state)))))))
   :hints (("goal"
            :in-theory (e/d (valid-rp-statep) ())))))||#

(defthm rp-state-push-to-try-to-rw-stack-is-valid-rp-state-syntaxp
  (and (implies (valid-rp-state-syntaxp rp-state)
                (valid-rp-state-syntaxp (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                                    rp-context
                                                                                    rp-state))))
       (implies (valid-rp-statep rp-state)
                (valid-rp-statep (mv-nth 1 (rp-state-push-to-try-to-rw-stack rule var-bindings
                                                                             rp-context
                                                                             rp-state)))))
  :hints (("goal"
           :expand ((valid-rp-state-syntaxp-aux
                     (update-rw-stack-size
                      (+ 1 (nth *rw-stack-size* rp-state))
                      (update-rw-stack (cons (list (nth *rw-stack-size* rp-state)
                                                   '(:type trying)
                                                   (list :rune (cdddr rule))
                                                   (list :lhs (cdr (car rule)))
                                                   (list :rhs (caddr rule))
                                                   (list :hyp (cdr (cadr rule)))
                                                   (list :context rp-context)
                                                   (list :var-bindings var-bindings))
                                             (nth *rw-stack* rp-state))
                                       rp-state)))
                    (valid-rp-statep
                     (update-rw-stack-size
                      (+ 1 (nth *rw-stack-size* rp-state))
                      (update-rw-stack (cons (list (nth *rw-stack-size* rp-state)
                                                   '(:type trying)
                                                   (list :rune (cdddr rule))
                                                   (list :lhs (cdr (car rule)))
                                                   (list :rhs (caddr rule))
                                                   (list :hyp (cdr (cadr rule)))
                                                   (list :context rp-context)
                                                   (list :var-bindings var-bindings))
                                             (nth *rw-stack* rp-state))
                                       rp-state))))
           :use ((:instance rp-state-push-to-try-to-rw-stack-is-rp-statep)
                 (:instance valid-rp-statep-necc
                            (key (valid-rp-statep-witness
                                  (update-rw-stack-size
                                   (+ 1 (nth *rw-stack-size* rp-state))
                                   (update-rw-stack (cons (list (nth *rw-stack-size* rp-state)
                                                                '(:type trying)
                                                                (list :rune (cdddr rule))
                                                                (list :lhs (cdr (car rule)))
                                                                (list :rhs (caddr rule))
                                                                (list :hyp (cdr (cadr rule)))
                                                                (list :context rp-context)
                                                                (list :var-bindings var-bindings))
                                                          (nth *rw-stack* rp-state))
                                                    rp-state)))))
                 (:instance valid-rp-state-syntaxp-aux-necc
                            (key (valid-rp-state-syntaxp-aux-witness
                                  (update-rw-stack-size
                                   (+ 1 (nth *rw-stack-size* rp-state))
                                   (update-rw-stack (cons (list (nth *rw-stack-size* rp-state)
                                                                '(:type trying)
                                                                (list :rune (cdddr rule))
                                                                (list :lhs (cdr (car rule)))
                                                                (list :rhs (caddr rule))
                                                                (list :hyp (cdr (cadr rule)))
                                                                (list :context rp-context)
                                                                (list :var-bindings var-bindings))
                                                          (nth *rw-stack* rp-state))
                                                    rp-state))))))
           :in-theory (e/d (rp-state-push-to-try-to-rw-stack
                            valid-rp-state-syntaxp)
                           (rp-statep
                            valid-rp-statep
                            update-rw-stack
                            valid-rp-state-syntaxp-aux
                            update-rw-stack-size)))))

(defthm rp-statep-rp-state-push-to-result-to-rw-stack
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-push-to-result-to-rw-stack rule
                                                           index
                                                           failed
                                                           old-term
                                                           new-term
                                                           rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-state-push-to-result-to-rw-stack) ()))))

(defthm valid-rp-statep-rp-state-push-to-result-to-rw-stack
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (rp-state-push-to-result-to-rw-stack rule
                                                                 index
                                                                 failed
                                                                 old-term
                                                                 new-term
                                                                 rp-state)))
  :hints (("goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key
                   (valid-rp-statep-witness
                    (rp-state-push-to-result-to-rw-stack rule
                                                         index
                                                         failed
                                                         old-term
                                                         new-term
                                                         rp-state)))))
           :in-theory (e/d (rp-state-push-to-result-to-rw-stack
                            valid-rp-statep
                            ;;valid-rp-statep-necc
                            )
                           (;;valid-rp-statep
                            update-rule-frame-cnts
                            (:definition valid-sc-nt)
                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            rp-statep
                            rule-frame-cnts
                            (:rewrite default-cdr)
                            rw-stack
                            nfix
                            hons-acons
                            hons-get
                            fix
                            rw-stack-size
                            rp-brr
                            rp-rune$inline
                            update-rw-stack)))))

(defthm valid-rp-state-syntaxp-rp-state-push-to-result-to-rw-stack
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (rp-state-push-to-result-to-rw-stack rule
                                                                        index
                                                                        failed
                                                                        old-term
                                                                        new-term
                                                                        rp-state)))
  :hints (("goal"
           :use (
                 (:instance rp-statep-rp-state-push-to-result-to-rw-stack)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key
                   (valid-rp-state-syntaxp-aux-witness
                    (rp-state-push-to-result-to-rw-stack rule
                                                         index
                                                         failed
                                                         old-term
                                                         new-term
                                                         rp-state)))))
           :in-theory (e/d (rp-state-push-to-result-to-rw-stack
                            valid-rp-state-syntaxp)
                           (valid-rp-statep
                            rule-list-syntaxp
                            update-rule-frame-cnts
                            (:definition valid-sc-nt)
                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            rp-statep
                            rule-frame-cnts
                            (:rewrite default-cdr)
                            rw-stack
                            nfix
                            hons-acons
                            hons-get
                            fix
                            rw-stack-size
                            rp-brr
                            rp-rune$inline
                            update-rw-stack)))))

(defthm rp-statep-rp-stat-add-to-rules-used
  (implies (rp-statep rp-state)
           (rp-statep (rp-stat-add-to-rules-used rule failed rp-state)))
  :hints (("goal"
           :in-theory (e/d (rp-stat-add-to-rules-used
                            rp-statep
                            alistp
                            hons-acons) ()))))

(defthm valid-rp-statep-rp-stat-add-to-rules-used
  (implies (valid-rp-statep rp-state)
           (valid-rp-statep (rp-stat-add-to-rules-used rule failed rp-state)))
  :hints (("goal"
           :use ((:instance
                  valid-rp-statep-necc
                  (key (valid-rp-statep-witness
                        (rp-stat-add-to-rules-used rule failed rp-state)))))
           :in-theory (e/d (rp-stat-add-to-rules-used
                            valid-rp-statep)
                           (rp-statep
                            update-rules-used
                            (:definition valid-sc-nt)
                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                            (:definition not)
                            (:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))

(defthm valid-rp-state-syntaxp-rp-stat-add-to-rules-used
  (implies (valid-rp-state-syntaxp rp-state)
           (valid-rp-state-syntaxp (rp-stat-add-to-rules-used rule failed rp-state)))
  :hints (("goal"
           :use ((:instance
                  rp-statep-rp-stat-add-to-rules-used)
                 (:instance
                  valid-rp-state-syntaxp-aux-necc
                  (key (valid-rp-state-syntaxp-aux-witness
                        (rp-stat-add-to-rules-used rule failed rp-state)))))
           :in-theory (e/d (rp-stat-add-to-rules-used
                            valid-rp-state-syntaxp
                            valid-rp-statep)
                           (rp-statep
                            update-rules-used
                            (:definition valid-sc-nt)
                            (:rewrite acl2::o-p-o-infp-car)
                            (:definition eval-and-all-nt)
                            (:rewrite default-cdr)
                            (:rewrite acl2::o-p-def-o-finp-1)
                            (:type-prescription o-p)
                            (:definition rp-hyp$inline)
                            (:definition count-used-rules-flg)
                            (:definition hons-acons)
                            (:definition hons-get)
                            (:definition nfix)
                            (:definition not)
                            (:definition rules-used)
                            (:definition show-used-rules-flg)
                            (:definition rp-rune$inline)
                            )))))


(defthm rp-statep-rp-state-new-run
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-new-run rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-state-new-run) ()))))

#|(defthm rp-statep-rp-state-new-run
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-new-run rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-state-new-run) ()))))||#

;; (defthm rp-statep-rp-state-push-meta-to-rw-stack
;;   (implies (rp-statep rp-state)
;;            (rp-statep (rp-state-push-meta-to-rw-stack meta-rule old-term new-term rp-state)))
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-state-push-meta-to-rw-stack) ()))))
