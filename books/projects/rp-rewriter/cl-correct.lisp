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

(include-book "rp-rewriter")
(include-book "extract-formula")
(include-book "eval-functions")
;(include-book "proof-functions")

;(include-book "tools/with-supporters" :dir :system)
(local (include-book "proofs/extract-formula-lemmas"))
(local (include-book "proofs/rp-correct"))
(local (include-book "proofs/rp-equal-lemmas"))

(include-book "proofs/guards")

(encapsulate
  nil
  (defrec rp-cl-hints
    (runes . new-synps)
    t)
  (defun rp-cl-hints-p (hints)
    (declare (xargs :guard t))
    (and  (weak-rp-cl-hints-p hints)
          (alistp (access rp-cl-hints hints :new-synps)))))

(defun rp-clause-processor-aux (cl hints meta-rules rp-state state)
  (declare #|(ignorable rule-names)||#
   (xargs
    :guard (and (rp-meta-rule-recs-p meta-rules state)
                (rp-cl-hints-p hints))
    :stobjs (rp-state state)
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   (rp-rw-aux
                                    get-rules
                                    #|GET-ENABLED-EXEC-RULES||#
                                    beta-search-reduce))))
    :verify-guards t))
  (if (and (consp cl)
           (not (consp (cdr cl))))
      (b* ((car-cl (beta-search-reduce (car cl) *big-number*))
           ((when (not (and (rp-termp car-cl)
                            (not (include-fnc car-cl 'rp)))))
            ;; we have to have it here because pseudo-termp allows nil to
            ;; appear in the term but rp-termp does not.
            (mv nil (list cl) rp-state state))
           (runes (access rp-cl-hints hints :runes))
           ((mv runes exc-rules)
            (if runes
                (mv runes (get-disabled-exc-rules-from-table
                           (table-alist 'rp-exc-rules (w state))))
              (get-enabled-rules-from-table state)))
           (new-synps (access rp-cl-hints hints :new-synps))
           (rules-alist (get-rules runes state :new-synps new-synps))
           ((when (not (rules-alistp rules-alist)))
            (progn$ (hard-error 'rp-clause-precessor-aux
                                "format of rules-alist is bad ~%" nil)
                    (mv nil (list cl) rp-state state)))
           (rp-state (rp-state-new-run rp-state))

           (disabled-meta-rules (table-alist 'disabled-rp-meta-rules
                                             (w state)))
           (meta-rules (remove-disabled-meta-rules meta-rules disabled-meta-rules))
           (meta-rules (make-fast-alist meta-rules))
           ((mv rw rp-state)
            (rp-rw-aux car-cl
                       rules-alist
                       exc-rules
                       meta-rules
                       rp-state
                       state))
           (- (fast-alist-free meta-rules))
           (- (fast-alist-free exc-rules))
           (- (fast-alist-free rules-alist)))
        (mv nil
            (list (list rw))
            rp-state
            state))
    (mv nil (list cl) rp-state state)))

;; When the clause-processor is to be proved with a new evaluator, this lemmas
;; will be used with functional instantiation with the new evaluator and other
;; functions. We would be needing a new evaluator when we want to use a new
;; meta function.
(defthm correctness-of-rp-clause-processor-aux
  (implies (and (pseudo-term-listp cl)
                (rp-meta-valid-syntax-listp meta-rules state)
                (valid-rp-meta-rule-listp meta-rules state)
                (alistp a)
                (rp-evl-meta-extract-global-facts :state state))
           (iff (rp-evl (acl2::conjoin-clauses
                         (acl2::clauses-result
                          (rp-clause-processor-aux cl hint meta-rules rp-state state)))
                        a)
                (rp-evl (acl2::disjoin cl) a)))
  :otf-flg t
  :hints (("Goal"
           :do-not-induct t
           :expand ((REMOVE-DISABLED-META-RULES
                     NIL
                     (TABLE-ALIST 'DISABLED-RP-META-RULES
                                  (CDR (ASSOC-EQUAL 'ACL2::CURRENT-ACL2-WORLD
                                                    (NTH 2 STATE))))))
           :in-theory (e/d (rp-evl-of-fncall-args
                            ;; valid-rp-meta-rule-listp
                            rp-evl-of-beta-search-reduce
                            rp-meta-valid-syntax-listp
                            ;;symbol-alistp-get-enabled-exec-rules
                            rp-rw-aux-is-correct)
                           (get-rules
                            valid-rp-meta-rule-listp
                            
                            valid-rp-meta-rulep
                            rp-meta-valid-syntaxp-sk
                            ex-from-synp-lemma1
                            valid-rules-alistp
                            rp-rw-aux
                            #|get-enabled-exec-rules||#
                            assoc-eq
                            table-alist))))
  :rule-classes :rewrite)

;; This function needs a guard (rp-evl-meta-extract-global-facts :state state)
;; because we need to use resolve-b+-order-is-valid-rp-meta-rulep proved in
;; proofs/apply-meta-lemmas.lisp. We need to verify the guards because
;; rp-clause-processor-aux is not executable (its guards call a defun-sk).
(defun rp-clause-processor (cl hints rp-state state)
  (declare
   (xargs :stobjs (rp-state state)
          :guard t
          :guard-hints (("goal"
                         :in-theory (e/d (rp-meta-valid-syntax-listp)
                                         (rp-meta-valid-syntaxp-sk))))
          :verify-guards nil))
  (if (rp-cl-hints-p hints)
      (rp-clause-processor-aux
       cl hints
       nil
       rp-state
       state)
    (mv nil (list cl) rp-state state)))

(verify-guards rp-clause-processor)

(progn
  (table rp-rw 'meta-rules nil)

  (table rp-rw 'rp-clause-processor
         'rp-clause-processor))

(defthm correctness-of-rp-clause-processor-lemma
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (rp-evl (acl2::conjoin-clauses
                         (acl2::clauses-result (list nil (list cl) rp-state state)))
                        a))
           (rp-evl (acl2::disjoin cl) a))
  :hints (("goal"
           :in-theory (e/d (acl2::disjoin acl2::conjoin-clauses) ()))))

(defthm correctness-of-rp-clause-processor
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (rp-evl-meta-extract-global-facts :state state)
    (rp-evl (acl2::conjoin-clauses
             (acl2::clauses-result
              (rp-clause-processor cl hint rp-state state)))
            a))
   (rp-evl (acl2::disjoin cl) a))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (correctness-of-rp-clause-processor-aux
                            valid-rp-meta-rule-listp
                            rp-meta-valid-syntax-listp
                            rp-rw-aux-is-correct)
                           (rp-clause-processor-aux
                            rp-cl-hints-p
                            valid-rp-meta-rulep
                            rp-meta-valid-syntaxp-sk
                            acl2::conjoin-clauses
                            acl2::clauses-result))))
  :rule-classes :clause-processor)
