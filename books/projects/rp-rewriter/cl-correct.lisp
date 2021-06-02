; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Regents of the University of Texas
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

(local (include-book "proofs/extract-formula-lemmas"))
(local (include-book "proofs/rp-correct"))
(local (include-book "proofs/rp-equal-lemmas"))

(include-book "proofs/guards")

(encapsulate
  nil
  (defrec rp-cl-hints
    (runes runes-outside-in . new-synps)
    t)
  (defun rp-cl-hints-p (hints)
    (declare (xargs :guard t))
    (and  (weak-rp-cl-hints-p hints)
          (or (alistp (access rp-cl-hints hints :new-synps))
              (hard-error 'rp-cl-hints-p
                          "The :new-synps hint should be an alist. ~%" nil)))))

(defund get-meta-rules (table-entry)
  (declare (xargs :guard t ))
  (if (or (atom table-entry)
          (atom (car table-entry)))
      nil
    (b* ((e (cdar table-entry)))
      (append (true-list-fix e) (get-meta-rules (cdr table-entry))))))

(defun rp-clause-processor-aux (cl hints rp-state state)
  (declare
   (xargs
    :guard (and
            (rp-cl-hints-p hints))
    :stobjs (rp-state state)
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   (preprocess-then-rp-rw
                                    get-rules
                                    beta-search-reduce))))
    :verify-guards t))
  (if (and (consp cl)
           (not (consp (cdr cl))))
      (b* ((car-cl (beta-search-reduce (car cl) *big-number*))
           ((when (not (and (rp-termp car-cl)
                            (mbt (rp-statep rp-state))
                            (mbt (alistp (access rp-cl-hints hints :new-synps)))
                            (or (not (include-fnc car-cl 'rp))
                                (hard-error
                                 'rp-clause-processor-aux
                                 "Conjectures given to RP-Rewriter cannot include an rp instance~%" nil)))))
            (mv nil (list cl) rp-state state))
         
           (rp-state (rp-state-new-run rp-state))
           (rp-state (rp-state-init-rules (access rp-cl-hints hints :runes)
                                          (access rp-cl-hints hints :runes-outside-in)
                                          (access rp-cl-hints hints :new-synps)
                                          rp-state
                                          state))
           ((mv rw rp-state)
            (if (rp-formula-checks state)
                (preprocess-then-rp-rw car-cl rp-state state)
              (mv car-cl rp-state))))
        (mv nil
            (list (list rw))
            rp-state
            state))
    (mv nil (list cl) rp-state state)))

(local
 (defthm correctness-of-rp-clause-processor-aux
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (rp-evl-meta-extract-global-facts :state state))
            (iff (rp-evl (acl2::conjoin-clauses
                          (acl2::clauses-result
                           (rp-clause-processor-aux cl hint rp-state state)))
                         a)
                 (rp-evl (acl2::disjoin cl) a)))
   :otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (rp-evl-of-fncall-args
                             rp-evl-of-beta-search-reduce
                             preprocess-then-rp-rw-is-correct)
                            (get-rules
                             ex-from-synp-lemma1
                             valid-rules-alistp
                             preprocess-then-rp-rw
                             assoc-eq
                             table-alist))))
   :rule-classes :rewrite))

(defun rp-rewriter (cl hints rp-state state)
  (declare
   (xargs :stobjs (rp-state state)
          :guard t
          :guard-hints (("goal"
                         :in-theory (e/d ()
                                         (rp-meta-valid-syntaxp-sk))))
          :verify-guards nil))
  (if (rp-cl-hints-p hints)
      (rp-clause-processor-aux
       cl hints
       rp-state
       state)
    (mv nil (list cl) rp-state state)))

(verify-guards rp-rewriter)

(local
 (defthm correctness-of-rp-clause-processor-lemma
   (implies (and (pseudo-term-listp cl)
                 (alistp a)
                 (rp-evl (acl2::conjoin-clauses
                          (acl2::clauses-result (list nil (list cl) rp-state state)))
                         a))
            (rp-evl (acl2::disjoin cl) a))
   :hints (("goal"
            :in-theory (e/d (acl2::disjoin acl2::conjoin-clauses) ())))))

(defthm correctness-of-rp-clause-processor
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (rp-evl-meta-extract-global-facts :state state)
    (rp-evl (acl2::conjoin-clauses
             (acl2::clauses-result
              (rp-rewriter cl hint rp-state state)))
            a))
   (rp-evl (acl2::disjoin cl) a))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (correctness-of-rp-clause-processor-aux
                            preprocess-then-rp-rw-is-correct)
                           (rp-clause-processor-aux
                            rp-cl-hints-p
                            acl2::conjoin-clauses
                            acl2::clauses-result))))
  :rule-classes :clause-processor)
