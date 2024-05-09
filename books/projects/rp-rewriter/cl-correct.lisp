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
(local (include-book "proofs/rp-state-functions-lemmas"))

(include-book "proofs/guards")

(progn
  (defrec rp-cl-args
    (runes runes-outside-in new-synps cases ruleset
           suppress-not-simplified-error)
    t)
  (defun rp-cl-args-p (cl-args)
    (declare (xargs :guard t))
    (and  (weak-rp-cl-args-p cl-args)
          (symbolp (access rp-cl-args cl-args :ruleset))
          (booleanp (access rp-cl-args cl-args :suppress-not-simplified-error))   
          (or (alistp (access rp-cl-args cl-args :new-synps))
              (hard-error 'rp-cl-args-p
                          "The :new-synps hint should be an alist. ~%" nil)))))

(defund get-meta-rules (table-entry)
  (declare (xargs :guard t ))
  (if (or (atom table-entry)
          (atom (car table-entry)))
      nil
    (b* ((e (cdar table-entry)))
      (append (true-list-fix e) (get-meta-rules (cdr table-entry))))))


(defun rp-clause-processor-aux (cl cl-args rp-state state)
  (declare
   (xargs
    :guard (and
            (true-listp cl)
            (rp-cl-args-p cl-args))
    :stobjs (rp-state state)
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   (acl2::disjoin
                                    preprocess-then-rp-rw
                                    update-orig-conjecture
                                    update-casesplitter-cases
                                    get-rules
                                    beta-search-reduce))))
    :verify-guards t))
  (b* (((unless (and (consp cl)
                     (not (consp (cdr cl)))))
        ;; this trap is  actually unnecessary and removing would  not cause any
        ;; problem with  rest of the  stuff here.  But  I am leaving  this here
        ;; because I never experimented with clauses with multiple literals and
        ;; I would  first want  to see  an example  before letting  the program
        ;; disjoin the clause and let the  rw start working on it. For example,
        ;; if literals come in a bad order, then it may first rewrite the large
        ;; term and then the other terms that are intended to be in the context
        ;; first.
        (progn$ (hard-error
                 'rp-clause-processor-aux
                 "RP-Rewriter currently only supports clauses with a single literal. You may make a request to fix this.~%"
                 nil)
                (mv nil (list cl) rp-state state)))

       (car-cl (acl2::disjoin cl))
       (car-cl (beta-search-reduce car-cl *big-number*))
       ((when (not (and (rp-termp car-cl)
                        (mbt (rp-statep rp-state))
                        (mbt (alistp (access rp-cl-args cl-args :new-synps)))
                        (or (not (include-fnc car-cl 'rp))
                            (hard-error
                             'rp-clause-processor-aux
                             "Conjectures given to RP-Rewriter cannot include an rp instance~%" nil))
                        (or (not (include-fnc car-cl 'equals))
                            (hard-error
                             'rp-clause-processor-aux
                             "Conjectures given to RP-Rewriter cannot include an equals instance~%" nil)))))
        (mv nil (list cl) rp-state state))

       (rp-state (update-orig-conjecture car-cl rp-state))
       
       (rp-state (rp-state-new-run rp-state))
       (cases (access rp-cl-args cl-args :cases))
       (rp-state (if (rp-term-listp cases)
                     (update-casesplitter-cases cases rp-state)
                   (progn$ (hard-error 'rp-clause-processor-aux
                                       "Given cases does not satisfy rp-term-listp: ~p0 ~%"
                                       (list (cons #\0 cases)))
                           rp-state)))
       (rp-state (rp-state-init-rules (access rp-cl-args cl-args :runes)
                                      (access rp-cl-args cl-args :runes-outside-in)
                                      (access rp-cl-args cl-args :new-synps)
                                      rp-state
                                      state
                                      :ruleset
                                      (or (access rp-cl-args cl-args :ruleset) 'rp-rules)
                                      :suppress-not-simplified-error
                                      (and (access rp-cl-args cl-args :suppress-not-simplified-error) t)))
       
       ((mv rw rp-state)
        (if (and (rp-meta-fnc-formula-checks state)
                 (rp-proc-formula-checks state))
            (preprocess-then-rp-rw car-cl rp-state state)
          (mv car-cl rp-state))))
    (mv nil
        (list (list rw))
        rp-state
        state)))

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
                            (update-orig-conjecture
                             get-rules
                             update-casesplitter-cases
                             ex-from-synp-lemma1
                             valid-rules-alistp
                             preprocess-then-rp-rw
                             assoc-eq
                             table-alist))))
   :rule-classes :rewrite))

(defun rp-rewriter (cl cl-args rp-state state)
  (declare
   (xargs :stobjs (rp-state state)
          :guard t
; Matt K. mod, 8/30/2023: The :guard-hints were formerly ignored by a later
; verify-guards event, but that has changed.  When the verify-guards event
; below uses the :in-theory below on "goal", guard verification fails, because
; RP-META-VALID-SYNTAXP-SK does not designate any rules.  So we comment this
; out so that once again, there are no :hints for the verify-guards event.
;         :guard-hints (("goal"
;                        :in-theory (e/d ()
;                                        (rp-meta-valid-syntaxp-sk))))
          :verify-guards nil))
  (if (and (rp-cl-args-p cl-args)
           (true-listp cl))
      (time$ (rp-clause-processor-aux cl cl-args
                                      rp-state
                                      state)
             ;;:mintime 1/2
             :msg "RP-Rewriter took ~st seconds (real-time), or ~sc seconds ~
  (cpu-time), and ~sa bytes allocated.~%~%")
    (mv (hard-error 'rp-rewriter
                    "Given cl-args does not satisfy rp-cl-args-p: ~p0 ~%"
                    (list (cons #\0 cl-args)))
        (list cl) rp-state state)))

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
                            rp-cl-args-p
                            acl2::conjoin-clauses
                            acl2::clauses-result))))
  :rule-classes :clause-processor)
