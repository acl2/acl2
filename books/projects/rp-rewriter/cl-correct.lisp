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
          (alistp (access rp-cl-hints hints :new-synps)))))

(defund get-meta-rules (table-entry)
 (declare (xargs :guard t ))
 (if (or (atom table-entry)
         (atom (car table-entry)))
     nil
   (b* ((e (cdar table-entry)))
     (append (true-list-fix e) (get-meta-rules (cdr table-entry))))))

(defwarrant rp-meta-fnc)
(defwarrant rp-meta-trig-fnc)

(define get-enabled-meta-rules-from-table (outside-in-flg state)
  :prepwork
  ((local
    (defthm weak-rp-meta-rule-recs-p-implies-true-listp
      (implies (weak-rp-meta-rule-recs-p x)
               (true-listp x)))))
  :guard-hints (("Goal"
                 :in-theory (e/d () (weak-rp-meta-rule-rec-p
                                     (:rewrite
                                      acl2::member-equal-strip-cars-assoc-equal)
                                     hons-get
                                     assoc-equal
                                     (:definition no-duplicatesp-equal)
                                     (:definition always$)
                                     (:rewrite acl2::fancy-uqi-integer-1)
                                     (:definition integer-listp)
                                     (:definition fgetprop)
                                     (:rewrite acl2::apply$-badgep-properties
                                               . 1)
                                     (:definition acl2::apply$-badgep)
                                     (:definition member-equal)))))
  (b* ((meta-rules-list (cdr (hons-assoc-equal 'meta-rules-list
                                               (table-alist 'rp-rw
                                                            (w state)))))
       (rp-rules (make-fast-alist (table-alist 'rp-rules (w state))))
       ((unless (weak-rp-meta-rule-recs-p meta-rules-list))
        (progn$ (fast-alist-clean rp-rules)))
       (runes (loop$ for x in meta-rules-list
                          collect
                          :guard (weak-rp-meta-rule-rec-p x)           
                          `(:meta ,(rp-meta-fnc x) . ,(rp-meta-trig-fnc  x))))
       (res (loop$ for x in runes when
                   (b* ((entry (cdr (hons-get x rp-rules))))
                     (case-match entry
                       ((':outside-in . t)
                        outside-in-flg)
                       ((':inside-out . t)
                        (not outside-in-flg))
                       ((':both . t)
                        t)
                       (&
                        (and entry
                             (not outside-in-flg)))))
                   collect x))
       (- (fast-alist-clean rp-rules)))
    res))

(defun rp-clause-processor-aux (cl hints rp-state state)
  (declare
   (xargs
    :guard (and 
            (rp-cl-hints-p hints))
    :stobjs (rp-state state)
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   (rp-rw-aux
                                    get-rules
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
           (runes-outside-in (access rp-cl-hints hints :runes-outside-in))
           (- (and runes-outside-in (not runes)
                   (cw "WARNING: You passed some values for runes-outside-in
but did not pass anything for runes. Assigning values to any one of those
values will cause runes to be not retrieved from the table.~%")))
           
           ((mv runes runes-outside-in exc-rules)
            (if (or runes runes-outside-in)
                (mv runes runes-outside-in
                    (get-disabled-exc-rules-from-table
                           (table-alist 'rp-exc-rules (w state))))
              (get-enabled-rules-from-table state)))
           (new-synps (access rp-cl-hints hints :new-synps))
           (rules-alist (get-rules runes state :new-synps new-synps))
           (rules-alist-outside-in (get-rules runes-outside-in state :new-synps new-synps))
           ((unless (and (rules-alistp rules-alist)
                         (rules-alistp rules-alist-outside-in)))
            (progn$ (hard-error 'rp-clause-precessor-aux
                                "format of rules-alist is bad ~%" nil)
                    (mv nil (list cl) rp-state state)))
           (rp-state (rp-state-new-run rp-state))
           ((mv rw rp-state)
            (if (rp-formula-checks state)
                (rp-rw-aux car-cl
                           rules-alist
                           exc-rules
                           rules-alist-outside-in
                           rp-state
                           state)
              (mv car-cl rp-state)))
           (- (fast-alist-free rules-alist-outside-in))
           (- (fast-alist-free exc-rules))
           (- (fast-alist-free rules-alist)))
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
           :expand ((remove-disabled-meta-rules
                     nil
                     (table-alist 'disabled-rp-meta-rules
                                  (cdr (assoc-equal 'acl2::current-acl2-world
                                                    (nth 2 state))))))
           :in-theory (e/d (rp-evl-of-fncall-args
                            rp-evl-of-beta-search-reduce
                            rp-meta-valid-syntax-listp
                            rp-rw-aux-is-correct)
                           (get-rules
                            valid-rp-meta-rule-listp
                            valid-rp-meta-rulep
                            rp-meta-valid-syntaxp-sk
                            ex-from-synp-lemma1
                            valid-rules-alistp
                            rp-rw-aux
                            assoc-eq
                            table-alist))))
  :rule-classes :rewrite))

(defun rp-rewriter (cl hints rp-state state)
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
       rp-state
       state)
    (mv nil (list cl) rp-state state)))

(verify-guards rp-rewriter)

(progn
  (table rp-rw 'meta-rules nil)
  (table rp-rw 'simple-meta-rules-alist nil)
  (table rp-rw 'rp-rewriter
         'rp-rewriter))

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

