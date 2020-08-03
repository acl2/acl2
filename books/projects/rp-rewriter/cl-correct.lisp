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



;; (defund create-simple-meta-rules-alist-aux (meta-rules disabled-meta-rules)
;;   (declare (xargs :guard t))
;;   (if (atom meta-rules)
;;       nil
;;     (b* (((when (not (weak-rp-meta-rule-rec-p (car meta-rules))))
;;           (progn$ (hard-error 'create-simple-meta-rules-alist-aux
;;                               "Possibly broken table! ~p0"
;;                               (cons #\0 (car meta-rules)))
;;                   nil))
;;          (trig-fnc (acl2::symbol-fix (rp-meta-trig-fnc (car meta-rules))))
;;          (fnc (acl2::symbol-fix (rp-meta-fnc (car meta-rules))))
;;          (rest (create-simple-meta-rules-alist-aux (cdr meta-rules)
;;                                                disabled-meta-rules))
;;          (entry (hons-get fnc disabled-meta-rules))
;;          ((when (and entry
;;                      (cdr entry)))
;;           rest))
;;       (acons trig-fnc fnc rest))))


(defund get-meta-rules (table-entry)
 (declare (xargs :guard t ))
 (if (or (atom table-entry)
         (atom (car table-entry)))
     nil
   (b* ((e (cdar table-entry)))
     (append (true-list-fix e) (get-meta-rules (cdr table-entry))))))

;; (defund create-simple-meta-rules-alist (state)
;;   (declare (xargs :stobjs (state)))
;;   (b* ((world (w state))
;;        (rp-rw-meta-rules-with-fc (table-alist 'rp-rw-meta-rules world))
;;        (meta-rules (get-meta-rules rp-rw-meta-rules-with-fc))
;;        (disabled-meta-rules (Make-Fast-Alist (table-alist 'disabled-rp-meta-rules world)))
;;        (simple-meta-rules-list (create-simple-meta-rules-alist-aux meta-rules
;;                                                                    disabled-meta-rules))
;;        (- (fast-alist-free disabled-meta-rules)))
;;     simple-meta-rules-list))

(defwarrant rp-meta-fnc)
(defwarrant RP-META-TRIG-FNC)

(define get-enabled-meta-rules-from-table (state)
  :prepwork
  ((local
    (defthm WEAK-RP-META-RULE-RECS-P-implies-TRUE-LISTP
      (implies (WEAK-RP-META-RULE-RECS-P x)
               (TRUE-LISTP x)))))
  :guard-hints (("Goal"
                 :in-theory (e/d () (WEAK-RP-META-RULE-REC-P
                                     (:REWRITE
                                      ACL2::MEMBER-EQUAL-STRIP-CARS-ASSOC-EQUAL)
                                     HONS-GET
                                     ASSOC-EQUAL
                                     (:DEFINITION NO-DUPLICATESP-EQUAL)
                                     (:DEFINITION ALWAYS$)
                                     (:REWRITE ACL2::FANCY-UQI-INTEGER-1)
                                     (:DEFINITION INTEGER-LISTP)
                                     (:DEFINITION FGETPROP)
                                     (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES
                                               . 1)
                                     (:DEFINITION ACL2::APPLY$-BADGEP)
                                     (:DEFINITION MEMBER-EQUAL)))))
  (b* ((meta-rules-list (cdr (HONS-ASSOC-EQUAL 'meta-rules-list (table-alist 'rp-rw
                                                                        (w
                                                                         state)))))
       (rp-rules (make-fast-alist (table-alist 'rp-rules (w state))))
       ((unless (weak-rp-meta-rule-recs-p meta-rules-list))
        (progn$ (fast-alist-clean rp-rules)))
       (runes (loop$ for x in meta-rules-list
                          collect
                          :guard (weak-rp-meta-rule-rec-p x)           
                          `(:meta ,(rp-meta-fnc x) . ,(rp-meta-trig-fnc  x))))
       (res (loop$ for x in runes when (cdr (hons-get x rp-rules)) collect x))
       (- (fast-alist-clean rp-rules)))
    res))
                               
           
       
  

#|(local
 (defthm simple-meta-rule-alistp-of-create-simple-meta-rules-alist-aux
   (and (simple-meta-rule-alistp (create-simple-meta-rules-alist-aux meta-rules disabled-meta-rules))
        )
   :hints (("Goal"
            :induct (create-simple-meta-rules-alist-aux meta-rules
                                                        disabled-meta-rules)
            :do-not-induct t
            :in-theory (e/d (create-simple-meta-rules-alist
                             SIMPLE-META-RULE-ALISTP
                             CREATE-SIMPLE-META-RULES-ALIST-AUX)
                            ())))))||#

#|(local
 (defthm simple-meta-rule-alistp-of-create-simple-meta-rules-alist
   (and (simple-meta-rule-alistp (create-simple-meta-rules-alist state)))
   :hints (("Goal"
            :in-theory (e/d (create-simple-meta-rules-alist
                             SIMPLE-META-RULE-ALISTP)
                            ())))))||#

(defun rp-clause-processor-aux (cl hints rp-state state)
  (declare #|(ignorable rule-names)||#
   (xargs
    :guard (and #|(rp-meta-rule-recs-p meta-rules state)||#
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
           ;;(meta-rules (create-simple-meta-rules-alist state))
           #|(disabled-meta-rules (table-alist 'disabled-rp-meta-rules
           (w state)))||#
           #|(meta-rules (remove-disabled-meta-rules meta-rules disabled-meta-rules))||#
           ;;(meta-rules (make-fast-alist meta-rules))
           (meta-rules nil)
           ((mv rw rp-state)
            (if (rp-formula-checks state)
                (rp-rw-aux car-cl
                           rules-alist
                           exc-rules
                           meta-rules
                           rp-state
                           state)
              (mv car-cl rp-state)))
           ;;(- (fast-alist-free meta-rules))
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
                ;; (rp-meta-valid-syntax-listp meta-rules state)
                ;; (valid-rp-meta-rule-listp meta-rules state)
                ;;(rp-formula-checks state)
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
