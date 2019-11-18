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
(include-book "cl-correct")
(include-book "tools/templates" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;(include-book "def-formula-checks")

;; (table-alist 'rp-rw-meta-rules (w state)) has meta rules with formal checks
;; that merge as books are added.

;; (cdr (assoc-equal 'formal-checks-fn-list (table-alist 'rp-rw (w state))))
;; this only has the name of meta checks functions that cannot be merged by
;; sepearet books and is updated succesfully when a new clause processor is
;; generated.

(defun create-rp-clause-proc (cl-name-prefix appended-meta-rules)
  (list
   `(defun ,(sa cl-name-prefix "RP-CLAUSE-PROCESSOR") (cl hints rp-state state)
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
           ,appended-meta-rules
           rp-state
           state)
        (mv nil (list cl) rp-state state)))

   `(defthm ,(sa 'correctness-of-rp-clause-processor cl-name-prefix)
      (implies
       (and
        (pseudo-term-listp cl)
        (alistp a)
        (rp-evl-meta-extract-global-facts :state state)
        (rp-evl (acl2::conjoin-clauses
                 (acl2::clauses-result
                  (,(sa cl-name-prefix "RP-CLAUSE-PROCESSOR") cl hint rp-state state)))
                a))
       (rp-evl (acl2::disjoin cl) a))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (correctness-of-rp-clause-processor-aux
                                valid-rp-meta-rule-listp
                                rp-meta-valid-syntax-listp)
                               (rp-clause-processor-aux
                                valid-rp-meta-rulep
                                rp-meta-valid-syntaxp-sk
                                acl2::conjoin-clauses
                                acl2::clauses-result))))
      :rule-classes :clause-processor)))

(defun make-appended-meta-rules (all-rp-rw-meta-rules)
  (if (atom all-rp-rw-meta-rules)
      nil
    `(append (and (,(caar all-rp-rw-meta-rules) state)
                  ',(cdar all-rp-rw-meta-rules))
             ,(make-appended-meta-rules (cdr all-rp-rw-meta-rules)))))

(progn
  (defun make-appended-meta-rules2-aux1 (all-rp-rw-meta-rules)
    (if (atom all-rp-rw-meta-rules)
        nil
      (cons `',(cdar all-rp-rw-meta-rules)
            (make-appended-meta-rules2-aux1 (cdr all-rp-rw-meta-rules)))))

  (defun make-appended-meta-rules2-aux2 (all-rp-rw-meta-rules)
    (if (atom all-rp-rw-meta-rules)
        nil
      (cons `(,(caar all-rp-rw-meta-rules) state)
            (make-appended-meta-rules2-aux2 (cdr all-rp-rw-meta-rules)))))

  (defun make-appended-meta-rules2 (all-rp-rw-meta-rules)
    `(if (and . ,(make-appended-meta-rules2-aux2 all-rp-rw-meta-rules))
         (append . ,(make-appended-meta-rules2-aux1 all-rp-rw-meta-rules))
       nil)))

(defun append-entries (alist)
  (if (atom alist)
      nil
    (append (cdar alist)
            (append-entries (cdr alist)))))

(defmacro update-rp-clause-proc (cl-name-prefix)
  `(make-event
    (b* ((all-rp-rw-meta-rules (table-alist 'rp-rw-meta-rules (w state)))
         (appended-meta-rules (make-appended-meta-rules2
                               all-rp-rw-meta-rules))
         (meta-rules-list (append-entries all-rp-rw-meta-rules))
         (cl-name-prefix ',cl-name-prefix))
      `(encapsulate
         nil
         (local
          (in-theory (disable (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND)
                              (:e tau-system)
                              (:TYPE-PRESCRIPTION RP-CLAUSE-PROCESSOR-AUX)
                              (:TYPE-PRESCRIPTION BINARY-APPEND)
                              (:DEFINITION PSEUDO-TERM-LISTP)
                              (:TYPE-PRESCRIPTION RP-CLAUSE-PROCESSOR-AUX)
                              (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP)
                              (:TYPE-PRESCRIPTION ALISTP))))
         (table rp-rw 'cl-name-prefix ',cl-name-prefix)
         (table rp-rw 'meta-rules ',appended-meta-rules)
         (table rp-rw 'meta-rules-list ',meta-rules-list)
         (table rp-rw 'formal-checks-fn-list ',(strip-cars all-rp-rw-meta-rules))
         ,@(create-rp-clause-proc cl-name-prefix appended-meta-rules)))))

(defun add-meta-rules-fn (formal-checks-fn new-meta-rules cl-name-prefix)
  `(make-event
    (b* ((?talist (table-alist 'rp-rw (w state)))
         (?added-meta-rules (cdr (assoc-equal 'meta-rules talist)))
         (?added-meta-rules-list (cdr (assoc-equal 'meta-rules-list talist)))
         (?added-meta-formal-checks-fn-list (cdr (assoc-equal 'formal-checks-fn-list talist)))
         (?formal-checks-fn ',formal-checks-fn)
         (cl-name-prefix ',cl-name-prefix)
         (?new-meta-rules ',new-meta-rules))

      `(encapsulate
         nil

         (in-theory (disable ,formal-checks-fn
                             (:type-prescription ,formal-checks-fn)))

;(value-triple (cw  "Disabled for

         (table rp-rw-meta-rules
                ',formal-checks-fn
                ',new-meta-rules)

         ,@(if ',cl-name-prefix
               `((update-rp-clause-proc ,cl-name-prefix)
                 #|(table rp-rw 'cl-name-prefix ',cl-name-prefix)

                 (table rp-rw 'meta-rules `(append
                 (and (,',formal-checks-fn state)
                 ',',new-meta-rules)
                 ,',added-meta-rules))

                 (table rp-rw 'meta-rules-list (append
                 ',new-meta-rules
                 ',added-meta-rules-list))

                 (table rp-rw 'formal-checks-fn-list (cons
                 ',formal-checks-fn
                 ',added-meta-formal-checks-fn-list))

                 ,@(create-rp-clause-proc cl-name-prefix `(append
                 (and (,formal-checks-fn state)
                 ',new-meta-rules)
                 ,added-meta-rules))||#)
             nil)

         ))))

(defmacro add-meta-rules (formal-checks-fn new-meta-rules &optional cl-name-prefix)
  `(make-event
    (add-meta-rules-fn ',formal-checks-fn ,new-meta-rules ',cl-name-prefix)))

(defun is-rp-clause-processor-up-to-date (world)
  (declare (xargs :guard (and (PLIST-WORLDP world))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (hons-assoc-equal
                                                  ACL2::PLIST-WORLDP-WITH-FORMALS) ())))))
  (b* ((all-rp-rw-meta-rules (table-alist 'rp-rw-meta-rules world))
       (added-meta-formal-checks-fn-list (cdr (hons-assoc-equal
                                               'formal-checks-fn-list
                                               (table-alist 'rp-rw world)))))
    (equal (len all-rp-rw-meta-rules)
           (len added-meta-formal-checks-fn-list))))

(define check-if-clause-processor-up-to-date (world)
  (declare (xargs :guard (and (PLIST-WORLDP world))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (assoc-equal
                                                  ACL2::PLIST-WORLDP-WITH-FORMALS) ())))))
  (if (is-rp-clause-processor-up-to-date world)
      nil
    (hard-error 'defthmrp
                "The clause processor function is NOT up-to-date with respect
  to added meta rules. Run (update-rp-clause-proc cl-name-suffix) to create the
  updated clause processor. cl-name-suffix should be a unique nickname for the
  updated clause processor function. ~%"
                nil)))

(progn
  (defthm valid-rp-meta-rule-listp-opener-cons
    (equal (valid-rp-meta-rule-listp (cons rule1 rest) state)
           (and (valid-rp-meta-rulep rule1 state)
                (valid-rp-meta-rule-listp rest state)))
    :hints (("goal"
             :in-theory (e/d (valid-rp-meta-rule-listp)
                             (valid-rp-meta-rulep)))))

  (defthm valid-rp-meta-rule-listp-opener-nil
    (equal (valid-rp-meta-rule-listp nil state)
           t)
    :hints (("goal"
             :in-theory (e/d (valid-rp-meta-rule-listp)
                             (valid-rp-meta-rulep)))))

  (defthm rp-meta-valid-syntax-listp-opener-cons
    (equal (rp-meta-valid-syntax-listp (cons first rest) state)
           (and (rp-meta-valid-syntaxp-sk first state)
                (rp-meta-valid-syntax-listp rest
                                            state)))
    :hints (("goal"
             :in-theory (e/d (rp-meta-valid-syntax-listp)
                             (rp-meta-valid-syntaxp-sk)))))

  (defthm rp-meta-valid-syntax-listp-opener-nil
    (equal (rp-meta-valid-syntax-listp nil state)
           t)
    :hints (("goal"
             :in-theory (e/d (rp-meta-valid-syntax-listp)
                             (rp-meta-valid-syntaxp-sk))))))


(progn  
  (define disable-meta-rules-fnc (args)
    (if (atom args)
        nil
      (cons `(table disabled-rp-meta-rules
                    ',(car args)
                    t)
            (disable-meta-rules-fnc (cdr args)))))

  (define enable-meta-rules-fnc (args)
    (if (atom args)
        nil
      (cons `(table disabled-rp-meta-rules
                    ',(car args)
                    nil)
            (enable-meta-rules-fnc (cdr args)))))


  (defmacro disable-meta-rules (&rest args)
    (if (not args)
        `(value-triple :none)
      `(progn
         ,@(disable-meta-rules-fnc args))))

  (defmacro enable-meta-rules (&rest args)
    (if (not args)
        `(value-triple :none)
      `(progn
         ,@(enable-meta-rules-fnc args)))))
