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

(defthm rp-state-preservedp-of-the-same-rp-state
  (implies (rp-statep rp-state)
           (rp-state-preservedp rp-state rp-state))
  :hints (("Goal"
           :in-theory (e/d (rp-state-preservedp) ()))))

(defconst *acceptable-meta-rule-args*
  '(term
    dont-rw
    context
    rp-state
    state))

(defconst *acceptable-processor-args*
  '(term
    context
    rp-state
    state))

(defconst *acceptable-meta-rule-ret-vals*
  '(term
    dont-rw
    rp-state
    state))

(defun fix-args/returns-package (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (b* (((when (not (symbolp (car lst))))
          (cons (car lst)
                (fix-args/returns-package (cdr lst))))
         (cur (symbol-name (car lst)))
         ((when (or (equal cur "rp-state")
                    (equal cur "state")))
          (cons (car lst)
                (fix-args/returns-package (cdr lst)))))
      (cons (intern$ cur "RP")
            (fix-args/returns-package (cdr lst))))))

(defun add-meta-rule-guard (meta-fnc trig-fnc formula-checks
                                     returns outside-in
                                     valid-syntaxp cl-name-prefix state)

  (declare (xargs :guard t
                  :stobjs (state)
                  :guard-hints (("Goal"
                                 :in-theory (e/d () ((:DEFINITION acl2::formals)))))))
  (and (or (and (symbolp meta-fnc)
                meta-fnc)
           (hard-error 'add-meta-rule-guard
                       "You need to pass a non-nil symbol for :meta-fnc keyword ~%"
                       nil))
       (or (and (symbolp trig-fnc)
                trig-fnc)
           (hard-error 'add-meta-rule-guard
                       "You need to pass a non-nil symbol for :trig-fnc keyword ~%"
                       nil))
       (or (and (symbolp formula-checks))
           (hard-error 'add-meta-rule-guard
                       "You need to pass a non-nil symbol for :formula-checks keyword~%"
                       nil))
       (or (subsetp-equal (true-list-fix (fix-args/returns-package (acl2::formals meta-fnc (w state))))
                          *acceptable-meta-rule-args*)
           (hard-error 'add-meta-rule-guard
                       "The arguments of your function should be a subset of
~p0 ~%"
                       (list (cons #\0 *acceptable-meta-rule-args*))))
       (or (and (symbolp returns)
                (equal (symbol-name returns) "TERM"))
           (and (symbol-listp returns)
                (> (len returns) 2)
                (equal (car returns) 'mv)
                (subsetp-equal (true-list-fix (fix-args/returns-package (cdr
                                                                         returns)))
                               *acceptable-meta-rule-ret-vals*))
           (hard-error 'add-meta-rule-guard
                       "Possible options for :returns keyword are:
1. (mv symbol1 symbol2 ...) where symbols must be a subset of ~p1
2. term
but instead you passed ~p0~%"
                       (list (cons #\0 returns)
                             (cons #\1 *acceptable-meta-rule-ret-vals*))))
       (or (booleanp valid-syntaxp)
           (hard-error 'add-meta-rule-guard
                       "You need to pass a t or nil for :valid-syntaxp keyword~%"
                       nil))

       (or (booleanp outside-in)
           (equal outside-in ':both)
           (hard-error 'add-meta-rule-guard
                       "You need to pass a t, nil or :both for :outside-in keyword~%"
                       nil))
       (or (symbolp cl-name-prefix)
           (hard-error 'add-meta-rule-guard
                       "You need to pass a symbol for :cl-name-prefix keyword~%"
                       nil))))

(defun add-processor-guard (processor-fnc formula-checks
                                          valid-syntaxp cl-name-prefix state)

  (declare (xargs :guard t
                  :stobjs (state)
                  :guard-hints (("Goal"
                                 :in-theory (e/d () ((:DEFINITION acl2::formals)))))))
  (and (or (and (symbolp processor-fnc)
                processor-fnc)
           (hard-error 'add-processor-guard
                       "You need to pass a non-nil symbol for :meta-fnc keyword ~%"
                       nil))
       (or (and (symbolp formula-checks))
           (hard-error 'add-processor-guard
                       "You need to pass a non-nil symbol for :formula-checks keyword~%"
                       nil))
       (or (subsetp-equal (true-list-fix (fix-args/returns-package (acl2::formals processor-fnc (w state))))
                          *acceptable-processor-args*)
           (hard-error 'add-processor-guard
                       "The arguments of your function should be a subset of
~p0 ~%"
                       (list (cons #\0 *acceptable-processor-args*))))
       (or (booleanp valid-syntaxp)
           (hard-error 'add-processor-guard
                       "You need to pass a t or nil for :valid-syntaxp keyword~%"
                       nil))
       (or (symbolp cl-name-prefix)
           (hard-error 'add-processor-guard
                       "You need to pass a symbol for :cl-name-prefix keyword~%"
                       nil))))

(defrec meta-rule-table-rec
  (formula-checks ;; formula-checks function for the associated meta rule
   trig-fnc ;; trigger function name
   meta-fnc ;; function name that meta rule executes
   valid-syntaxp ;; if meta rule returns valid-syntax (rp-valid-termp)
   outside-in ;; rewriting direction outside-in, inside-out or both
   returns ;; return vals of "meta-fnc"
   args
   correctness-lemma)
  t)

(defrec pre-post-processor-table-rec
  (formula-checks ;; formula-checks function for the associated meta rule
   processor-fnc ;; function name that meta rule executes
   valid-syntaxp ;; if meta rule returns valid-syntax (rp-valid-termp)
   args
   correctness-lemma
   priority)
  t)

(defund add-meta-rule-fn (meta-fnc trig-fnc formula-checks  returns outside-in
                                   valid-syntaxp hints cl-name-prefix disabledp
                                   state)
  (declare (xargs :guard (add-meta-rule-guard meta-fnc trig-fnc
                                              formula-checks returns
                                              outside-in valid-syntaxp
                                              cl-name-prefix state)
                  :stobjs (state)))
  (b* ((rune `(:meta ,meta-fnc . ,trig-fnc))
       (returns (if (symbolp returns) (list returns) returns))
       (returns (fix-args/returns-package returns))
       (returns (if (equal (len returns) 1) (car returns) returns))
       (args (true-list-fix (fix-args/returns-package (acl2::formals meta-fnc (w state)))))
       (correctness-lemma (sa meta-fnc 'for trig-fnc 'valid))
       (entry (make meta-rule-table-rec
                    :formula-checks formula-checks
                    :trig-fnc trig-fnc
                    :meta-fnc meta-fnc
                    :valid-syntaxp valid-syntaxp
                    :outside-in outside-in
                    :returns returns
                    :correctness-lemma correctness-lemma
                    :args args)))
    `(encapsulate
       nil
       (set-ignore-ok t)

       (table rp-rules ',rune
              ',(cond
                 ((equal outside-in ':both) `(:both . t))
                 (outside-in `(:outside-in . t))
                 (t `(:inside-out . t))))

       (table rp-rw-all-meta-rules ',rune ',entry)

       ,@(if disabledp
             `((disable-rules '(,rune)))
           nil)

       (defthmd ,correctness-lemma
        (and
         (implies (and (rp-evl-meta-extract-global-facts)
                       (rp-termp term)
                       (valid-sc term a)
                       ,@(append (and formula-checks
                                      `((,formula-checks state)))
                                 (and (member-equal 'context args)
                                      `((valid-sc-subterms context a)
                                        (rp-term-listp context)))
                                 (and (member-equal 'rp-state args)
                                      `((rp-statep rp-state)))))
                  (b* ((term-input term)
                       (,returns
                        (,meta-fnc . ,args)))
                    (and (equal (rp-evlt term a)
                                (rp-evlt term-input a))
                         (valid-sc term a))))

         ,@(append (and valid-syntaxp
                        `((implies (rp-termp term)
                                   (b* ((term-input term)
                                        (,returns
                                         (,meta-fnc . ,args)))
                                     (rp-termp term)))))
                   (and (true-listp returns)
                        (member-equal 'rp-state returns)
                        `((implies (rp-statep rp-state)
                                   (b* ((rp-state-input rp-state)
                                        (,returns (,meta-fnc . ,args)))
                                     (rp-state-preservedp rp-state-input
                                                          rp-state)))))))
        :hints ,hints)

       ,@(and cl-name-prefix
              `((attach-meta-fncs ,cl-name-prefix))))))

(defmacro add-meta-rule (&key meta-fnc
                              trig-fnc
                              formula-checks
                              (returns 'term)
                              (outside-in 'nil)
                              (valid-syntaxp 't)
                              (disabledp 'nil)
                              hints
                              (cl-name-prefix 'nil))
  `(make-event
    (add-meta-rule-fn ',meta-fnc
                      ',trig-fnc
                      ',formula-checks
                      ',returns
                      ',outside-in
                      ',valid-syntaxp
                      ',hints
                      ',cl-name-prefix
                      ',disabledp
                      state)))


(defmacro disable-preprocessor (processor-fnc)
  `(table rp-processors '(:preprocessor ,processor-fnc)
           nil))

(defmacro enable-preprocessor (processor-fnc)
  `(table rp-processors '(:preprocessor ,processor-fnc)
           t))

(defmacro disable-postprocessor (processor-fnc)
  `(table rp-processors '(:postprocessor ,processor-fnc)
           nil))

(defmacro enable-postprocessor (processor-fnc)
  `(table rp-processors '(:postprocessor ,processor-fnc)
           t))

(defund add-processor-fn (processor-fnc formula-checks  
                                   valid-syntaxp hints cl-name-prefix disabledp
                                   processor-type
                                   state)
  (declare (xargs :guard (add-processor-guard processor-fnc formula-checks 
                                              valid-syntaxp
                                              cl-name-prefix state)
                  :stobjs (state)))
  (b* ((rune `(,processor-type ,processor-fnc))
       (args (true-list-fix (fix-args/returns-package (acl2::formals processor-fnc (w state)))))
       (correctness-lemma (sa processor-fnc 'valid))
       (entry (make pre-post-processor-table-rec
                    :formula-checks formula-checks
                    :processor-fnc processor-fnc
                    :valid-syntaxp valid-syntaxp
                    :correctness-lemma correctness-lemma
                    :args args)))
    `(encapsulate
       nil
       (set-ignore-ok t)

       (table rp-processors ',rune ',(not disabledp))

       ,(if (equal processor-type :preprocessor)
            `(table rp-rw-all-preprocessors ',processor-fnc ',entry)
          `(table rp-rw-all-postprocessors ',processor-fnc ',entry))

       (defthmd ,correctness-lemma
        (and
         (implies (and (rp-evl-meta-extract-global-facts)
                       (rp-termp term)
                       (valid-sc term a)
                       ,@(append (and formula-checks
                                      `((,formula-checks state)))
                                 (and (member-equal 'context args)
                                      `((valid-sc-subterms context a)
                                        (rp-term-listp context)))
                                 (and (member-equal 'rp-state args)
                                      `((rp-statep rp-state)))))
                  (b* ((term-input term)
                       (term
                        (,processor-fnc . ,args)))
                    (and (equal (rp-evlt term a)
                                (rp-evlt term-input a))
                         (valid-sc term a))))

         ,@(append (and valid-syntaxp
                        `((implies (rp-termp term)
                                   (b* ((term-input term)
                                        (term
                                         (,processor-fnc . ,args)))
                                     (rp-termp term)))))
                   ))
        :hints ,hints)

       ,@(and cl-name-prefix
              `((attach-meta-fncs ,cl-name-prefix))))))

(defmacro add-preprocessor (&key processor-fnc
                                 formula-checks
                                 (valid-syntaxp 't)
                                 (disabledp 'nil)
                                 hints
                                 (cl-name-prefix 'nil))
  `(make-event
    (add-processor-fn ',processor-fnc
                      ',formula-checks
                      ',valid-syntaxp
                      ',hints
                      ',cl-name-prefix
                      ',disabledp
                      :preprocessor
                      state)))

(defmacro add-postprocessor (&key processor-fnc
                                  formula-checks
                                  (valid-syntaxp 't)
                                  (disabledp 'nil)
                                  hints
                                  (cl-name-prefix 'nil))
  `(make-event
    (add-processor-fn ',processor-fnc
                      ',formula-checks
                      ',valid-syntaxp
                      ',hints
                      ',cl-name-prefix
                      ',disabledp
                      :postprocessor
                      state)))

;; (add-meta-rule :meta-fnc test-meta-fnc
;;                :trig-fnc foo
;;                :formula-checks test-formula-checks
;;                :returns (mv term rp-state dont-rw)
;;                :outside-in t
;;                :valid-syntaxp nil
;;                :hints (("Goal"
;;                         :in-theory (e/d (test-meta-fnc) ()))))


#|(defun add-meta-rules-fn-aux (formula-checks-fn new-meta-rules  hints)
  (declare (xargs :guard (weak-rp-meta-rule-recs-p new-meta-rules)))
  (if (atom new-meta-rules)
      nil
    (cons
     `(local
       (in-theory (disable ,(rp-meta-fnc (car new-meta-rules)))))
     (cons
      (b* ((cur (car new-meta-rules))
           (dont-rw (rp-meta-dont-rw cur))
           (syntax (rp-meta-syntax-verified cur))
           (trig-fnc (rp-meta-trig-fnc cur))
           (fnc (rp-meta-fnc cur))
           (outside-in (rp-meta-outside-in cur))
           (rune `(:meta ,fnc . ,trig-fnc)))
        `(progn
           (table rp-rules ',rune
                  ',(cond
                     ((equal outside-in ':both) `(:both . t))
                     (outside-in `(:outside-in . t))
                     (t `(:inside-out . t))))

           (table rp-rw-all-meta-rules ',rune ',formula-checks-fn)

           (defthm ,(sa fnc 'for trig-fnc 'valid)
             (and (implies (and (,formula-checks-fn state)
                                (rp-evl-meta-extract-global-facts)
                                (rp-termp term)
                                (valid-sc term a))
                           (and (equal (rp-evlt
                                        ,(if dont-rw `(mv-nth 0 (,fnc term)) `(,fnc
                                                                               term))
                                        a)
                                       (rp-evlt term a))
                                (valid-sc ,(if dont-rw `(mv-nth 0 (,fnc term)) `(,fnc
                                                                                 term))
                                          a
                                          )))
                  ,@(append (and dont-rw
                                 `((dont-rw-syntaxp (mv-nth 1 (,fnc term)))))
                            (and syntax
                                 `((implies (rp-termp term)
                                            (rp-termp ,(if dont-rw `(mv-nth 0 (,fnc term)) `(,fnc
                                                                                             term))))))))
             :hints ,hints)))
      (add-meta-rules-fn-aux formula-checks-fn (cdr new-meta-rules)  hints)))))||#

#|(defun add-meta-rules-fn (formula-checks-fn new-meta-rules cl-name-prefix
                                            hints)
  (declare (ignorable hints cl-name-prefix))
  `(make-event
    (b* ((?talist (table-alist 'rp-rw (w state)))
         (?added-meta-rules (cdr (assoc-equal 'meta-rules talist)))
         (?added-meta-rules-list (cdr (assoc-equal 'meta-rules-list talist)))
         (?added-meta-formal-checks-fn-list (cdr (assoc-equal 'formal-checks-fn-list talist)))
         (formula-checks-fn ',formula-checks-fn)
         (?new-meta-rules ',new-meta-rules))
      `(encapsulate
         nil

         (in-theory (disable ,formula-checks-fn
                             (:type-prescription ,formula-checks-fn)))

         (progn ,@(add-meta-rules-fn-aux formula-checks-fn new-meta-rules ',hints))

         ))))||#

(xdoc::defxdoc
 add-meta-rule
 :parents (rp-rewriter/meta-rules)
 :short "A macro to add created meta rules to RP-Rewriter"
 :long "<p>
<code>
@('
(add-meta-rule :meta-fnc <meta-fnc-name> ;; mandatory
               :trig-fnc <trig-fnc-name> ;; mandatory
               :formula-checks <formula-check-fnc-name> ;; nil by default,
 necessary for most cases.
               :returns <return-signature>   ;; optional
               :outside-in <nil-t-or-:both>  ;; optional, nil by default
               :valid-syntaxp <t-or-nil>     ;; optional, t by default
               :disabledp <t-or-nil>         ;; optional, t by default
               :hints    <regular-ACL2-hints> ;; optional
               :cl-name-prefix <nil-or-a-unqiue-prefix> ;; optional, nil by default
               )
')
 </code>

registers a verified meta-rule for RP-Rewriter.
</p>

<p> Mandatory arguments: </p>
<ul>
<li> :meta-fnc  must be the name of the meta function. </li>
<li> :trig-fnc  the function to trigger this meta function </li>
</ul>

<p> Optional Arguments: </p>

<ul>
<li> :formula-checks  the name of the formula-checks function created
with def-formula-checks if the meta rule needed one. This will likely be
necessary for most cases. </li>
<li> :returns  return signature of the meta function. By default, it is 'term',
which means that it only returns the rewritten term. Other acceptable forms are
(mv term dont-rw), (mv term dont-rw rp-state), (mv term rp-state) etc. in any
order. </li>
<li> :outside-in  whether the meta rule be applied from outside-in or
inside-out. You can pass t, nil, or :both. If you choose to make it outside-in,
then it is recommended that you input the current dont-rw structure and update
it accordingly. </li>
<li> :valid-syntaxp  if you proved that your meta function returns rp-termp,
then set this to t. Otherwise, RP-Rewriter will have to call rp-termp everytime
the meta runction changes the term. </li>
<li> :disabledp This macro will prove the necessary lemma to make sure that the
meta function can be registered soundly (even though this lemma might be
redundant). If you choose to keep this lemma disabled, then set this to t. It
is, by default, set to t. </li>
<li>:hints regular ACL2 hints passed to the defthm event of the aforementioned
lemma to be proved.</li>
<li> :cl-name-prefix Meta functions are attached to RP-Rewriter using a
defattach mechanism. By default, add-meta-rule will not trigger this mechanism,
and the user needs to call @(see attach-meta-fncs) once all the necessary meta
rules are created and included in the same book. If you wish to call @(see
attach-meta-fncs) autommatically with rp::add-meta-rule, then pass a unique
name for :cl-name-prefix. It is nil by default, which will prevent @(see
attach-meta-fncs) from being executed. </li>
</ul>
"
 )


(defun create-rp-rw-meta-rule-fn-aux1 (all-entries)
  ;; gets unique formula-checks function names
  (if (atom all-entries)
      nil
    (b* ((rest (create-rp-rw-meta-rule-fn-aux1 (cdr all-entries)))
         (formula-check-fnc
          (cond ((weak-meta-rule-table-rec-p (cdr (car all-entries)))
                 (access meta-rule-table-rec
                         (cdr (car all-entries))
                         :formula-checks))
                ((weak-pre-post-processor-table-rec-p
                  (cdr (car all-entries)))
                 (access pre-post-processor-table-rec
                         (cdr (car all-entries))
                         :formula-checks))
                (t nil))))

      (if (or (member-equal formula-check-fnc rest)
              (not formula-check-fnc))
          rest
        (cons formula-check-fnc rest)))))

(defun create-rp-rw-meta-rule-fn-aux2 (rp-rw-all-meta-rules)
  (if (atom rp-rw-all-meta-rules)
      (mv nil `((t (mv term nil rp-state))))
    (b* (((mv added-meta-fnc rest) (create-rp-rw-meta-rule-fn-aux2 (cdr rp-rw-all-meta-rules)))
         (cur (cdar rp-rw-all-meta-rules))
         (meta-fnc (access meta-rule-table-rec cur :meta-fnc))
         ((when (member-equal meta-fnc added-meta-fnc))
          (mv added-meta-fnc rest))
         (valid-syntaxp (access meta-rule-table-rec cur :valid-syntaxp))
         (returns (access meta-rule-table-rec cur :returns))
         (args (access meta-rule-table-rec cur :args))
         (body
          `((eq meta-fnc-name ',meta-fnc)
            (b* (,@(and (not valid-syntaxp)
                        `((input-term term)))
                 (,returns (,meta-fnc . ,args)))
              ,(if valid-syntaxp
                   `(mv term dont-rw rp-state)
                 `(mv (if (rp-termp term) term input-term) dont-rw rp-state))))))
      (mv (cons meta-fnc added-meta-fnc)
          (cons body rest)))))

(defund is-proc-enabled (proc-fnc type state)
  (declare (xargs :guard t
                  :stobjs state))
  (cdr (hons-assoc-equal `(,type ,proc-fnc)
                         (table-alist 'rp-processors (w state)))))

(defun create-rp-rw-processor-fn-aux2 (all-processors type)
  (if (atom all-processors)
      nil
    (b* ((rest (create-rp-rw-processor-fn-aux2 (cdr all-processors) type))
         (cur (cdar all-processors))
         (proc-fnc (access pre-post-processor-table-rec cur :processor-fnc))
         (valid-syntaxp (access pre-post-processor-table-rec cur :valid-syntaxp))
         (args (access pre-post-processor-table-rec cur :args))

         (body
          `(term
            (if (is-proc-enabled ',proc-fnc ',type state)
                ,(if valid-syntaxp
                     `(,proc-fnc . ,args)
                   `(b* ((input-term term)
                         (term (,proc-fnc . ,args)))
                      (if (rp-termp term)
                          term
                        input-term)))
              term)))
         )
      (cons body rest))))

(defun create-rp-rw-meta-rule-fn-aux3 (all-entries)
  (if (atom all-entries)
      nil
    (b* ((cur (cdar all-entries))
         (correctness-lemma
          (cond ((weak-meta-rule-table-rec-p cur)
                 (access meta-rule-table-rec cur :correctness-lemma))
                ((weak-pre-post-processor-table-rec-p cur)
                 (access pre-post-processor-table-rec cur :correctness-lemma))
                (t nil)))
         (rest (create-rp-rw-meta-rule-fn-aux3 (cdr all-entries))))
      (if correctness-lemma
          (cons correctness-lemma rest)
        rest))))



#|
(add-meta-rule :meta-fnc test-meta-fnc
               :trig-fnc foo
               :formula-checks test-formula-checks
               :returns (mv term rp-state dont-rw)
               :outside-in t
               :valid-syntaxp t
               :hints (("Goal"
                        :in-theory (e/d (test-meta-fnc) ()))))||#

;;(create-rp-rw-meta-rule-fn-aux2 (table-alist 'rp-rw-all-meta-rules (w state)))

(defun create-rp-rw-meta-rule-fn (prefix world)
  (b* ((meta-fnc-name (sa prefix 'rp-rw-meta-rule))
       (preprocessor-fnc-name (sa prefix 'rp-rw-preprocessor))
       (postprocessor-fnc-name (sa prefix 'rp-rw-postprocessor))
       (formula-checks-fnc-name (sa prefix 'rp-formula-checks))

       (rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules world))
       (rp-rw-all-preprocessors (table-alist 'rp-rw-all-preprocessors world))
       (rp-rw-all-postprocessors (table-alist 'rp-rw-all-postprocessors world))

       (formula-checks-fns (create-rp-rw-meta-rule-fn-aux1
                            (append rp-rw-all-meta-rules
                                    rp-rw-all-preprocessors
                                    rp-rw-all-postprocessors)))
       (formula-checks-fn-body
        (cons 'and (pairlis$ formula-checks-fns (pairlis$ (repeat (len
                                                                   formula-checks-fns) 'state) nil))))

       ((mv & new-meta-rule-fnc-body)
        (create-rp-rw-meta-rule-fn-aux2 rp-rw-all-meta-rules))

       (new-preprocessor-body
        (create-rp-rw-processor-fn-aux2 rp-rw-all-preprocessors :preprocessor))

       (new-postprocessor-body
        (create-rp-rw-processor-fn-aux2 rp-rw-all-postprocessors :postprocessor))
       #|(meta-rule-validity-lemmas (get-meta-rule-validity-lemma meta-rules))||#
       )
    `(

      (defun ,formula-checks-fnc-name (state)
        (declare (xargs :stobjs (state)))
        ,formula-checks-fn-body)

      (defun ,meta-fnc-name (term meta-fnc-name dont-rw context rp-state state )
        (declare (xargs :guard (rp-termp term)
                        :stobjs (rp-state state)))
        (declare (ignorable term meta-fnc-name dont-rw context rp-state state))
        (cond
         . ,new-meta-rule-fnc-body))

      (defun ,preprocessor-fnc-name (term context rp-state state )
        (declare (xargs :guard (rp-termp term)
                        :stobjs (rp-state state)))
        (declare (ignorable term context rp-state state))
        (b* (
             ,@new-preprocessor-body)
          term))

      (defun ,postprocessor-fnc-name (term context rp-state state )
        (declare (xargs :guard (rp-termp term)
                        :stobjs (rp-state state)))
        (declare (ignorable term context rp-state state))
        (b* (
             ,@new-postprocessor-body)
         term))

      (table rp-rw 'main-formula-checks-fnc-name ',formula-checks-fnc-name)
      (table rp-rw 'meta-rule-caller-fnc-name ',meta-fnc-name)
      (table rp-rw 'preprocessor-caller-fnc-name ',preprocessor-fnc-name)
      (table rp-rw 'postprocessor-caller-fnc-name ',postprocessor-fnc-name)

      (table rp-rw 'added-meta-rules
             ',(table-alist 'rp-rw-all-meta-rules world))
      (table rp-rw 'added-preprocessors
             ',(table-alist 'rp-rw-all-preprocessors world))
      (table rp-rw 'added-postprocessors
             ',(table-alist 'rp-rw-all-postprocessors world))

      (defattach
        (rp-formula-checks ,formula-checks-fnc-name)
        (rp-rw-meta-rule ,meta-fnc-name)
        (rp-rw-preprocessor ,preprocessor-fnc-name)
        (rp-rw-postprocessor ,postprocessor-fnc-name)
        :hints (("Goal"
                 :in-theory '(,formula-checks-fnc-name
                              ,meta-fnc-name
                              ,preprocessor-fnc-name
                              ,postprocessor-fnc-name
                              rp-state-preservedp-of-the-same-rp-state
                              ,@(create-rp-rw-meta-rule-fn-aux3
                                 rp-rw-all-meta-rules)
                              ,@(create-rp-rw-meta-rule-fn-aux3
                                 rp-rw-all-preprocessors)
                              ,@(create-rp-rw-meta-rule-fn-aux3
                                 rp-rw-all-postprocessors)
                              (:e dont-rw-syntaxp))))))))

(defun attach-meta-fncs-fn (prefix state)
  (declare (xargs :stobjs (state)
                  :guard (symbolp prefix)
                  :verify-guards nil))
  `(progn
     ,@(create-rp-rw-meta-rule-fn prefix (w state))))

(defmacro attach-meta-fncs (prefix)
  `(make-event
    (attach-meta-fncs-fn ',prefix state)))

(defun is-rp-clause-processor-up-to-date (world)
  (declare (xargs :guard (and (PLIST-WORLDP world))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (hons-assoc-equal
                                                  acl2::plist-worldp-with-formals)
                                                 ())))))
  (and (b* ( (rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules world))
             (add-meta-rules (cdr (hons-assoc-equal 'added-meta-rules
                                                    (table-alist 'rp-rw world)))))
         (acl2::set-equiv (true-list-fix rp-rw-all-meta-rules)
                          (true-list-fix add-meta-rules)))

       (b* ( (rp-rw-all-preprocessors (table-alist 'rp-rw-all-preprocessors world))
             (added (cdr (hons-assoc-equal 'added-preprocessors
                                           (table-alist 'rp-rw world)))))
         (acl2::set-equiv (true-list-fix rp-rw-all-preprocessors)
                          (true-list-fix added)))

       (b* ( (rp-rw-all-postprocessors (table-alist 'rp-rw-all-postprocessors world))
             (added (cdr (hons-assoc-equal 'added-postprocessors
                                           (table-alist 'rp-rw world)))))
         (acl2::set-equiv (true-list-fix rp-rw-all-postprocessors)
                          (true-list-fix added)))))

(xdoc::defxdoc
 is-rp-clause-processor-up-to-date
 :parents (rp-rewriter/meta-rules)
 :short "Checks if all the added meta-rules are 'registered'"
 :long "<p>
After calling @(see add-meta-rule) or when different books with meta rules are
 included, users need to call @(see rp::attach-meta-fncs). This function
 checks if it is necessary.</p>
<code>(is-rp-clause-processor-up-to-date world)</code>
")

(define check-if-clause-processor-up-to-date (world)
  (declare (xargs :guard (and (PLIST-WORLDP world))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (assoc-equal
                                                  ACL2::PLIST-WORLDP-WITH-FORMALS) ())))))
  (if (is-rp-clause-processor-up-to-date world)
      nil
    (hard-error 'defthmrp
                "The clause processor function is NOT up-to-date with respect ~
to added meta rules. Run (rp::attach-meta-fncs prefix) to create the ~
attach all the meta functions to RP-Rewriter. \"prefix\" should be a unique ~
symbol for the updated meta-rule caller function. ~%"
                nil)))

(progn

  ;; (defwarrant RP-META-FNC)
  ;; (defwarrant RP-META-TRIG-FNC)

  (defwarrant meta-rune-fnc$inline)

  (define disable-meta-rules-fnc (rp-rw-all-meta-rules args)
    :verify-guards nil
    (if (atom args)
        nil
      (b* ((rest (disable-meta-rules-fnc rp-rw-all-meta-rules (cdr args)))
           (cur (loop$ for x in rp-rw-all-meta-rules
                       when (equal (car args)
                                   (meta-rune-fnc (car x)))
                       collect
                       (car x))))
        (if cur
            (cons `(disable-rules
                    ',cur)
                  rest)
          rest))))

  (define enable-meta-rules-fnc (rp-rw-all-meta-rules args)
    :verify-guards nil
    (if (atom args)
        nil
      (b* ((rest (enable-meta-rules-fnc rp-rw-all-meta-rules (cdr args)))
           (cur (loop$ for x in rp-rw-all-meta-rules
                       when (equal (car args)
                                   (meta-rune-fnc (car x)))
                       collect
                       (car x))))
        (if cur
            (cons `(enable-rules
                    ',cur)
                  rest)
          rest))))

  (defmacro disable-all-meta-rules ()
    `(make-event
      (b* ((rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules (w state)))
           (meta-rules (strip-cars rp-rw-all-meta-rules)))
        `(disable-rules ',meta-rules))))

  (defmacro enable-all-meta-rules ()
    `(make-event
      (b* ((rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules (w state)))
           (meta-rules (strip-cars rp-rw-all-meta-rules)))
        `(enable-rules ',meta-rules))))

  (defmacro disable-meta-rules (&rest args)
    (if (not args)
        `(value-triple :none)
      `(make-event
        (b* ((rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules (w state))))
          `(progn
             ,@(disable-meta-rules-fnc rp-rw-all-meta-rules ',args))))))

  (defmacro enable-meta-rules (&rest args)
    (if (not args)
        `(value-triple :none)
      `(make-event
        (b* ((rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules (w state))))
          `(progn
             ,@(enable-meta-rules-fnc rp-rw-all-meta-rules ',args))))))

  (defmacro bump-all-meta-rules ()
    `(make-event
      (b* ((rp-rw-all-meta-rules (table-alist 'rp-rw-all-meta-rules (w state)))
           (meta-rules (strip-cars rp-rw-all-meta-rules)))
        `(bump-rp-rules ,@(reverse meta-rules))))))

(defthm iff-of-rp-evlt-lst
  (iff (rp-evlt-lst subterms a)
       (consp subterms))
  :hints (("goal"
           :induct (len subterms)
           :do-not-induct t
           :in-theory (e/d () ()))))

(defthmd rp-evl-of-ex-from-rp-reverse-for-atom
  (implies (syntaxp (atom x))
           (equal (rp-evl x a)
                  (rp-evl (ex-from-rp x) a)))
  :hints (("Goal"
           :do-not-induct t
           :induct (ex-from-rp x)
           :in-theory (e/d (is-rp) ()))))

(defthmd rp-evlt-of-ex-from-rp-reverse-for-atom
  (implies (syntaxp (atom x))
           (equal (rp-evlt x a)
                  (rp-evlt (ex-from-rp x) a)))
  :hints (("Goal"
           :do-not-induct t
           :induct (ex-from-rp x)
           :in-theory (e/d (is-rp) ()))))

(acl2::def-ruleset
 regular-eval-lemmas
 nil)

(acl2::def-ruleset
 regular-eval-lemmas-with-ex-from-rp
 nil)

(defun create-regular-eval-lemma-fn (fn argc formula-checks)
  `(progn
     (defthmd ,(sa 'regular-rp-evl-of fn 'when formula-checks)
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (,formula-checks state)
                     (case-match x ((',fn . ,(repeat argc '&)) t)))
                (and (equal (rp-evl x a)
                            (,fn . ,(loop$ for i from 1 to argc
                                           collect `(rp-evl (nth ,i x) a))))
                     (equal (rp-evlt x a)
                            (,fn . ,(loop$ for i from 1 to argc
                                           collect `(rp-evlt (nth ,i x)
                                                             a))))))
       :hints (("Goal"
                :in-theory (e/d (rp-trans trans-list) ()))))
     (acl2::add-to-ruleset regular-eval-lemmas '(,(sa 'regular-rp-evl-of fn 'when formula-checks)))
     (defthmd ,(sa 'regular-rp-evl-of fn 'when formula-checks 'with-ex-from-rp)
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (,formula-checks state)
                     (let* ((x (ex-from-rp x))) (case-match x ((',fn . ,(repeat argc '&)) t))))
                (and (equal
                      (rp-evl x a)
                      (,fn . ,(loop$ for i from 1 to argc
                                     collect `(rp-evl (nth ,i (ex-from-rp  x)) a))))
                     (equal
                      (rp-evlt x a)
                      (,fn . ,(loop$ for i from 1 to argc
                                     collect `(rp-evlt (nth ,i (ex-from-rp x)) a))))))
       :hints (("Goal"
                :use ((:instance
                       ,(sa 'regular-rp-evl-of fn 'when formula-checks)
                       (x (ex-from-rp x))))
                :in-theory '(
                             rp-evlt-of-ex-from-rp-reverse-for-atom
                             rp-evl-of-ex-from-rp-reverse-for-atom ))))
     (acl2::add-to-ruleset regular-eval-lemmas
                           '(,(sa 'regular-rp-evl-of fn 'when formula-checks 'with-ex-from-rp)))
     (acl2::add-to-ruleset regular-eval-lemmas-with-ex-from-rp
                           '(,(sa 'regular-rp-evl-of fn 'when formula-checks 'with-ex-from-rp)))))

(defmacro create-regular-eval-lemma (fn argc formula-checks)
  `(make-event
    (create-regular-eval-lemma-fn ',fn ',argc ',formula-checks)))

(xdoc::defxdoc
 rp-rewriter/meta-rules
 :parents (rp-rewriter)
 :short "The steps necessary to add meta rules to RP-Rewriter"
 :long "<p>Below are the steps users need to follow, and information they may
 use:</p>

<p>
1. Create your  meta function.
<code>
@('(define <meta-fnc> (term)
     :returns (mv term dont-rw) OR (term)
     ...)')
</code>
Your meta function can return either two values:term and @(see rp::dont-rw); or
only term. For best performance, it is recommended that you return dont-rw
structure as well. If you do not want the returned term to be rewritten at all,
you can return 't' for dont-rw.
</p>

<p>
2. Create formula-checks function.
<code>
@('(def-formula-checks <formula-check-name>
       (<list-of-function-names>))')
</code>
This event submits a function with signature @('(<formula-check-name> state)'). When
you add this function to your correctness theorem for this meta function, the
evaluator of RP-Rewriter will recognize the functions you list.
</p>

<p>
3. Prove that evaluation of the function returns an equivalent term under the
evaluator.
<code>
@('(defthm rp-evlt-of-meta-fnc
    (implies (and (valid-sc term a) ;;optional
                  (rp-termp term) ;;optional
                  (rp-evl-meta-extract-global-facts)
                  (<formula-check-name> state))
             (equal (rp-evlt (<meta-fnc> term) a)
                    (rp-evlt term a))))')
</code>

This is the correctness theorem of the meta rule. Optionally, you may have
(valid-sc term a), which states that the side-conditions in RP-Rewriter are
correct; and (rp-termp term), which states that some of the syntactic
invariances hold and the term is syntactically compatible with RP-Rewriter. See
discussions for @(see valid-sc) and @(see rp-termp).
</p>

<p>
If the meta function returns dont-rw, then you need to prove the same lemma for
@('(mv-nth 0 (<meta-fnc> term))').
</p>

<p>
4. Prove that meta-function retains the correctness of side-conditions.
<code>
 @('(defthm valid-sc-of-meta-fnc
    (implies (and (valid-sc term a)
                  (rp-termp term) ;;optional
                  (rp-evl-meta-extract-global-facts) ;;optional
                  (<formula-check-name> state)) ;;optional
             (valid-sc (<meta-fnc> term) a)))')
</code>

Meta functions can introduce or change side-conditions by manipulating 'rp'
instances. Therefore users need to prove that the invariance about side
conditions are maintained.
</p>

<p>
If the meta function returns dont-rw, then you need to prove the same lemma for
@('(mv-nth 0 (<meta-fnc> term))').
</p>

<p>
5. Optionally, prove that the meta function returns a valid syntax.
<code>
@('(defthm rp-termp-of-meta-fnc
    (implies (rp-termp term)
             (rp-termp (<meta-fnc> term))))')
</code>

Even though it is optional, it is recommended that you prove such a lemma for
your meta function. It prevents syntactic check on every term returned from
meta function.
</p>
<p>
If the meta function returns dont-rw, then you need to prove the same lemma for
@('(mv-nth 0 (<meta-fnc> term))').
</p>

<p>
6. If your function returns @(see rp::dont-rw), then you also need to prove
that it is syntactically correct. Otherwise skip this step.
<code>
@('(defthm dont-rw-syntaxp-of-meta-fnc
   (dont-rw-syntaxp (mv-nth 1 (<meta-fnc> term))))')
</code>
</p>

<p>
7. Save the meta rule in the rule-set of RP-Rewriter for meta rules.
<code>
@('
(rp::add-meta-rule
 :meta-fnc <meta-fnc>
 :trig-fnc <trig-fnc>
 :returns <return-signature>
 :outside-in <t-if-the-meta-rule-should-apply-from-outside-in>
 :valid-syntaxp <t-if-rp-termp-of-meta-fnc-is-proved>)
')
</code>

See @(see add-meta-rule) for further discussion of the options.

</p>

<p>
8. Attach these newly created meta functions.
<code>
@('(rp::attach-meta-fncs <a-unique-name-for-updated-clause-processor>)')
</code>
If you are going to include this book later when other meta rules for
RP-Rewriter is present, you may want to call this function when all the meta
rules are included.
</p>

<p>
You may look at examples of RP-Rewriter meta rules under
/books/projects/RP-Rewriter/meta/*. implies-meta.lisp is a very simple example
of an outside-in meta rule.
</p>

<p>
Some books under /books/projects/RP-Rewriter/proofs/* might be useful when
proving when proving meta rules correct, especially aux-function-lemmas and
eval-functions-lemmas.
</p>

")

(xdoc::defxdoc
 dont-rw
 :parents (rp-rewriter/meta-rules)
 :short "A special data structure that RP-Rewriter meta rules may return to
 control rewriting of returned terms."
 :long "<p>When a term us returned from a meta rule, it appears as completely
 new to the rewriter and by default, it will be parsed completely and be
 rewritten for a second time. This can cause performance issues with big
 terms. To solve this problem, we use a special structure called dont-rw that
 meta functions may generate and return to control which subterms should be
 rewritten and which should not.</p>

<p>
The dont-rw structure has the same cons skeleton as the term itself such that
it is traversed (car'ed and cdr'ed) the same way as the term. Whenever dont-rw
structure becomes an atom and non-nil, the rewriting of corresponding term
stops. For example, assume that a meta rule returns the following term and we
would like to avoid rewriting all the instances of g, then the following
dont-rw structure would enable that.</p>

<code>
 (f1 (f2 (g a b) c)
     (f3 d (g x y)))
 </code>
 <code>
 (nil (nil t t)
      (nil t t))
</code>")

(xdoc::defxdoc
 attach-meta-fncs
 :parents (rp-rewriter/meta-rules)
 :short "Creates and attaches a new meta-rule caller function to register added meta rules."
 :long "<p>
After calling @(see add-meta-rule) or when different books with meta rules are
 included, users need to call attach-meta-fncs. This creates a
 new meta function caller function and attaches it to rp::rp-rw-meta-rule. </p>
<code>(rp::attach-meta-fncs unique-prefix)</code>
<p> unique-prefix should be a unique name that will be a prefix to the name
 of the new  meta-rule caller function. </p>
")
