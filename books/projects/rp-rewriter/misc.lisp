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

(include-Book "macros")
(include-Book "aux-functions")
(include-Book "std/strings/cat-base" :dir :system)

(encapsulate
  nil

  ;; Parse a rewrite rules and create functions for all the lambda expressions so
  ;; that they open up one at a time.

  (mutual-recursion

   (defun lambda-to-fnc (base-name index keys body)
     (declare (xargs :mode :program))
     (b* ((fnc-name (sa base-name 'lambda-fnc index))
          (signature `((,fnc-name ,@(repeat (len keys) '*)) => *))
          ((mv other-signatures other-fncs other-openers real-body new-index)
           (search-lambda-to-fnc base-name (1+ index) body))
          (opener `((equal (,fnc-name ,@keys)
                           ,real-body)))
          (fnc `((local
                  (defun-nx ,fnc-name ,keys
                    ,real-body)))))
       (mv (append other-signatures (list signature))
           (append other-fncs fnc)
           (append other-openers opener)
           new-index)))

   (defun search-lambda-to-fnc (base-name index term)
     (cond ((or (atom term)
                (eq (car term) 'quote))
            (mv nil nil nil term index))
           ((is-lambda term)
            (b* (((mv sigs fncs openers new-index)
                  (lambda-to-fnc base-name index (cadr (car term)) (caddr (car
                                                                           term))))
                 (fnc-name (sa base-name 'lambda-fnc index)))
              (mv sigs fncs
                  openers
                  `(,fnc-name ,@(cdr term))
                  new-index)))
           (t
            (b* (((mv sigs fncs openers rest new-index)
                  (search-lambda-to-fnc-lst base-name index  (cdr term))))
              (mv sigs fncs openers
                  (cons (car term) rest)
                  new-index)))))

   (defun search-lambda-to-fnc-lst (base-name index lst)
     (if (atom lst)
         (mv nil nil nil lst index)
       (b* (((mv sigs fncs openers first new-index)
             (search-lambda-to-fnc base-name index (car lst)))
            ((mv o-sigs o-fncs o-openers rest new-index)
             (search-lambda-to-fnc-lst base-name new-index (cdr lst))))
         (mv (append sigs o-sigs)
             (append fncs o-fncs)
             (append openers o-openers)
             (cons first rest)
             new-index)))))

  (defun openers-to-rule (base-name openers)
    `(def-rp-rule ,(sa base-name 'lambda-opener)
       (and ,@openers)))

  (defun lambdas-to-other-rules (rule-name rule hints)
    (declare (xargs :mode :program))
    (case-match rule
      (('implies p ('equal a b))
       (b* (((mv p-sigs p-fncs p-openers p-body index)
             (search-lambda-to-fnc rule-name 0 p))
            ((mv b-sigs b-fncs b-openers b-body &)
             (search-lambda-to-fnc rule-name index b)))
         `(encapsulate
            ,(append p-sigs b-sigs)
            ,@(append p-fncs b-fncs)
            ,(openers-to-rule rule-name (append p-openers b-openers))
            (def-rp-rule ,rule-name
              (implies ,p-body
                       (equal ,a ,b-body))
              ,@hints))))
      (('equal a b)
       (b* (((mv b-sigs b-fncs b-openers b-body &)
             (search-lambda-to-fnc rule-name 0 b)))
         `(encapsulate
            ,b-sigs
            ,@(append b-fncs)
            ,(openers-to-rule rule-name b-openers)
            (def-rp-rule ,rule-name
              (equal ,a
                     ,b-body)
              ,@hints))))
      (('implies p b)
       (b* (((mv p-sigs p-fncs p-openers p-body index)
             (search-lambda-to-fnc rule-name 0 p))
            ((mv b-sigs b-fncs b-openers b-body &)
             (search-lambda-to-fnc rule-name index b)))
         `(encapsulate
            ,(append p-sigs b-sigs)
            ,@(append p-fncs b-fncs)
            ,(openers-to-rule rule-name (append p-openers b-openers))
            (def-rp-rule ,rule-name
              (implies ,p-body
                       ,b-body)
              ,@hints))))
      (& `(def-rp-rule ,rule-name
            ,rule
            ,@hints))))

  (defmacro defthm-lambda (rule-name rule &rest hints)
    `(make-event
      (b* (((mv err term & state)
            (acl2::translate1 ',rule t nil nil 'top-level (w state) state))
           (- (if err (hard-error 'defthm-lambda "Error translating term ~%" nil) nil)))
        (mv err
            (lambdas-to-other-rules
             ',rule-name
             term
             ',hints)
            state)))))


(xdoc::defxdoc
 defthm-lambda
 :parents (rp-utilities)
 :short "A useful utility to use rewrite rules that has lambda expression on
 RHS for RP-Rewriter."
 :long "<p>RP-Rewriter does not work with terms that has lambda expressions. Every
 rewrite rule and conjectures are beta-reduced. However, for some cases, doing
 beta-reduction without rewriting subterms first can cause performance issues
 due to repetition.</p>
<p> To mitigate this issue, we use a macro defthm-lambda that can retain the
 functionality of lambda expressions for RHS of rewrite rules. defthm-lambda
 has the same signature as defthm. </p>

")

(encapsulate
  nil

  (defun rw-opener-error-args-string (args cnt)
    (declare (xargs :mode :program))
    (if (atom args)
        ""
      (str::cat
       (symbol-name (car args))
       ": ~p" (str::intstr cnt)
       " ~% "
       (rw-opener-error-args-string (cdr args) (1+ cnt)))))

  (defun rw-opener-error-args-pairs (args cnt)
    (declare (xargs :mode :program))
    (if (atom args)
        nil
      (cons
       (list 'cons (nth cnt acl2::*base-10-chars*)
             (car args))
       (rw-opener-error-args-pairs (cdr args) (1+ cnt)))))

  (mutual-recursion
   (defun pseudo-term-fix (term)
     (cond ((atom term)
            (if (or (acl2-numberp term)
                    (booleanp term)
                    (stringp term))
                (list 'quote term)
              term))
           ((quotep term)
            term)
           (t
            (cons (car term)
                  (pseudo-term-list-fix (cdr term))))))

   (defun pseudo-term-list-fix (lst)
     (if (atom lst)
         nil
       (cons (pseudo-term-fix (car lst))
             (pseudo-term-list-fix (cdr lst))))))

  (defmacro def-rw-opener-error (name term &key
                                      (do-not-print 'nil)
                                      (disabled 'nil)
                                      (message 'nil))
    (b* ((vars-to-print (set-difference$ (acl2::all-vars (pseudo-term-fix term)) do-not-print)))
      `;(progn
;(table rw-opener-error-rules  ',name t)
      (def-rp-rule$ t ,disabled  
       ,name
       (implies (hard-error
                 ',name
                 ,(str::cat 
                   (if message message
                     (str::cat "A " (symbol-name (car term))
                               " instance must have slipped through all of its rewrite rules."))
"To debug, you can try using (rp::update-rp-brr t rp::rp-state) and
(rp::pp-rw-stack :omit '()
                 :evisc-tuple (evisc-tuple 10 12 nil nil)
                 :frames 50). ~%"
                   (rw-opener-error-args-string vars-to-print 0))
                 ,(cons 'list (rw-opener-error-args-pairs vars-to-print 0)))
                (equal
                 ,term
                 t))
       :hints (("Goal"
                ;:expand (hide ,term)
                :in-theory '(return-last hard-error))))))
  
  #|(defmacro disable-opener-error-rule (rule-name)
    `(table 'rw-opener-error-rules ',rule-name nil))||#

  #|(defmacro enable-opener-error-rule (rule-name)
    `(table 'rw-opener-error-rules ',rule-name t))||#)


(xdoc::defxdoc
 def-rw-opener-error
 :short "A macro that causes RP-Rewriter to throw a readable error when a
 certain pattern occurs."
 :long "<p>
 In cases where users want to make sure that a term of a certain pattern
 does not occur, or it is taken care of by a rewrite rule with higher
 priority. </p>
 
<code>
@('(def-rw-opener-error 
  <name> ;; a unique name for the opener error rule
  <pattern> ;; a pattern to match/unify
  ;;optional keys
  :do-not-print (a b c ...)   ;; a list of variables not to print when
                              ;; RP-Rewriter encounters the term and
                              ;; unifies with variables. Default: nil.
  :disabled <t-or-nil>        ;; whether or not opener error rule should be
                              ;; disabled.
  :message \"...\"            ;; A user defined message if user wants to
                              ;; override the original.
  )')
</code>

<p> A def-rw-opener-error event will submit a disabled rewrite rule with
defthm, but it will be enabled in RP-Rewriter's rule-set by default. Such rules
might be useful if you are using some rewrite rules with hypotheses and want to
make sure that hypotheses are relieved, otherwise this rule will be used and
RP-Rewriter will throw an eligible error.</p>"

 :parents (rp-utilities))


(defun translate1-vals-in-alist (alist state)
  (declare (xargs :guard (alistp alist)
                  :stobjs (state)
                  :mode :program ))
  (if (atom alist)
      (mv nil state)
    (b* ((c (cdar alist))
         ((mv err c & state)
          (acl2::translate1 c t nil nil 'top-level (w state) state))
         (- (if err
                (hard-error 'translate1-vals-in-alist
                            "Error translating term ~p0~%"
                            (list (cons #\0 c)))
              nil))
         ((mv rest state)
          (translate1-vals-in-alist (cdr alist) state)))
      (mv (acons (caar alist) c rest)
          state))))

(defmacro rp-thm (term &key
                       (untranslate 't)
                       #|(disable-opener-error 'nil)||#
                       (new-synps 'nil)
                       (disable-meta-rules 'nil)
                       (enable-meta-rules 'nil)
                       (enable-rules 'nil)
                       (disable-rules 'nil)
                       (runes 'nil)
                       (not-simplified-action ':warning))
  `(encapsulate
     nil

     ,@(if enable-meta-rules
           `((local
              (enable-meta-rules ,@enable-meta-rules)))
         'nil)

     ,@(if disable-meta-rules
           `((local
              (disable-meta-rules ,@disable-meta-rules)))
         'nil)

     ,@(if enable-rules
           `((local
              (enable-rules ,enable-rules)))
         'nil)

     ,@(if disable-rules
           `((local
              (disable-rules ,disable-rules)))
         'nil)

     (make-event
      (b* ((- (check-if-clause-processor-up-to-date (w state)))
           ((mv err term & state)
            (acl2::translate1 ',term t nil nil 'top-level (w state) state))
           (- (if err (hard-error 'rp-thm "Error translating term ~%" nil) nil))
           (term (beta-search-reduce term 1000))
           ((mv runes exc-rules)
            ,(if runes
                 `(mv ,runes (get-disabled-exc-rules-from-table (table-alist 'rp-exc-rules world)))
               '(get-enabled-rules-from-table state)))
           ((mv new-synps state) (translate1-vals-in-alist ,new-synps state))
           (rules-alist (get-rules runes state :new-synps new-synps))
           (rp-state (rp-state-new-run rp-state))
           (old-not-simplified-action (not-simplified-action rp-state))
           (rp-state (update-not-simplified-action ,not-simplified-action rp-state))
           (meta-rules  (make-fast-alist (cdr (assoc-equal 'meta-rules-list (table-alist
                                                                             'rp-rw (w state))))))

           ((mv rw rp-state)
            (time$
             (rp-rw-aux term
                        rules-alist
                        exc-rules
                        meta-rules
                        rp-state
                        state)))
           (rw (if ,untranslate (untranslate rw t (w state)) rw))
           (- (fast-alist-free meta-rules))
           (state (fms "~p0~%"
                       (list
                        (cons #\0 rw))
                       *standard-co* state (evisc-tuple 8 10 nil nil)))
           (rp-state (update-not-simplified-action old-not-simplified-action rp-state)))
        (mv nil `(value-triple :none) state rp-state)))))

(defmacro rp-cl (&key (new-synps 'nil)
                      (cl-name-prefix '0)
                      (runes 'nil))
  `(,(sa (if (equal cl-name-prefix 0) nil cl-name-prefix) "RP-CLAUSE-PROCESSOR")
    clause
    (make rp-cl-hints
          :runes ',runes #|,(if rules-override
          rules-override
          `(append (let ((world (w state))) (current-theory :here))
          ,extra-rules)
          )||#
          :new-synps ,new-synps)
    rp-state state))

(defmacro def-rp-thm (name term
                           &key
                           (rule-classes ':rewrite)
                           ;; (use-opener-error-rules 't)
                           (new-synps 'nil)
                           (disable-meta-rules 'nil)
                           (enable-meta-rules 'nil)
                           (enable-rules 'nil)
                           (disable-rules 'nil)
                           (runes 'nil) ;; when nil, runes will be read from
                           ;; rp-rules table
                           )
  `(make-event
    (b* ((- (check-if-clause-processor-up-to-date (w state)))
         (cl-name-prefix (cdr (assoc-eq 'cl-name-prefix (table-alist 'rp-rw (w state)))))
         (body `(def-rp-rule ,',name ,',term
                  :rule-classes ,',rule-classes
                  :hints (("Goal"
                           :do-not-induct t
                           :rw-cache-state nil
                           :do-not '(preprocess generalize fertilize)
                           :clause-processor
                           (rp-cl :runes ,,runes
                                  :cl-name-prefix ,cl-name-prefix
                                  :new-synps ,',new-synps))))))
      ,(if (or disable-meta-rules
               enable-meta-rules
               enable-rules
               disable-rules)
           ``(encapsulate
               nil
               ;; ,@(if ,use-opener-error-rules
               ;;       `((local
               ;;          (in-theory (enable . ,opener-error-rules))))
               ;;     'nil)

               ,@(if ',enable-meta-rules
                     `((local
                        (enable-meta-rules ,@',enable-meta-rules)))
                   'nil)

               ,@(if ',disable-meta-rules
                     `((local
                        (disable-meta-rules ,@',disable-meta-rules)))
                   'nil)

               ,@(if ',enable-rules
                     `((local
                        (enable-rules ,',enable-rules)))
                   'nil)

               ,@(if ',disable-rules
                     `((local
                        (disable-rules ,',disable-rules)))
                   'nil)
               ,body)
         `body))))

(defmacro defthmrp (&rest rest)
  `(def-rp-thm ,@rest))


(xdoc::defxdoc
 def-rp-thm
 :short "Same as @(see rp::defthmrp)")

(xdoc::defxdoc
 defthmrp
 :short "A defthm macro that calls RP-Rewriter as a clause processor with some
 capabilities."
 :parents (rp-utilities rp-rewriter)
 :long "<p>RP::Defthmrp is a macro that calls defthm with RP-Rewriter as a
 clause-processor. It may also take some of the following parameters:

<code>
@('
 (rp::defthmrp
  <new-rule-name>
  <conjecture>
  ;; optional keys:
  :rule-classes <...>   ;; default: :rewrite
  :new-synps <...>      ;; for advanced users; can attach syntaxp to some existing
                        ;; rewrite rules. Default: nil
  :enable-meta-rules (meta-fnc1 meta-fnc2 ...) ;; an unquoted list of names
                                               ;; of meta functions that users
                                               ;; wants to enable.  
  :disable-meta-rules (meta-fnc1 meta-fnc2 ...) ;; same as above 
  :enable-rules (append '(rule1 rule2)
                        *rules3*
                        ...) ;; List of rule-names that users wants enabled in
      ;; RP-Rewriter's rule-set. The macro will execute the expressions first to
      ;; generate the names.
  :disable-rules <...>      ;; Same as above
  :runes '(rule1 rule2 ...) ;; When nil, the macro uses the existing rule-set of
      ;; RP-rewriter. Otherwise, it will overrride everything else regarding rules
      ;; and use only the rules given in this list. 
  )
')
</code>
</p>
"
 )
      


(encapsulate
  nil

  (defun fetch-new-events-step1 (event)
    `(make-event
      (b* ((?current-theory (let ((world (w state))) (current-theory :here))))
        `(progn ,',event

                (table fetch-new-events 'a ',current-theory)))))

  (defun fetch-new-events-step2 (macro-name)
    `(make-event
      (b* ((new-current-theory (let ((world (w state))) (current-theory :here)))
           (old-current-theory (cdr (assoc-equal 'a (table-alist
                                                     'fetch-new-events
                                                     (w state)))))
           (- (cw "Scanning for newly added event ..."))
           (added-events (set-difference$ new-current-theory
                                          old-current-theory
                                          :test 'equal))
           (- (cw "Scanning for disabled events ..."))
           (removed-events (set-difference$ old-current-theory
                                            new-current-theory
                                            :test 'equal)))
        (if (and (not removed-events)
                 (not added-events))
            `(value-triple (cw "~%Event did not change current theory, not ~
    creating macro ~p0. ~%" ',',macro-name))
          `(defmacro ,',macro-name (use)
             (if use
                 `(in-theory (e/d ,',added-events
                                  ,',removed-events))
               `(in-theory (e/d ,',removed-events
                                ,',added-events))))))))

  (defmacro fetch-new-events (event macro-name &key (disabled 'nil) )
    `(with-output
       :off (warning event  prove  observation)
       :gag-mode :goals
       (progn
         ,(fetch-new-events-step1 event)
         ,(fetch-new-events-step2 macro-name)
         ,@(if disabled
               `((,macro-name nil))
             nil)))))


(xdoc::defxdoc
 fetch-new-events
 :short "A macro that detects the changes in the theory when a book is
 included, and creates a macro to enable users to enable and disable the new events."
 :parents (rp-utilities)
 :long "<p>Gives users the ability to undo and redo the changes an event, such
 as include-book, makes to current theory.

<code>
@('
 (fetch-new-events 
  <event>               ;; e.g., (include-book \"arithmetic-5\" :dir :system)
  <macro-name>          ;; e.g., use-aritmetic-5 
  ;;optional key
  :disabled <disabled> ;; When non-nil, the event does not change the current
  theory. Default: nil.
  )
')
</code>
</p>

<p>
After including the arithmetic library as given below, users can enable and
disable the library as given.

<code>
@('
 (fetch-new-events 
  (include-book \"arithmetic-5\" :dir :system)
  use-aritmetic-5)
')
</code>

<code>
(use-aritmetic-5 t)
</code>

<code>
(use-aritmetic-5 nil)
</code>

</p>

<p>
Note that when current theory contains many events, this utility may work very
slowly. If you do not wish to generate a macro, you may also use @(see
rp::preserve-current-theory). This utility will work with current theory of any size.
</p>
"
 )


(encapsulate
  nil

  (defun preserve-current-theory-step1 (event)
    `(make-event
      (b* ((?current-theory (let ((world (w state))) (current-theory :here))))
        `(progn ,',event
                (table preserve-current-theory 'a ',current-theory)))))

  (defun preserve-current-theory-step2 ()
    `(make-event
      (b* ((old-current-theory (cdr (assoc-equal 'a (table-alist
                                                     'preserve-current-theory
                                                     (w state))))))
        `(in-theory ',old-current-theory))))

  (defmacro preserve-current-theory (event)
    `(with-output
       :off (warning event  prove  observation)
       :gag-mode :goals
       (progn
         ,(preserve-current-theory-step1 event)
         ,(preserve-current-theory-step2)))))


(xdoc::defxdoc
 preserve-current-theory
 :short "A macro that detects the changes in the theory when a book is
 included, and retains the current theory"
 :parents (rp-utilities)
 :long "See @(see rp::fetch-new-events)"
 )
