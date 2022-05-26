; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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
(include-Book "extract-formula")
(include-Book "proofs/guards")

(local
 (include-Book "proofs/extract-formula-lemmas"))

(local
 (include-Book "proofs/rp-state-functions-lemmas"))


(defund pull-keys-from-rest-args (rest-args keys)
  (if (or (atom rest-args)
          (atom (cdr rest-args)))
      (mv nil rest-args)
    (b* (((mv rest-pulled rest-rest)
          (pull-keys-from-rest-args (cdr rest-args) keys)))
      (if (member-equal (car rest-args) keys)
          (mv (acons (car rest-args)
                     (cadr rest-args)
                     rest-pulled)
              (cdr rest-rest))
        (mv rest-pulled (cons-with-hint (car rest-args) rest-rest rest-args))))))

(encapsulate
  nil

  ;; Parse a rewrite rules and create functions for all the lambda expressions so
  ;; that they open up one at a time.

  (mutual-recursion

   (defun lambda-to-fnc (base-name index keys body)
     (declare (xargs :mode :program))
     (b* ((fnc-name (sa base-name 'lambda-fnc index))
          (signature `((,fnc-name ,@(repeat (len keys) '*)) => *))
          ((mv other-signatures other-fncs other-fnc-names other-openers real-body new-index)
           (search-lambda-to-fnc base-name (1+ index) body))
          (opener `((equal (,fnc-name ,@keys)
                           ,real-body)))
          (fnc `((local
                  (defun-nx ,fnc-name ,keys
                    ,real-body))
                 (disable-exc-counterpart ,fnc-name)
                 (local
                  (add-rp-rule ,fnc-name)))))
       (mv (append other-signatures (list signature))
           (append other-fncs fnc)
           (cons `(,fnc-name ,@keys) other-fnc-names)
           (append other-openers opener)
           new-index)))

   (defun search-lambda-to-fnc (base-name index term)
     (cond ((or (atom term)
                (eq (car term) 'quote))
            (mv nil nil nil nil term index))
           ((is-lambda term)
            (b* (((mv sigs fncs fnc-names openers new-index)
                  (lambda-to-fnc base-name index (cadr (car term)) (caddr (car
                                                                           term))))
                 (fnc-name (sa base-name 'lambda-fnc index)))
              (mv sigs fncs
                  fnc-names
                  openers
                  `(,fnc-name ,@(cdr term))
                  new-index)))
           (t
            (b* (((mv sigs fncs fnc-names openers rest new-index)
                  (search-lambda-to-fnc-lst base-name index  (cdr term))))
              (mv sigs fncs fnc-names openers
                  (cons (car term) rest)
                  new-index)))))

   (defun search-lambda-to-fnc-lst (base-name index lst)
     (if (atom lst)
         (mv nil nil nil nil lst index)
       (b* (((mv sigs fncs fnc-names openers first new-index)
             (search-lambda-to-fnc base-name index (car lst)))
            ((mv o-sigs o-fncs o-fnc-names o-openers rest new-index)
             (search-lambda-to-fnc-lst base-name new-index (cdr lst))))
         (mv (append sigs o-sigs)
             (append fncs o-fncs)
             (append fnc-names o-fnc-names)
             (append openers o-openers)
             (cons first rest)
             new-index)))))

  (defun openers-to-rule (base-name openers)
    `(def-rp-rule ,(sa base-name 'lambda-opener)
       (and ,@openers)))

  (defun lambdas-to-other-rules (rule-name rule untranslated-rule
                                           from-add-rp-rule hints)
    (declare (xargs :mode :program))
    (b* (((mv hyp lhs rhs iff)
          (case-match rule
            (('implies hyp ('equal lhs rhs))
             (mv hyp lhs rhs nil))
            (('implies hyp ('iff lhs rhs))
             (mv hyp lhs rhs t))
            (('implies hyp lhs)
             (mv hyp lhs ''t t))
            (('equal lhs rhs)
             (mv ''t lhs rhs nil))
            (('iff lhs rhs)
             (mv ''t lhs rhs t))
            (&
             (mv ''t rule ''t t))))
         ((mv hyp-sigs hyp-fncs hyp-fnc-names hyp-openers hyp-body index)
          (search-lambda-to-fnc rule-name 0 hyp))
         ((mv rhs-sigs rhs-fncs rhs-fnc-names rhs-openers rhs-body index)
          (search-lambda-to-fnc rule-name index rhs))
         ((mv lhs-sigs lhs-fncs lhs-fnc-names lhs-openers lhs-body ?index)
          (search-lambda-to-fnc rule-name index lhs))
         (sigs (append hyp-sigs rhs-sigs lhs-sigs))
         (fncs (append hyp-fncs rhs-fncs lhs-fncs))
         (fnc-names (append hyp-fnc-names rhs-fnc-names lhs-fnc-names))
         (openers (append hyp-openers rhs-openers lhs-openers))

         (rule-name-for-rp (intern$ (str::cat (symbol-name rule-name)
                                              "-FOR-RP")
                                    (symbol-package-name rule-name))))
      (if (or (and sigs fncs openers)
              (and (or sigs fncs openers)
                   (hard-error
                    'lambdas-to-other-rules
                    "something unexpected happened.... contact Mertcan Temel<temelmertcan@gmail.com>~%"
                    nil)))
          `(encapsulate
               ,sigs
               ,@fncs
             (local
              (defthmd opener-lemmas
                  (and ,@(loop$ for x in openers collect
                               `(equal ,x t)))
                :hints (("Goal"
                         :expand ,fnc-names
                         :in-theory  (union-theories (theory 'acl2::minimal-theory)
                                                     '(hard-error
                                                       hons-acons
                                                       hons-copy
                                                       make-fast-alist
                                                       fmt-to-comment-window
                                                       return-last)
                                                     ))
                        (AND STABLE-UNDER-SIMPLIFICATIONP
                             '(:IN-THEORY (e/d () ()))))))
             (local
              (rp::add-rp-rule opener-lemmas :outside-in t))

             (with-output
               :stack :pop
               :on (acl2::summary acl2::event)
               :summary-off (:other-than acl2::time acl2::rules)
               (defthmd ,rule-name-for-rp
                 (and (implies ,hyp-body
                               (,(if iff `iff `equal)
                                ,lhs-body
                                ,rhs-body))
                      ,@openers)
                 ,@hints))
             
             
             ,@(if from-add-rp-rule
                   nil
                 `((defthm ,rule-name
                     ,rule
                     :hints (("Goal"
                              :use ((:instance ,rule-name-for-rp))
                              :in-theory '(,rule-name-for-rp))))))

             (add-rp-rule ,rule-name
                          :beta-reduce nil)
             (table corresponding-rp-rule ',rule-name ',rule-name-for-rp)
             #|(acl2::extend-pe-table ,rule-name-for-rp
                                    (def-rp-rule ,rule-name-for-rp
                                      ,body
                                      :hints ,',hints))|#)
        `(progn
           (with-output
             :stack :pop
             :on (acl2::summary acl2::event)
             :summary-off (:other-than acl2::time acl2::rules)
             (defthm ,rule-name
               ,untranslated-rule
               ,@hints))
           (add-rp-rule ,rule-name
                        :beta-reduce nil)))))

  ;; (case-match rule
  ;;   (('implies p ('equal a b))
  ;;    (b* (((mv p-sigs p-fncs p-openers p-body index)
  ;;          (search-lambda-to-fnc rule-name 0 p))
  ;;         ((mv b-sigs b-fncs b-openers b-body &)
  ;;          (search-lambda-to-fnc rule-name index b)))
  ;;      `(encapsulate
  ;;         ,(append p-sigs b-sigs)
  ;;         ,@(append p-fncs b-fncs)
  ;;         ,(openers-to-rule rule-name (append p-openers b-openers))
  ;;         (defthm ,rule-name
  ;;           (implies ,p-body
  ;;                    (equal ,a ,b-body))
  ;;           ,@hints)
  ;;         (add-rp-rule ,rule-name))))
  ;;   (('equal a b)
  ;;    (b* (((mv b-sigs b-fncs b-openers b-body &)
  ;;          (search-lambda-to-fnc rule-name 0 b)))
  ;;      `(encapsulate
  ;;         ,b-sigs
  ;;         ,@(append b-fncs)
  ;;         ,(openers-to-rule rule-name b-openers)
  ;;         (defthm ,rule-name
  ;;           (equal ,a
  ;;                  ,b-body)
  ;;           ,@hints)
  ;;         (add-rp-rule ,rule-name))))
  ;;   (('implies p b)
  ;;    (b* (((mv p-sigs p-fncs p-openers p-body index)
  ;;          (search-lambda-to-fnc rule-name 0 p))
  ;;         ((mv b-sigs b-fncs b-openers b-body &)
  ;;          (search-lambda-to-fnc rule-name index b)))
  ;;      `(encapsulate
  ;;         ,(append p-sigs b-sigs)
  ;;         ,@(append p-fncs b-fncs)
  ;;         ,(openers-to-rule rule-name (append p-openers b-openers))
  ;;         (defthm ,rule-name
  ;;           (implies ,p-body
  ;;                    ,b-body)
  ;;           ,@hints)
  ;;         (add-rp-rule ,rule-name))))
  ;;   (& `(def-rp-rule ,rule-name
  ;;         ,rule
  ;;         ,@hints))))

  (defmacro defthm-lambda (rule-name rule &rest rest)
    `(make-event
      (b* (((mv err term & state)
            (acl2::translate1 ',rule t nil nil 'top-level (w state) state))

           ((mv pulled-entries rest)
            (pull-keys-from-rest-args ',rest '(:from-add-rp-rule)))
           
           (- (if err (hard-error 'defthm-lambda "Error translating term ~%" nil) nil)))
        (mv err
            (lambdas-to-other-rules
             ',rule-name
             term
             ',rule
             (cdr (hons-assoc-equal :from-add-rp-rule pulled-entries))
             rest)
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
 functionality of lambda expressions rewrite rules. defthm-lambda
 has the same signature as defthm. </p>

<p> Below is an example defthm-lambda event and what it translates to:</p>
<code>
@('(defthm-lambda foo-redef
    (implies (p x)
             (equal (foo x)
                    (let* ((a (f1 x))
                           (b (f2 x)))
                      (f4 a a b)))))

  ;; The above event is translated into this:
  (encapsulate
    (((foo-redef_lambda-fnc_1 * *) => *)
     ((foo-redef_lambda-fnc_0 * *) => *))
    (local (defun-nx foo-redef_lambda-fnc_1 (b a)
             (f4 a a b)))
    (local (defun-nx foo-redef_lambda-fnc_0 (a x)
             (foo-redef_lambda-fnc_1 (f2 x) a)))
    (def-rp-rule foo-redef_lambda-opener
      (and (equal (foo-redef_lambda-fnc_1 b a)
                  (f4 a a b))
           (equal (foo-redef_lambda-fnc_0 a x)
                  (foo-redef_lambda-fnc_1 (f2 x) a))))
    (def-rp-rule foo-redef
      (implies (p x)
               (equal (foo x)
                      (foo-redef_lambda-fnc_0 (f1 x) x)))))
')
</code>
")

(progn
  (mutual-recursion
   (defund contains-lambda-expression (body)
     (declare (xargs :guard t))
     (cond ((atom body) nil)
           ((quotep body) nil)
           ((is-lambda body) t)
           (t (contains-lambda-expression-lst (cdr body)))))
   (defund contains-lambda-expression-lst (lst)
     (and (consp lst)
          (or (contains-lambda-expression (car lst))
              (contains-lambda-expression-lst (cdr lst))))))

  (defmacro bump-rule (rule-name/rune)
    `(with-output
       :off :all
       :gag-mode nil
       (make-event
        (b* ((rule-name/rune ',rule-name/rune)
             (rune (case-match rule-name/rune
                     ((& . &) rule-name/rune)
                     (& (get-rune-name rule-name/rune state))))
             (entry (hons-assoc-equal rune (table-alist
                                            'rp-rules (w state))))
             (- (and (not (consp entry))
                     (hard-error 'bump-rule
                                 "This rule is not added with add-rp-rule There is
nothing to bump!" nil)))
             ;;(cur-table (table-alist 'rp-rules (w state)))
             ;;(cur-table (remove-assoc-equal rune cur-table))
             )
          `(progn
             (table rp-rules nil (remove-assoc-equal ',rune (table-alist 'rp-rules acl2::world)) :clear)
             ;;(table rp-rules nil ',cur-table :clear)
             (table rp-rules ',rune ',(cdr entry))
             )))))

  (defmacro bump-down-rule (rule-name/rune &key (ruleset 'rp-rules))
    `(with-output
       :off :all
       :gag-mode nil
       (make-event
        (b* ((rule-name/rune ',rule-name/rune)
             (rune (case-match rule-name/rune
                     ((& . &) rule-name/rune)
                     (& (get-rune-name rule-name/rune state))))
             (entry (hons-assoc-equal rune (table-alist
                                            ',ruleset (w state))))
             (- (and (not (consp entry))
                     (hard-error 'bump-rule
                                 "This rule is not added with add-rp-rule There is
nothing to bump!" nil)))
             ;; (cur-table (table-alist 'rp-rules (w state)))
             ;; (cur-table (remove-assoc-equal rune cur-table))
             ;; (cur-table (append cur-table (list entry)))
             )
          `(progn
             (table ,',ruleset nil (append (remove-assoc-equal ',rune (table-alist ',',ruleset acl2::world))
                                         (list ',entry))
                    :clear)
             ;;(table rp-rules ',rune ',(cdr entry))
             )))))

  (defun bump-rules-body (args)
    (if (atom args)
        nil
      (cons `(bump-rule ,(car args))
            (bump-rules-body (cdr args)))))

  (defmacro bump-rules (&rest args)
    `(progn
       . ,(bump-rules-body args)))

  (defmacro add-rp-rule (rule-name &key
                                   (disabled 'nil)
                                   (beta-reduce 'nil)
                                   (hints 'nil)
                                   (outside-in 'nil)
                                   (ruleset 'rp-rules))

    (b* ((rw-direction
          (cond ((or (equal outside-in ':inside-out)
                     (equal outside-in ':both))
                 :both)
                ((equal outside-in t)
                 :outside-in)
                ((equal outside-in nil)
                 :inside-out)
                (t (hard-error 'add-rp-rule
                               ":outside-in can only be :inside-out, t, or nil but we are given: ~p0 ~%"
                               (list (cons #\0 outside-in)))))))
      `(make-event
        (b* ((body (and ,beta-reduce
                        (meta-extract-formula ',rule-name state)))
             (beta-reduce (and ,beta-reduce
                               (contains-lambda-expression body)))
             (rule-name ',rule-name)
             (new-rule-name (if beta-reduce
                                (intern$ (str::cat (symbol-name ',rule-name)
                                                   "-FOR-RP")
                                         (symbol-package-name ',rule-name))
                              ',rule-name))
             (rest-body
              `(with-output
                 :off :all
                 :gag-mode nil :on error
                 (make-event
                  (b* ((rune (get-rune-name ',new-rule-name state))
                       (disabled ,,disabled)
                       (- (get-rules `(,rune) state :warning :err)))
                    `(progn
                       (table ,',',ruleset
                              ',rune
                              (cons ,,',rw-direction
                                    ,(not disabled)))))))))
          (if beta-reduce
              `(progn
                 (defthm-lambda ,rule-name
                   ,body
                   :from-add-rp-rule t
                   :hints ,',hints)
                 (with-output :off :all :gag-mode nil :on error
                   (progn
                     ;;(in-theory (disable ,new-rule-name))
                     (value-triple (cw "This rule has a lambda expression, ~
and it is automatically put through rp::defthm-lambda  and a ~
new rule is created to be used by RP-Rewriter. You can disable this by setting ~
:beta-reduce to nil ~% The name of this rule is: ~p0 ~%" ',new-rule-name))
                     (value-triple ',new-rule-name))))
            rest-body)))))

  (defun def-rp-rule-fn (rule-name rule hints)
    `(progn
       (defthm-lambda ,rule-name ,rule ,@hints)
       #|(acl2::extend-pe-table ,rule-name
                              (def-rp-rule ,rule-name ,rule ,@hints))|#
       (value-triple ',rule-name)))

  (defmacro def-rp-rule (rule-name rule &rest hints)
    `(with-output
       :off :all
       :on (error)
       :stack :push
       ,(def-rp-rule-fn rule-name rule hints)))

  (defmacro def-rp-rule$ (defthmd disabled rule-name rule  &rest hints)
    `(progn
       (,(if defthmd 'defthmd 'defthm)
        ,rule-name ,rule ,@hints)
       (with-output :off :all :gag-mode nil :on error
         (add-rp-rule  ,rule-name :disabled ,disabled
                       :beta-reduce nil)))))

(encapsulate
  nil

  (defun rw-opener-error-args-string (args cnt)
    (declare (xargs :mode :program))
    (if (atom args)
        ""
      (str::cat
       (symbol-name (car args))
       ": ~p" (str::int-to-dec-string cnt)
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

(define rp-thm-rw-fn ((term rp-termp) runes
                      runes-outside-in
                      (new-synps alistp)
                      rp-state state)
  (b* ((rp-state (rp-state-new-run rp-state))
       (rp-state (rp-state-init-rules runes runes-outside-in new-synps rp-state state))
       ((mv term rp-state)
        (preprocess-then-rp-rw term rp-state state)))
    (mv term rp-state)))

(defmacro rp-thm (term &key
                       (untranslate 't)
                       #|(disable-opener-error 'nil)||#
                       (new-synps 'nil)
                       (disable-meta-rules 'nil)
                       (enable-meta-rules 'nil)
                       (enable-rules 'nil)
                       (disable-rules 'nil)
                       (runes 'nil)
                       (runes-outside-in 'nil)
                       (time 't)
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
           (term (beta-search-reduce term 10000))
           ((mv new-synps state) (translate1-vals-in-alist ,new-synps state))
           (old-not-simplified-action (not-simplified-action rp-state))
           (rp-state (update-not-simplified-action ,not-simplified-action rp-state))
           ((mv rw rp-state)
            (if ,time
                (time$
                 (rp-thm-rw-fn term ',runes ',runes-outside-in new-synps rp-state state))
              (rp-thm-rw-fn term ',runes ',runes-outside-in new-synps rp-state state)))
           (rw (if ,untranslate (untranslate rw t (w state)) rw))
           (state (fms "~p0~%"
                       (list
                        (cons #\0 rw))
                       *standard-co* state (evisc-tuple 8 10 nil nil)))
           (rp-state (update-not-simplified-action old-not-simplified-action rp-state)))
        (mv nil `(value-triple :none) state rp-state)))))

(defmacro rp-cl (&key (new-synps 'nil)
                      (runes 'nil)
                      (runes-outside-in 'nil)
                      (cases 'nil)) ;
  `(rp-rewriter
    clause
    (make rp-cl-hints
          :cases ,cases
          :runes-outside-in ',runes-outside-in
          :runes ',runes #|,(if rules-override
          rules-override
          `(append (let ((world (w state))) (current-theory :here))
          ,extra-rules)
          )||#
          :new-synps ,new-synps)
    rp-state state))

(defun untranslate-lst (lst iff-flg world)
  (declare (xargs :mode :program))
  (if (atom lst)
      nil
    (cons (untranslate (car lst) iff-flg world)
          (untranslate-lst (cdr lst) iff-flg world))))


(defmacro def-rp-thm (name term
                           &key
                           (rule-classes ':rewrite)
                           ;; (use-opener-error-rules 't)
                           (new-synps 'nil)
                           (disable-meta-rules 'nil)
                           (enable-meta-rules 'nil)
                           (enable-rules 'nil)
                           (disable-rules 'nil)
                           (runes 'nil)
                           (runes-outside-in 'nil);; when nil, runes will be read from
                           ;; rp-rules table
                           (cases 'nil)
                           )
  `(make-event
    (b* ((world (w state))
         (- (check-if-clause-processor-up-to-date world))
         (cases ',cases #|(untranslate-lst ',cases t world)|#)
         (body `(with-output
                  :stack :pop
                  :on (acl2::summary acl2::event acl2::error)
                  :gag-mode :goals
                  :summary-off (:other-than acl2::time acl2::rules)
                  (def-rp-rule ,',name ,',term
                    :rule-classes ,',rule-classes
                    :hints (("goal"
                             :do-not-induct t
                             :rw-cache-state nil
                             :do-not '(preprocess generalize fertilize)
                             :clause-processor
                             (rp-cl :runes ,,runes
                                    :runes-outside-in ,,runes-outside-in
                                    :new-synps ,',new-synps
                                    :cases ',cases)))))))
      ,(if (or disable-meta-rules
               enable-meta-rules
               enable-rules
               disable-rules)
           ``(with-output
               :off :all
               :stack :push
               (encapsulate
                 nil
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
                 ,body))
         `body))))

(defmacro defthmrp (&rest rest)
  `(def-rp-thm ,@rest))

(xdoc::defxdoc
 def-rp-thm
 :parents (rp-other-utilities)
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


(xdoc::defxdoc
 rp-other-utilities
 :short "Some names that are aliases to other tools"
 :parents (rp-utilities)
 )
