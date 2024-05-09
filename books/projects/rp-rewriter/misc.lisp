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
(include-book "centaur/meta/let-abs" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(local
 (include-Book "proofs/extract-formula-lemmas"))

(local
 (include-Book "proofs/rp-state-functions-lemmas"))

(defsection defwarrant-rp
  :parents (rp-utilities)
  :short "Calls defwarrant and register the resulting rule with RP, and disbled executable counterpart for the warrant"
  (defmacro defwarrant-rp (fn)
    `(make-event
      (b* ((fn ',fn))
        (acl2::template-subst
         `(progn
            (defwarrant <fn>)
            (rp::disable-rules
             '((:e apply$-warrant-<fn>)))
            (rp::add-rp-rule apply$-<fn>))
         :atom-alist `((<fn> . ,fn))
         :str-alist `(("<FN>" . ,(symbol-name fn)))
         :pkg-sym fn)))))

(progn
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
          (mv rest-pulled (cons-with-hint (car rest-args) rest-rest
                                          rest-args))))))
  (defund pull-name-and-body-from-args (args)
    (if (or (atom args)
            (atom (cdr args)))
        (mv nil nil args)
      (b* (((mv rule-name body rest-args)
            (pull-name-and-body-from-args (cddr args)))
           ((when (and rule-name body))
            (mv rule-name body (append (take 2 args) rest-args)))
           (cur (car args))
           (cur-2 (cadr args)))
        (if (not (keywordp cur))
            (mv cur cur-2 (cddr args))
          (mv nil nil args))))))

(defun untranslate-lst (lst iff-flg world)
  (declare (xargs :mode :program))
  (if (atom lst)
      nil
    (cons (untranslate (car lst) iff-flg world)
          (untranslate-lst (cdr lst) iff-flg world))))

(progn
  (define hidden-constant (x)
    x)
  (define hide/unhide-constants-for-translate (hide term)
    :mode :program
    (cond ((atom term)
           (if (and hide
                    (symbolp term)
                    (b* ((chars (explode (symbol-name term))))
                      (and (> (len chars) 2)
                           (equal (first chars) #\*)
                           (equal (last chars) '(#\*)))))
               `(hidden-constant ',term)
             term))
          ((quotep term)
           term)
          ((and (not hide)
                (case-match term (('hidden-constant ('quote &)) t)))
           (cadr (cadr term)))
          (t (cons (hide/unhide-constants-for-translate hide (car term))
                   (hide/unhide-constants-for-translate hide (cdr term)))))))

(encapsulate
  nil

  (defwarrant acl2::explode$inline)

  ;; Parse a rewrite rules and create functions for all the lambda expressions so
  ;; that they open up one at a time.

  (mutual-recursion

   (defun lambda-to-fnc (base-name index keys body)
     (declare (xargs :mode :program))
     (b* ((fnc-name (intern-in-package-of-symbol
                     (str::cat (symbol-name base-name)
                               "_LAMBDA-FNC_"
                               (str::int-to-dec-string index))
                     base-name))
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
       (mv fnc-name
           (append other-signatures (list signature))
           (append other-fncs fnc)
           (cons `(,fnc-name ,@keys) other-fnc-names)
           (append other-openers opener)
           new-index)))

   (defun search-lambda-to-fnc (base-name index term)
     (cond ((or (atom term)
                (eq (car term) 'quote))
            (mv nil nil nil nil term index))
           ((is-lambda term)
            (b* ((keys (cadr (car term)))
                 (body (caddr (car term)))
                 (exps (cdr term))

                 (exps (loop$ for k in keys as e in exps
                              when (b* ((chars (explode (symbol-name k))))
                                     (and (not (equal (car chars) #\*))
                                          (not (equal (last chars) '(#\*)))))
                              collect e))
                 (keys (loop$ for k in keys 
                              when (b* ((chars (explode (symbol-name k))))
                                     (and (not (equal (car chars) #\*))
                                          (not (equal (last chars) '(#\*)))))
                              collect k))
                 
                 ((mv fnc-name sigs fncs fnc-names openers new-index)
                  (lambda-to-fnc base-name index keys body)))
              (mv sigs fncs
                  fnc-names
                  openers
                  `(,fnc-name ,@exps)
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

  #|(defun openers-to-rule (base-name openers)
  `(def-rp-rule ,(sa base-name 'lambda-opener)
  (and ,@openers)))|#

  #|(defun lambdas-to-other-rules (rule-name rule untranslated-rule args)
  (declare (xargs :mode :program))
  (b* (((mv pulled-args args)
  (pull-keys-from-rest-args args '(:disabled-for-rp
  :disabled
  :disabled-for-ACL2
  :from-add-rp-rule
  :lambda-opt
  :rw-direction
  :hints)))
  (from-add-rp-rule (cdr (hons-assoc-equal :from-add-rp-rule
  pulled-args)))
  (disabled (cdr (hons-assoc-equal :disabled
  pulled-args)))
  (disabled-for-rp (or disabled
  (cdr (hons-assoc-equal :disabled-for-rp
  pulled-args))))
  (disabled-for-acl2 (or disabled
  (cdr (hons-assoc-equal :disabled-for-acl2
  pulled-args))))
  (rw-direction (cdr (hons-assoc-equal :rw-direction pulled-args)))
  (hints (cdr (hons-assoc-equal :hints pulled-args)))
  (lambda-opt (if (hons-assoc-equal :lambda-opt pulled-args)
  (cdr (hons-assoc-equal :lambda-opt pulled-args))
  t))

  ((mv hyp lhs rhs iff)
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
  (symbol-package-name rule-name)))
  (rule-name-for-rp-openers (intern$ (str::cat (symbol-name rule-name)
  "-FOR-RP-OPENERS")
  (symbol-package-name rule-name))))
  (if (and lambda-opt
  (or (and sigs fncs openers)
  (and (or sigs fncs openers)
  (hard-error
  'lambdas-to-other-rules
  "something unexpected happened.... contact Mertcan Temel<temelmertcan@gmail.com>~%"
  nil))))
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
  (AND Stable-under-simplificationp
  '(:in-theory (e/d () ()))))))
  (local
  (rp::add-rp-rule opener-lemmas :rw-direction :outside-in))

  (with-output
  :stack :pop
  :on (acl2::summary acl2::event)
  :summary-off (:other-than acl2::time acl2::rules)
  (defthmd ,rule-name-for-rp
  (and (implies ,hyp-body
  (,(if iff `iff `equal)
  ,lhs-body
  ,rhs-body))
  ,@(if (or (equal rw-direction :outside-in)
  (equal rw-direction :both)
  (and from-add-rp-rule (not hints)))
  nil
  openers))
  ,@args
  ,@(if (and from-add-rp-rule (not hints))
  `(:hints (("Goal"
  :in-theory '(,rule-name ,@(strip-cars fnc-names)))))
  `(:hints ,hints))))

  ;; if outside-in is selected, then opener lemmas should be separate

  ,@(and (or (equal rw-direction :outside-in)
  (equal rw-direction :both)
  (and from-add-rp-rule (not hints)))
  `((with-output
  :stack :pop
  :on (acl2::summary acl2::event)
  :summary-off (:other-than acl2::time acl2::rules)
  (def-rp-rule :disabled-for-acl2 t
  ,rule-name-for-rp-openers
  (and ,@openers)
  :lambda-opt nil
  :hints (("Goal"
  :use ((:instance opener-lemmas))
  :in-theory nil))))))

  ,@(if from-add-rp-rule
  nil
  `((,(if disabled-for-acl2 'defthmd 'defthm)
  ,rule-name
  ,untranslated-rule
  :hints (("Goal"
  :use ((:instance ,rule-name-for-rp)
  ,@(and (or (equal rw-direction :outside-in)
  (equal rw-direction :both))
  `((:instance ,rule-name-for-rp-openers))))
  :in-theory '((:definition iff)
  ,rule-name-for-rp
  ,@(and (or (equal rw-direction :outside-in)
  (equal rw-direction :both))
  `(,rule-name-for-rp-openers))))))))

  (add-rp-rule ,rule-name
  :lambda-opt nil
  :rw-direction ,rw-direction
  :disabled ,disabled-for-rp)
  (table corresponding-rp-rule ',rule-name ',rule-name-for-rp)
  (table corresponding-rp-rule-reverse ',rule-name-for-rp ',rule-name)

  #|(acl2::extend-pe-table ,rule-name-for-rp
  (def-rp-rule ,rule-name-for-rp
  ,body
  :hints ,',hints))|#)
  `(progn
  (with-output
  :stack :pop
  :on (acl2::summary acl2::event)
  :summary-off (:other-than acl2::time acl2::rules)
  (,(if disabled-for-acl2 'defthmd 'defthm)
  ,rule-name
  ,untranslated-rule
  ,@args
  :hints ,hints))
  (add-rp-rule ,rule-name
  :lambda-opt nil
  :rw-direction ,rw-direction
  :disabled ,disabled-for-rp)))))|#

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

  #|(defmacro defthm-lambda (rule-name rule &rest rest)
  `(make-event
  (b* (((mv err term & state)
  (acl2::translate1 ',rule t nil nil 'top-level (w state) state))
  (- (if err (hard-error 'defthm-lambda "Error translating term ~%" nil) nil)))
  (mv err
  (lambdas-to-other-rules
  ',rule-name
  term
  ',rule
  ',rest)
  state))))|#)

(xdoc::defxdoc
  defthm-lambda
  :parents (rp-other-utilities)
  :short "defthm-lambda is deprecated. Please see @(see defthmrp), @(see
  add-rp-rule), or @(see lambda-opt) for relevant topics."
  :long "<p>The defthm-lambda utility used to be used for @(see lambda-opt) in
  the calls of @(see defthmrp) and @(see add-rp-rule). After restructuring the
  program, we deprecated the defthm-lambda utility. </p>")

(xdoc::defxdoc lambda-opt
  :parents (add-rp-rule defthmrp)
  :short "A method to optimize lambda expression before RP-Rewriter attempts to
  rewrite them."
  :long "<p>RP-Rewriter does not internally work with terms that has lambda
  expressions. Every term (conjecture and rules) that is passed to the rewriter
  will be beta reduced. However, in some cases, doing
 beta-reduction will cause repetitive
  rewriting and this may result in significant proof-time and memory issues. </p>


<p> To mitigate this issue, we use a lambda optimization mechanism when adding
 rules to the RP-rewriter's ruleset with @(see add-rp-rule) and proving
 conjectures with @(see defthmrp). This mechanism is
 intended to imitate the
 structure of lambda expressions to prevent repetitive rewriting. For every
 level of lambda expression, we create a non-executable function so that values
 of the lambda expressions are rewritten first, then they are bound to the
 variables, and those variables are applied to the term. For example,
 add-rp-rule with lambda-opt enabled will produce these events for the given rule:</p>
<code>
@('
(defthm foo-redef
  (implies (p x)
           (equal (foo x)
                  (let* ((a (f1 x))
                         (b (f2 x)))
                    (f4 a a b)))))

(add-rp-rule foo-redef
             :lambda-opt t)

;; The above event is translated into this:
(encapsulate
  (((foo-redef_lambda-fnc_1 * *) => *)
   ((foo-redef_lambda-fnc_0 * *) => *))
  (local (defun-nx foo-redef_lambda-fnc_1 (b a)
           (f4 a a b)))
  (disable-exc-counterpart foo-redef_lambda-fnc_1)
  (local (add-rp-rule foo-redef_lambda-fnc_1))
  (local (defun-nx foo-redef_lambda-fnc_0 (a x)
           (foo-redef_lambda-fnc_1 (f2 x) a)))
  (disable-exc-counterpart foo-redef_lambda-fnc_0)
  (local (add-rp-rule foo-redef_lambda-fnc_0))
  (def-rp-rule
    foo-redef-for-rp-openers
    (and (equal (foo-redef_lambda-fnc_1 b a)
                (f4 a a b))
         (equal (foo-redef_lambda-fnc_0 a x)
                (foo-redef_lambda-fnc_1 (f2 x) a)))
    :disabled-for-acl2 t
    ...)
  (defthmd
    foo-redef-for-rp
    (and (implies (p x)
                  (equal (foo x)
                         (foo-redef_lambda-fnc_0 (f1 x) x))))
    :hints ...)
  ... <some-table-events> ...)
')
</code>

<p> Here, add-rp-rule will generate another lemma called
<tt>foo-redef-for-rp</tt> that is aimed to be used by RP-Rewriter
in lieu of the original <tt>foo-redef</tt> rule. The right hand side of the
original rule first binds @('a') to @('(f1 x')). After applying
@('foo-redef-for-rp'), the rewriter will first work on the @('(f1 x)') term, then
it will rewrite foo-redef_lambda-fnc_0 and bind @('a') to rewritten @('(f1 x)')
which will mimic the behavior
of the original lambda expression. Then, the program binds @('b') to @('(f2 x)') through
foo-redef_lambda-fnc_1, and then finally get the result. This way, the repeated (had it been beta reduced)
term @('(f1 x)')  is rewritten only once. </p>



<p> Users will chiefly observe this lambda optimization behavior when using
@(see def-rp-rule), @(see add-rp-rule), and @(see defthmrp). Def-rp-rule
simply proves a given lemma using ACL2 and given hints, and then calls
add-rp-rule to register the proved lemma with RP-Rewriter possibly with this
lambda optimization. Add-rp-rule and defthmrp themselves implement their
versions of the lambda optimization. Add-rp-rule parses the term of a given
rule's formula and beta reduces left-hand-side (lhs) while retaining the lambda form of
the hyps and right-hand-side (rhs). It pre-processes the term to push in the lambda
expressions in order to extract the terms for rhs and hyp. When its :lambda-opt argument is set to
:max, it tries to look for repeated terms in hyp and rhs separately that are not already bound in lambda
expressions for further optimizations. On the other hand, defthmrp does not try
to isolate rhs, hyp, and lhs during the optimization process and it works on the
term as a whole. However, whatever lambda optimization defthmrp does and
whatever events it creates in the process, they are made locally inside an
encapsulate and it is only for the sake of RP-Rewriter at the time of its
simplification of the given conjecture. Defthmrp still calls add-rp-rule when
saving the lemma as a rewrite rule for it to use later. </p>
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

  (define add-rp-rule-fn-aux (formulas rule-name lambda-opt index)
    :mode :program
    :returns (mv sigs fncs fnc-names openers bodies res-index)
    (if (atom formulas)
        (mv nil nil nil nil nil index)
      (b* (((mv flg hyp lhs rhs)
            (custom-rewrite-from-formula (car formulas)))
           ;; recollect into a lambda expression (rhs and hyp only) if there is
           ;; room for improvement
           ;;((list rhs-old hyp-old) (list rhs hyp)) 
           (rhs (if (equal lambda-opt :max) (cmr::let-abstract-term rhs 'lambda-opt-max-rhs-var) rhs))
           (hyp (if (equal lambda-opt :max) (cmr::let-abstract-term hyp 'lambda-opt-max-hyp-var) hyp))
           #|(- (or (equal rhs-old rhs)
                  (cw "changed rhs: rule: ~p0 ~%" rule-name)))|#
           #|(- (or (equal hyp-old hyp)
                  (cw "changed hyp: rule: ~p0 ~%" rule-name)))|#

           ((mv rhs-sigs rhs-fncs rhs-fnc-names rhs-openers rhs-body index)
            (search-lambda-to-fnc rule-name index rhs))
           ((mv hyp-sigs hyp-fncs hyp-fnc-names hyp-openers hyp-body index)
            (search-lambda-to-fnc rule-name index hyp))
           (lhs (beta-search-reduce lhs *big-number*))

           (body `(implies ,hyp-body
                           (,(if flg 'iff 'equal)
                            ,lhs
                            ,rhs-body)))

           ((mv sigs fncs fnc-names openers bodies index)
            (add-rp-rule-fn-aux (cdr formulas) rule-name lambda-opt index)))

        (mv (append rhs-sigs hyp-sigs sigs)
            (append rhs-fncs hyp-fncs fncs)
            (append rhs-fnc-names hyp-fnc-names fnc-names)
            (append rhs-openers hyp-openers openers)
            (cons body bodies)
            index))))

  (defines remove-unused-vars-from-lambdas
    (define remove-unused-vars-from-lambdas (term)
      :mode :program
      (cond ((or (atom term)
                 (quotep term))
             term)
            ((is-lambda term)
             (case-match term
               ((('lambda vars subterm) . expr)
                (b* ((subterm (remove-unused-vars-from-lambdas subterm))
                     (all-vars (all-vars subterm))
                     (vars-expr (pairlis$ vars expr))
                     (vars-expr (loop$ for x in vars-expr collect
                                       (and (member-equal (car x) all-vars)
                                            x)))
                     (vars-expr (remove nil vars-expr))
                     ((when (atom vars-expr))
                      subterm)
                     (vars (strip-cars vars-expr))
                     (expr (strip-cdrs vars-expr)))
                  `((lambda ,vars ,subterm) . ,expr)))
               (& term)))
            (t (cons (car term)
                     (remove-unused-vars-from-lambdas-lst (cdr term))))))
    (define remove-unused-vars-from-lambdas-lst (lst)
      (if (atom lst)
          nil
        (cons (remove-unused-vars-from-lambdas (car lst))
              (remove-unused-vars-from-lambdas-lst (cdr lst))))))

  (define push-lambdas-into-and-and-implies-aux (acc subterm)
    :mode :program
    (if (atom acc)
        subterm
      (b* ((subterm `((lambda ,(caar acc) ,subterm) . ,(cdar acc))))
        (push-lambdas-into-and-and-implies-aux (cdr acc) subterm))))

  (define push-lambdas-into-and-and-implies (term acc)
    :mode :program
    :returns (mv res-term acc-used)
    (case-match term
      (('return-last & & last)
       (push-lambdas-into-and-and-implies last acc))
      ((('lambda x subterm) . y)
       (b* ((acc (acons x y acc)))
         (case-match subterm
           (('implies p q)
            (b* ((p (push-lambdas-into-and-and-implies-aux acc p))
                 ((mv q acc-used)
                  (push-lambdas-into-and-and-implies q acc))
                 (q (if acc-used q (push-lambdas-into-and-and-implies-aux acc q))))
              (mv `(implies ,p ,q) t)))
           (('if p q ''nil)
            (b* (((mv p acc-used)
                  (push-lambdas-into-and-and-implies p acc))
                 (p (if acc-used p (push-lambdas-into-and-and-implies-aux acc p)))
                 ((mv q acc-used)
                  (push-lambdas-into-and-and-implies q acc))
                 (q (if acc-used q (push-lambdas-into-and-and-implies-aux acc q))))
              (mv `(if ,p ,q 'nil) t)))
           (&
            (b* (((when (is-lambda subterm))
                  (b* (((mv res acc-used)
                        (push-lambdas-into-and-and-implies subterm acc)))
                    (if acc-used (mv res t) (mv term nil))))
                 ((mv p q valid)
                  (case-match subterm
                    (('equal p q)
                     (mv p q t))
                    (('iff p q)
                     (mv p q t))
                    (& (mv nil nil nil))))
                 ((unless valid) (mv term nil))
                 (p (push-lambdas-into-and-and-implies-aux acc p))
                 (q (push-lambdas-into-and-and-implies-aux acc q)))
              (mv `(,(car subterm) ,p ,q)
                  t))))))
      (& (mv term nil))))

  (define add-rp-rule-fn (rule args state)
    :mode :program
    (b* ((?world (w state))
         ((std::extract-keyword-args (lambda-opt 'nil)
                                     (disabled 'nil)
                                     (rw-direction ':inside-out)
                                     (ruleset 'rp-rules)
                                     (hints 'nil))
          args)
         (rw-direction
          (cond ((equal rw-direction ':both) :both)
                ((equal rw-direction :outside-in) :outside-in)
                ((or (equal rw-direction :inside-out) (equal rw-direction nil)) :inside-out)
                (t (raise
                    ":rw-direction can only be :both, :outside-in, :inside-out,~
 or nil (meaning :inside-out) but it is given: ~p0 ~%"
                    rw-direction))))
         ((mv rule-name rune)
          (case-match rule
            ((rune-type rune-name . &)
             (if (and (or (equal rune-type :type-prescription)
                          (equal rune-type :definition)
                          (equal rune-type :rewrite)
                          (equal rune-type :unknown))
                      (symbolp rune-name))
                 (mv rune-name rule)
               (progn$ (raise "Unexpected rule name/rune is passed: ~p0" rule)
                       (mv nil nil))))
            (& (if (symbolp rule)
                   (b* ((rule (acl2::deref-macro-name rule (macro-aliases world))))
                     (mv rule (get-rune-name rule state)))
                 (progn$ (raise "Unexpected rule name/rune is passed: ~p0" rule)
                         (mv nil nil))))))

         (- (or (let* ((entry (assoc-equal
                               rule-name
                               (table-alist 'corresponding-rp-rule-openers-reverse (w state)))))
                  (and
                   entry
                   (raise "Given rule name (~p0) is registered as a rp-rule-openers. Please give the rule's original name instead: ~p1" (car entry) (cdr entry))))
                (let* ((entry (assoc-equal
                               rule-name
                               (table-alist 'corresponding-rp-rule-reverse (w state)))))
                  (and
                   entry
                   (raise "Given rule name (~p0) is registered as a corresponding rp-rule. Please give the rule's original name instead: ~p1" (car entry) (cdr entry))))))

         (- (and (consp (get-rune-name rule-name state))
                 (equal (car (get-rune-name rule-name state)) :definition)
                 (consp rune)
                 (equal (car rune) :type-prescription)
                 (raise ":type-prescription rules of functions are not supported.")))

         ;; just check if the rune can be parsed
         (- (get-rules (list rune) state :warning :err))

         ((unless lambda-opt)
          (value `(progn (table ,ruleset ',rune (cons ',rw-direction ',(not disabled)))
                         (value-triple ',rune))))

         (term (meta-extract-formula rule-name state))

         #|((acl2::er translated-term)
         (acl2::translate term t t nil 'add-rp-rule-fn world state))|#
         ;;(term (beta-search-reduce term *big-number*))

         (term (light-remove-return-last term))
         ((mv term &) (push-lambdas-into-and-and-implies term nil))
         (term (remove-unused-vars-from-lambdas term))
         (formulas (make-formula-better term *big-number*))
         ((mv sigs fncs fnc-names openers bodies &)
          (add-rp-rule-fn-aux formulas rule-name lambda-opt 0))

         ((unless (and sigs fncs fnc-names))
          ;; nothing.
          (progn$
           (and (or sigs fncs fnc-names)
                (raise "Something unexpected happen in the beta reduction/lambda optimization stage: ~p0" rule))
           (value `(progn (table ,ruleset ',rune (cons ',rw-direction ',(not disabled)))
                          (value-triple ',rune)))))

         (rule-name-for-rp (intern-in-package-of-symbol
                            (str::cat (symbol-name rule-name) "-FOR-RP") rule-name))
         (rule-name-for-rp-openers (intern-in-package-of-symbol
                                    (str::cat (symbol-name rule-name) "-FOR-RP-OPENERS") rule-name)))
      (value
       `(encapsulate
          ,sigs
          ,@fncs
          (defthmd
            ,rule-name-for-rp-openers
            (and ,@openers)
            :hints (("Goal"
                     :in-theory (union-theories
                                 '(hard-error hons-copy return-last ,@(strip-cars fnc-names))
                                 (theory 'minimal-theory)))
                    (and Stable-under-simplificationp
                         '(:in-theory (e/d () ())))))

          (defthmd ,rule-name-for-rp
            (and ,@bodies)

            :hints ,(if hints
                        hints
                      `(("Goal"
                         :use ((:instance ,rune))
                         :in-theory (union-theories
                                     '(hard-error hons-copy return-last ,@(strip-cars fnc-names))
                                     (theory 'minimal-theory)))
                        (AND Stable-under-simplificationp
                             '(:in-theory (e/d () ()))))))

          (table ,ruleset ',rune (cons ',rw-direction ',(not disabled)))

          (table corresponding-rp-rule ',rule-name ',rule-name-for-rp)
          (table corresponding-rp-rule-openers ',rule-name ',rule-name-for-rp-openers)

          (table corresponding-rp-rule-reverse ',rule-name-for-rp ',rule-name)
          (table corresponding-rp-rule-openers-reverse ',rule-name-for-rp-openers ',rule-name)
          
          (value-triple ',rule-name)))))

  (defmacro add-rp-rule (rule &rest args
                              ;; &key
                              ;; (disabled 'nil)
                              ;; (lambda-opt 'nil)
                              ;; (hints 'nil)
                              ;; (rw-direction ':inside-out)
                              ;; (ruleset 'rp-rules)
                              )
    `(with-output
       :off :all
       :on (comment error)
       ;;:stack :push
       (make-event
        (add-rp-rule-fn ',rule ',args state))))

  (defxdoc add-rp-rule
    :parents (rp-other-utilities)
    :short "Register a rule with RP-Rewriter"
    :long "<p>Please @(see rp-ruleset) for details.</p> ")

  #|(defmacro add-rp-rule (rule-name &key
  (disabled 'nil)
  (lambda-opt 'nil)
  (hints 'nil)
  (rw-direction ':inside-out)
  (ruleset 'rp-rules))

  (b* ((rw-direction
  (cond ((equal rw-direction ':both)
  :both)
  ((equal rw-direction :outside-in)
  :outside-in)
  ((or (equal rw-direction :inside-out)
  (equal rw-direction nil))
  :inside-out)
  (t (hard-error
  'add-rp-rule
  ":rw-direction can only be :both, :outside-in, :inside-out,~
  or nil (meaning :inside-out) but it is given: ~p0 ~%"
  (list (cons #\0 rw-direction)))))))
  `(make-event
  (b* ((body (and ,lambda-opt
  (meta-extract-formula ',rule-name state)))
  (lambda-opt (and ,lambda-opt
  (contains-lambda-expression body)))
  (rule-name ',rule-name)
  (new-rule-name (if lambda-opt
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
  (if lambda-opt
  `(progn
  (defthm-lambda ,rule-name
  ,body
  :from-add-rp-rule t
  :rw-direction ,',rw-direction
  :hints ,',hints)
  (with-output :off :all :gag-mode nil :on error
  (progn
  ;;(in-theory (disable ,new-rule-name))
  (value-triple (cw "This rule has a lambda expression, ~
  and it is automatically put through rp::defthm-lambda  and a ~
  new rule is created to be used by RP-Rewriter. You can disable this by setting ~
  :lambda-opt to nil ~% The name of this rule is: ~p0 ~%" ',new-rule-name))
  (value-triple ',new-rule-name))))
  rest-body)))))|#

  (define def-rp-rule-fn (args)
    :mode :program
    (b* (((mv rule-name rule args)
          (pull-name-and-body-from-args args))
         ((Unless (and rule-name rule))
          (- (hard-error 'def-rp-rule-fn
                         "Cannot pull out rule-name and body from these arguments: ~p0 ~%"
                         (list (cons #\0 args)))))

         ((std::extract-keyword-args (rule-classes ':rewrite)
                                     (lambda-opt 't)
                                     (disabled 'nil)
                                     (disabled-for-rp 'nil)
                                     (disabled-for-ACL2 'nil)
                                     (rw-direction ':inside-out)
                                     (ruleset 'rp-rules)
                                     ;;(supress-warnings 'nil)
                                     (hints 'nil)
                                     (otf-flg 'nil)
                                     (instructions 'nil))
          args))
      `(progn
         (,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
          ,rule-name
          ,rule
          ,@(and hints `(:hints ,hints))
          ,@(and otf-flg `(:otf-flg ,otf-flg))
          ,@(and instructions `(:instructions ,instructions))
          :rule-classes ,rule-classes)
         (add-rp-rule ,rule-name
                      :lambda-opt ,lambda-opt
                      :disabled ,(or disabled disabled-for-rp)
                      :rw-direction ,rw-direction
                      :ruleset ,ruleset)
         #|(acl2::extend-pe-table ,rule-name
         (def-rp-rule ,rule-name ,rule ,@hints))|#
         ;;(value-triple ',rule-name)
         )))

  (defmacro def-rp-rule (&rest args)
    (def-rp-rule-fn args))

  #|(defmacro def-rp-rule$ (defthmd disabled rule-name rule  &rest hints)
  `(progn
  (,(if defthmd 'defthmd 'defthm)
  ,rule-name ,rule ,@hints)
  (with-output :off :all :gag-mode nil :on error
  (add-rp-rule  ,rule-name :disabled ,disabled
  :lambda-opt nil))))|#)

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
      (def-rp-rule :disabled-for-acl2 t :disabled-for-rp ,disabled
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
       (rp-state (rp-state-init-rules runes runes-outside-in new-synps rp-state state
                                      :suppress-not-simplified-error t))
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
                       #|(not-simplified-action ':warning)|#)
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
           
           #|(old-not-simplified-action (not-simplified-action rp-state))|#
           #|(rp-state  (update-not-simplified-action ,not-simplified-action rp-state))|#
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
           #|(rp-state (update-not-simplified-action old-not-simplified-action rp-state))|#)
        (mv nil `(value-triple :none) state rp-state)))))

(defmacro rp-cl (&key (new-synps 'nil)
                      (runes 'nil)
                      (runes-outside-in 'nil)
                      (cases 'nil)
                      (ruleset 'rp-rules)
                      (suppress-not-simplified-error 'nil)) ;
  `(rp-rewriter
    clause
    (make rp-cl-args
          :cases ',cases
          :runes-outside-in ',runes-outside-in
          :runes ',runes #|,(if rules-override
          rules-override
          `(append (let ((world (w state))) (current-theory :here))
          ,extra-rules)
          )||#
          :ruleset ',ruleset
          :new-synps ',new-synps
          :suppress-not-simplified-error ,suppress-not-simplified-error)
    rp-state state))

(defmacro def-rp-thm (&rest rest)
  `(defthmrp ,@rest))

(defun translate-lst (term-lst acl2::stobjs-out acl2::logic-modep
                               acl2::known-stobjs ctx w state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (atom term-lst)
      (value nil)
    (b* (((acl2::er term)
          (acl2::translate (car term-lst)
                           acl2::stobjs-out acl2::logic-modep
                           acl2::known-stobjs ctx w state))
         ((acl2::er rest)
          (translate-lst (cdr term-lst)
                         acl2::stobjs-out acl2::logic-modep
                         acl2::known-stobjs ctx w state)))
      (value (cons term rest)))))

(define collect-hyps-from-implies (term)
  (case-match term
    (('implies p q)
     `(and ,p ,(collect-hyps-from-implies q)))
    (& 't)))



(define defthmrp-fn (name term args state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* (((Unless (symbolp name)) (value (raise "Given name should be a symbolp but instead got: ~p0" name)))
       ((std::extract-keyword-args (rule-classes ':rewrite)
                                   (new-synps 'nil)
                                   (disable-meta-rules 'nil)
                                   (enable-meta-rules 'nil)
                                   (enable-rules 'nil)
                                   (disable-rules 'nil)
                                   (runes 'nil)
                                   (runes-outside-in 'nil)
                                   (cases 'nil)
                                   (lambda-opt 't)
                                   (disabled 'nil)
                                   (disabled-for-rp 'nil)
                                   (disabled-for-ACL2 'nil)
                                   (rw-direction ':inside-out)
                                   (supress-warnings 'nil)
                                   (add-rp-rule 't)
                                   (ruleset 'rp-rules)
                                   (override-cl-hints 'nil)
                                   (vacuity-check ':auto))
        args)
       (world (w state))
       ((acl2::er translated-term)
        (acl2::translate (hide/unhide-constants-for-translate t term)
                         t t nil 'defthmrp-fn world state))
       (translated-term (hide/unhide-constants-for-translate nil translated-term))
       ((acl2::er cases)
        (translate-lst cases t t nil 'defthmrp-fn world state))
       ((unless (alistp new-synps))
        (value (raise "Given new-synps should be an alist but instead got: ~p0" new-synps)))
       ((acl2::er new-synps-vals) ;; new-synps is an alist...
        (translate-lst (strip-cdrs new-synps) t t nil 'defthmrp-fn world state))
       (new-synps (pairlis$ (strip-cars new-synps) new-synps-vals))
       
       (hints  (or override-cl-hints
                   `(:hints (("goal"
                              :do-not-induct t :rw-cache-state nil :do-not '(preprocess generalize fertilize)
                              :clause-processor (rp-cl :runes ,runes
                                                       :runes-outside-in ,runes-outside-in
                                                       :new-synps ,new-synps
                                                       :cases ,cases
                                                       :ruleset ,ruleset))))))
       (body
        (cond
         (lambda-opt
          (b* ((rule-name-for-rp (intern-in-package-of-symbol
                                  (str::cat "LOCAL-" (symbol-name name) "-FOR-RP") name))
               #|(name-tmp (intern-in-package-of-symbol (str::cat (symbol-name name) "-TMP") name))|#
               (translated-term (if (equal lambda-opt :max)
                                    (cmr::let-abstract-term translated-term 'lambda-opt-max-var)
                                  translated-term))
               ((mv ?sigs fncs ?fnc-names ?openers reduced-body &) (search-lambda-to-fnc name 0 translated-term))
               (- (or (and sigs fncs openers)
                      (and (or sigs fncs openers)
                           (hard-error 'defthmrp-fn "something unexpected happened.... contact Mertcan Temel<temelmertcan@gmail.com>~%" nil))))
               ((when (not sigs))
                `((with-output :stack :pop
                    (,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
                     ,name
                     ,term
                     :rule-classes ,rule-classes
                     ,@hints)))))
            `((encapsulate nil ;;defsection ,name
                ;;,sigs ;; no need to have the sigs here as we don't want to export the functions.
                (local
                 (progn
                   ,@fncs))
                (local
                 (with-output :stack :pop
                   (defthm ,rule-name-for-rp
                     ,reduced-body
                     ,@hints)))
                (,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
                 ,name ,term
                 :rule-classes ,rule-classes
                 :hints (("Goal"
                          :use ((:instance ,rule-name-for-rp))
                          :in-theory (union-theories
                                      '(hard-error hons-copy return-last ,@(strip-cars fnc-names))
                                      (theory 'minimal-theory)))
                         (and stable-under-simplificationp
                              '(:in-theory (e/d () ())))))))))
         (t `(:stack :pop
                     (,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
                      ,name
                      ,term
                      :rule-classes ,rule-classes
                      ,@hints)))))
       

       (body `(with-output :off :all :on (error) :gag-mode nil ,@body))


       (vacuity-check-body
        (and
         (or (equal vacuity-check t)
             (and (equal vacuity-check :auto)
                  ;; when :auto, only perform vacuity check when fgl::fgl-thm
                  ;; is defined.
                  (or (not (equal (meta-extract-formula 'fgl::fgl-thm state) ''t))
                      (acl2::getpropc 'fgl::fgl-thm 'acl2::macro-body))
                  ;; also tshell should be defined too.
                  (or (not (equal (meta-extract-formula 'acl2::tshell-ensure state) ''t))
                      (acl2::getpropc 'acl2::tshell-ensure 'acl2::macro-body))))
         `((value-triple (acl2::tshell-ensure))
           (make-event
            '(:or (acl2::must-fail
                   (fgl::fgl-thm (implies
                                  ,(collect-hyps-from-implies term)
                                  nil)
                                 :skip-vacuity-check t))
                  (value-triple (hard-error 'Rp-Rewriter "~%------------------------------------------------------------
!!! VACUITY CHECK FAILED !!!~%Some hypotheses / assumptions are possibly contradictory.
------------------------------------------------------------" nil)))))))
       )
    (value
     `(with-output
        :off :all :on (error 
                       ,@(and (not supress-warnings) '(comment)))
        :stack :push
        ,(if  (or disable-meta-rules
                  enable-meta-rules
                  enable-rules
                  disable-rules
                  add-rp-rule
                  vacuity-check-body)
             `(defsection ,name

                ,@vacuity-check-body
                
                ,@(and enable-meta-rules `((local
                                            (enable-meta-rules ,@enable-meta-rules))))

                ,@(and disable-meta-rules `((local
                                             (disable-meta-rules ,@disable-meta-rules))))

                ,@(and enable-rules  `((local
                                        (enable-rules ,enable-rules))))

                ,@(and disable-rules `((local
                                        (disable-rules ,disable-rules))))
                ,body

                ,@(and add-rp-rule
                       `((add-rp-rule ,name
                                      :lambda-opt ,lambda-opt
                                      :disabled ,(or disabled disabled-for-rp)
                                      :rw-direction ,rw-direction
                                      :ruleset ,ruleset))))
           body)))))

(defmacro defthmrp (name term &rest args)
  `(make-event
    (b* ((- (check-if-clause-processor-up-to-date (w state)))
         ((acl2::er body)
          (defthmrp-fn ',name ',term ',args state)))
      (value body))))

;;:i-am-here
;; (defmacro defthmrp (name term
;;                          &key
;;                          (rule-classes ':rewrite)
;;                          ;; (use-opener-error-rules 't)
;;                          (new-synps 'nil)
;;                          (disable-meta-rules 'nil)
;;                          (enable-meta-rules 'nil)
;;                          (enable-rules 'nil)
;;                          (disable-rules 'nil)
;;                          (runes 'nil)
;;                          (runes-outside-in 'nil) ;; when nil, runes will be read from
;;                          ;; rp-rules table
;;                          (cases 'nil)
;;                          (lambda-opt 't)
;;                          (disabled 'nil)
;;                          (disabled-for-rp 'nil)
;;                          (disabled-for-ACL2 'nil)
;;                          (rw-direction ':inside-out)
;;                          (supress-warnings 'nil)
;;                          (add-rp-rule 't) ;; whether or not register the lemma
;;                          ;; with add-rp-rule.
;;                          )
;;   `(make-event
;;     (b* ((world (w state))
;;          (- (check-if-clause-processor-up-to-date world))
;;          (cases ',cases #|(untranslate-lst ',cases t world)|#)
;;          (body `(with-output
;;                   :stack :pop
;;                   :on (acl2::summary acl2::event acl2::error)
;;                   :gag-mode :goals
;;                   :summary-off (:other-than acl2::time acl2::rules)

;;                   (
;;                    (

;;                   (def-rp-rule ,',name ,',term
;;                     :rule-classes ,',rule-classes
;;                     :lambda-opt ,',lambda-opt
;;                     :disabled-for-ACL2 ,',disabled-for-ACL2
;;                     :disabled-for-rp ,',disabled-for-rp
;;                     :disabled ,',disabled
;;                     :rw-direction ,',rw-direction
;;                     :hints (("goal"
;;                              :do-not-induct t
;;                              :rw-cache-state nil
;;                              :do-not '(preprocess generalize fertilize)
;;                              :clause-processor
;;                              (rp-cl :runes ,,runes
;;                                     :runes-outside-in ,,runes-outside-in
;;                                     :new-synps ,',new-synps
;;                                     :cases ',cases)))))))
;;       ,(if (or disable-meta-rules
;;                enable-meta-rules
;;                enable-rules
;;                disable-rules
;;                add-rp-rule)
;;            ``(with-output
;;                :off :all ,@(and ,(not supress-warnings) '(:on (comment)))
;;                :stack :push
;;                (encapsulate
;;                  nil
;;                  ,@(if ',enable-meta-rules
;;                        `((local
;;                           (enable-meta-rules ,@',enable-meta-rules)))
;;                      'nil)

;;                  ,@(if ',disable-meta-rules
;;                        `((local
;;                           (disable-meta-rules ,@',disable-meta-rules)))
;;                      'nil)

;;                  ,@(if ',enable-rules
;;                        `((local
;;                           (enable-rules ,',enable-rules)))
;;                      'nil)

;;                  ,@(if ',disable-rules
;;                        `((local
;;                           (disable-rules ,',disable-rules)))
;;                      'nil)
;;                  ,body))
;;          `body))))

(xdoc::defxdoc
  def-rp-thm
  :parents (rp-other-utilities)
  :short "Same as @(see rp::defthmrp)")

(xdoc::defxdoc defthmrp
  :short "A defthm macro that calls RP-Rewriter as a clause processor with custom arguments."
  :parents (rp-utilities rp-rewriter)
  :long "<p>RP::Defthmrp is a macro that expands to defthm and other auxiliary events that uses RP-Rewriter as a
 clause-processor to attempt a proof for the given conjecture.</p>


<h4> Signature: </h4>

<code>
@('
 (rp::defthmrp
  <new-rule-name>
  <conjecture>
  ;; optional keys:
  :rule-classes <...>   ;; default: :rewrite
  :new-synps <...>      ;; an alist to attach syntaxp to some existing
                        ;; rewrite rules. Default: nil
  :enable-meta-rules (meta-fnc1 meta-fnc2 ...)  ;; an unquoted list of names
                                                ;; of meta functions that users
                                                ;; wants to enable. Default: nil
  :disable-meta-rules (meta-fnc1 meta-fnc2 ...) ;; same as above for disable
  :enable-rules (append '(rule1 rule2) ;; List  of  rule-names  to enable.  The
                        *rules3*       ;; macro will evaluate  the expressions first
                        ...)           ;; to generate the names.  Default: nil
  :disable-rules <...>            ;; Same as above for disable
  :runes '(rule1 rule2  ...) ;; When  nil, the macro uses the existing rule-set
                             ;; of RP-rewriter from the  table specified in the
                             ;; ruleset argument.  Otherwise,  it will only use
                             ;; the  inside-out rules  given in  this argument.
                             ;; Default: nil
  :runes-outside-in '(rule1  rule2 ...) ;;  same as above  but for runes  to be
                                        ;; applied outside-in. Default: nil
  :cases (case1 case2 ...)    ;; casesplit the conjecture. Default: nil
  :lambda-opt <...>           ;; perform lambda  optimization. Useful  if the
                              ;; conjecture  has lambda  expressions.  
                              ;; Default: t
  :disabled  <t-or-nil>          ;; Disables the resulting rule for both ACL2 and RP
  :disabled-for-rp <t-or-nil>    ;; Disables the resulting rule only for RP
  :disabled-for-ACL2 <t-or-nil>  ;; Disables the resulting rule only for ACL2
  :rw-direction <...>            ;; Rewrite direction of the resulting rule for
                                 ;; RP. Default: :inside-out
  :supress-warnings <t-or-nil>   ;; supress some warnings. Default: nil
  :add-rp-rule <t-or-nil>        ;; Whether or not the rule should be added as
                                 ;; a rp rule. Default: t.
  :ruleset <...>                 ;; select which table to read and save
                                 ;; the rules. Default: rp-rules
  )
')
</code>

<h4> Parameters Explained </h4>

<p><b> rule-classes</b> will be passed as is to defthm. See @(see acl2::RULE-CLASSES). </p> 

<p><b> new-synps </b> can be used when users want to add new syntaxp hypothesis
to existing rewrite rules. This argument should be an alist.
Each key is a name of the rule (not its @(see acl2::rune)), e.g.,
key should be natp-implies-integerp, and not (:rewrite natp-implies-integerp). Each value should
be the desired additional syntaxp expression. When parsing every added rule,
the program will look up each of their names on this new-synps alist and attach
a translated @(see syntaxp) term at the beginning of existing hyps of the
rule. The program uses @(see assoc-equal) for look ups therefore if you have
repeated keys, then the first one will override the others.  The defthmrp macro
will translate the given terms.
</p>

<p>
<b>enable-meta-rules</b> and <b>disable-meta-rules</b> expect a list of meta
function names to enable/disable. These are passed to local events (@(see
enable-meta-rules) and @(see
disable-meta-rules)) before the
clause processor. The program will go through all the added
meta rules and enable/disable them with matching meta function names. For
example, if a meta function is used in two different rules with different
trigger functions, they will both be affected. enable-rules/disable-rules may
be used to enable/disable specific meta rules.  
</p>

<p>
<b>enable-rules</b> and <b>disable-rules</b> takes a term that will be
translated and evaluated to a list of rune/rule names that will be locally
disabled/enabled before the RP-Rewriter is called. See @(see rp-ruleset) for
detauls about how
the rules are managed. 
</p>

<p>
<b> runes </b> and <b> runes-outside-in </b> can be used to tell the rewriter to
use a certain set of rules instead of reading them from the table. This is by
default nil and we don't expect these options to be used often.
</p>

<p> <b> cases </b> is a list of terms which are used as hints in the rewriter
to casesplit. For each term in cases, the conjecture will be rewritten to
@('(if case conjecture conjecture)'). So if you pass 3 cases, then the given
conjecture will be repeated 2^3=8 times for each case combination. The number
of such rewrites can be fewer if certain case combinations contradict each
other as cases themselves will be rewritten as well. Given list of cases can be
untranslated terms.
</p>

<p> <b> lambda-opt</b> stands for \"lambda optimization\". Due to the
complexity of side-condition tracking, the rewriter does not internally
support lambda expressions. If you pass a lambda expression to the clause
processor, it is first @(see acl2::beta-reduce)d and then the rewriting
starts. In case of repeated large terms, this can cause expensive repetitive
rewriting. Therefore, we implement an additional mechanism to define some local
auxiliary lemmas to split each step of lambda expressions to different rewrite
rules. This helps to prevent the repeated rewriting problem. Please see @(see
lambda-opt) for more details. The <b>lambda-opt</b> argument can take :max, t,
or nil. When t, it retains the original lambda expression structure. When :max,
it retains the original lambda structure and tries to search for repeated terms
that are not lambda wrapped in the original term. When nil, the lambda
optimization feature is disabled and the term is beta-reduced before rewriting. 
</p>


<p> <b> disabled </b>, <b> disabled-for-rp </b>, and <b> disabled-for-ACL2</b>
controls if the rule derived from proved conjecture should be disabled for RP
rewriter, ACL2 rewriter, or both. </p>

<p> <b>rw-direction</b> RP-Rewriter can rewriter both from inside-out or from
outside-in directions. This argument tells the rw direction the resulting rule
should have. By default, it is set to :inside-out. It can be :inside-out,
:outside-in, or :both.
</p>

<p><b> supress-warnings </b> can be used to turn off printing of some
warnings. </p>

<p> <b> add-rp-rule </b> tells the program whether or not to call the @(see
add-rp-rule) event after proving the conjecture to register it in the
rewriter's ruleset table. It is by default set to t. When set to nil, relevant
arguments such as rw-direction, disabled-for-rp will be ignored. Some shared
parameters between add-rp-rule and internal defthmrp functionality such as
lambda-opt will be passed as is.</p>

<p> <b> ruleset </b> is passed directly to add-rp-rule as well as used by the
clause processor. It determines which
table to read and save the rewrite rule. By default, it is @('rp-rules'). If users
want to manage their own rewriting scheme in a custom table, then they may
choose to collect rules in another table with this argument. </p>

"
  )

(progn
  (defun pp-rw-rules (rules world)
    (declare (xargs :mode :program))
    (b* (((when (atom rules)) nil)
         (rule (car rules))
         ((Unless (weak-custom-rewrite-rule-p rule))
          (cw "Unexpected rule type: ~p0 ~%" rule))
         (rune (access custom-rewrite-rule rule :rune))
         (rune-entry (hons-assoc-equal rune (table-alist 'rp-rules world)))
         (hyps (untranslate-lst (access custom-rewrite-rule rule :hyp)
                                                                       t world))
         (- (cw  "Rune:              ~p0~%" rune))
         (- (cw  "Enabled:           ~p0~%" (and rune-entry (cddr rune-entry))))
         
         (- (cwe "Hyps:              ~p0~%" (if hyps (cons 'and hyps) 't)))
         (- (cw  "Equiv:             ~p0~%" (if (access custom-rewrite-rule rule :flg) 'iff 'equal)))
         (- (cwe "Lhs:               ~p0~%" (untranslate (access custom-rewrite-rule rule :lhs/trig-fnc)
                                                        t world)))
         (- (cwe "Rhs:               ~p0~%" (untranslate (access custom-rewrite-rule rule :rhs/meta-fnc)
                                                        t world)))
         (- (cw "~%")))
      (pp-rw-rules (cdr rules) world)))

  (define rp-pr-fn (name state)
    (declare (xargs :mode :program
                    :stobjs (state)))
    (b* ((extra-names
          (b* ((name (case-match name ((& name . &) name) (& name)))
               ((Unless (symbolp name))
                (raise "Unexpected name: ~p0" name))
               (extra-name (intern-in-package-of-symbol (str::cat (symbol-name name) "-FOR-RP-OPENERS")
                                                        name))
               (extra-names (or (equal (meta-extract-formula extra-name state) ''t)
                                (list extra-name)))

               (extra-name (intern-in-package-of-symbol (str::cat (symbol-name name) "-OPENERS")
                                                        name))
               (extra-names (if (or (equal (meta-extract-formula extra-name state) ''t)
                                    (not (str::substrp "-FOR-RP" (symbol-name name))))
                                extra-names
                              (cons extra-name extra-names))))
            extra-names))
         (rules (get-rules (cons name extra-names) state :warning :err))
         ((unless rules)
          nil)
         (rules (acl2::flatten (strip-cdrs rules))))
      (pp-rw-rules rules (w state))))

  (defmacro rp-pr (name)
    (list 'rp-pr-fn (list 'quote name) 'state))

  (xdoc::defxdoc rp-pr
    :parents (rp-ruleset rp-rewriter/debugging)
    :short "Print the rules for RP-Rewriter (similar to @(see pr))"
    :long "<p>Please @(see rp-ruleset) for details.</p> ")
  
  )

(xdoc::defxdoc rp-other-utilities
  :short "Some names that are aliases to other tools"
  :parents (rp-utilities)
  )
