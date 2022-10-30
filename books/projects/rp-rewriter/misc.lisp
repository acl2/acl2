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

(local
 (include-Book "proofs/extract-formula-lemmas"))

(local
 (include-Book "proofs/rp-state-functions-lemmas"))

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
            (b* (((mv fnc-name sigs fncs fnc-names openers new-index)
                  (lambda-to-fnc base-name index (cadr (car term)) (caddr (car term)))))
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
  :parents (rp-utilities)
  :short "A useful utility to use rewrite rules that has lambda expression on
 RHS for RP-Rewriter."
  :long "<p>RP-Rewriter does not work with terms that has lambda expressions. Every
 rewrite rule and conjectures are lambda-optd. However, for some cases, doing
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
           (rhs (if (equal lambda-opt :max) (cmr::let-abstract-term rhs 'rhs-var) rhs))
           (hyp (if (equal lambda-opt :max) (cmr::let-abstract-term hyp 'hyp-var) hyp))
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
          (def-rp-rule
            ,rule-name-for-rp-openers
            (and ,@openers)
            :disabled-for-acl2 t
            :lambda-opt nil
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
          (table corresponding-rp-rule-reverse ',rule-name-for-rp ',rule-name)

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
                      :rw-direction ,rw-direction)
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
                                   (add-rp-rule 't))
        args)
       (world (w state))
       ((acl2::er translated-term)
        (acl2::translate (hide/unhide-constants-for-translate t term)
                         t t nil 'defthmrp-fn world state))
       (translated-term (hide/unhide-constants-for-translate nil translated-term))
       ((acl2::er cases)
        (translate-lst cases t t nil 'defthmrp-fn world state))
       #|((acl2::er new-synps) ;; I guess new-synps should be an alist...
       (translate-lst new-synps t t nil 'defthmrp-fn world state))|#
       (hints  `(:hints (("goal"
                          :do-not-induct t :rw-cache-state nil :do-not '(preprocess generalize fertilize)
                          :clause-processor (rp-cl :runes ,runes
                                                   :runes-outside-in ,runes-outside-in
                                                   :new-synps ',new-synps
                                                   :cases ',cases)))))
       (body
        (cond
         (lambda-opt
          (b* ((rule-name-for-rp (intern-in-package-of-symbol (str::cat (symbol-name name) "-FOR-RP") name))
               #|(name-tmp (intern-in-package-of-symbol (str::cat (symbol-name name) "-TMP") name))|#
               ((mv ?sigs fncs ?fnc-names ?openers reduced-body &) (search-lambda-to-fnc name 0 translated-term))
               (- (or (and sigs fncs openers)
                      (and (or sigs fncs openers)
                           (hard-error 'defthmrp-fn "something unexpected happened.... contact Mertcan Temel<temelmertcan@gmail.com>~%" nil))))
               ((when (not sigs))
                `(,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
                  ,name
                  ,term
                  :rule-classes ,rule-classes
                  ,@hints)))
            `(encapsulate nil
               ;;,sigs
               (local
                (progn
                  ,@fncs))
               (local
                (defthm ,rule-name-for-rp
                  ,reduced-body
                  ,@hints))
               (,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
                ,name ,term
                :rule-classes ,rule-classes
                :hints (("Goal"
                         :use ((:instance ,rule-name-for-rp))
                         :in-theory (union-theories
                                     '(hard-error hons-copy return-last ,@(strip-cars fnc-names))
                                     (theory 'minimal-theory)))
                        (and stable-under-simplificationp
                             '(:in-theory (e/d () ()))))))))
         (t `(,(if (or disabled disabled-for-ACL2) 'defthmd 'defthm)
              ,name
              ,term
              :rule-classes ,rule-classes
              ,@hints))))
       (body `(with-output :stack :pop ,body)))
    (value
     (if (or disable-meta-rules
             enable-meta-rules
             enable-rules
             disable-rules
             add-rp-rule)
         `(with-output
            :off :all :on (error 
                           ,@(and (not supress-warnings) '(comment)))
            :stack :push
            ;;:stack :push
            (encapsulate
              nil
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
                                    :rw-direction ,rw-direction)))
              ))
       body))))

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
               ((when (equal (meta-extract-formula extra-name state) ''t))
                nil))
            (list extra-name)))
         (rules (get-rules (cons name extra-names) state :warning :err))
         ((unless rules)
          nil)
         (rules (acl2::flatten (strip-cdrs rules))))
      (pp-rw-rules rules (w state))))

  (defmacro rp-pr (name)
    (list 'rp-pr-fn (list 'quote name) 'state)))

(xdoc::defxdoc
  rp-other-utilities
  :short "Some names that are aliases to other tools"
  :parents (rp-utilities)
  )
