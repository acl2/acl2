; Copyright (C) Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

; Preprocess abbreviated ACL2 terms before they are used to generate an SVA
; from ACL2 uop proof assumptions.

(in-package "SV")

(include-book "std/util/defines" :dir :system)
; help with labelpair
(include-book "centaur/sv/svtv/chase-base" :dir :system)
(include-book "assume-to-sva-base")
(include-book "centaur/sv/svtv/process" :dir :system)
; simplify terms using proof builder's rewriter
(include-book "e-smpl")

(define goto-p (x)
  "Recognizer for signal reference in an SVTV"
  ;; Form: ("sig_name" phase/(label . [offset]))
  (and (conspn x 2)
       (stringp (car x))
       (sv::svtv-labelpair-p (cadr x))))

(define goto->var1 ((sig stringp)
                    (phase natp))
  (intern-in-package-of-symbol
   (str::upcase-string
    ;; "SVA_" indicates this name was generated
    (str::cat "SVA_" sig "_PHASE_" (str::nat-to-dec-string phase)))
   'pkg))

(define goto->var ((x goto-p)
                   (labels symbol-listp))
  :guard-hints (("Goal" :in-theory (enable goto-p)))
  "Convert goto-p reference into a symbol"
  (b* (((unless labels)
        (raise "The following GOTO-expression was encountered, but no SVTV was
                   provided to resolve label references: ~x0"
               x))
       (sig (car x))
       (labelpair (cadr x))
       (phase (sv::svtv-chase-labelpair-phase labelpair labels))
       ((unless phase)
        (raise "Error interpreting phase: ~x0 -- label not found~%" labelpair))
       ((unless (<= 0 phase))
        (raise "Error interpreting phase: ~x0 -- normalized to negative value: ~x1~%" labelpair phase))
       )
    (goto->var1 sig phase)))

(define merge-envs ((xs symbol-alistp) (alst symbol-alistp))
  (if (atom xs)
      alst
    (b* ((x (car xs)))
      (merge-envs (cdr xs) (put-assoc (car x) (cdr x) alst)))))

(define clean-declares (forms)
  (if (atom forms)
      forms
    (b* ((form (car forms))
         ((unless (consp form)) forms)
         (fn (car form)))
      (if (eq fn 'declare)
          (clean-declares (cdr forms))
        forms))))

(define get-defun-event-body ((fn symbolp) &key (state 'state))
  :mode :program
  (b* ((event (acl2::get-defun-event fn (w state))))
    (case-match event
      (('defun & & . rest)
       (b* ((clean-body (clean-declares rest))
            ((unless (equal (len clean-body) 1))
             (raise "Expected function body to be a list containing one
  element, after declare forms have been removed")))
         (car clean-body)))
      (& (raise "Expected a defun event form for fn: ~x0" fn)))))

(local
 (defthm plist-worldp-get-global
   (implies (state-p1 state)
            (plist-worldp (get-global 'acl2::current-acl2-world
                                      state)))
   :hints
   (("Goal" :in-theory (enable get-global)))))

(define preprocess-fn/macro=>t-p ((fn/macro symbolp))
  "Function/macro calls that assume-to-sva will assume are t"
  ;; We are unsure of the meaning of unsigned-byte-p in SystemVerilog so we
  ;; assume it to be true in the generated assertion.
  (or (str::strsuffixp "AUTOHYPS" (symbol-name fn/macro))
      (eq fn/macro 'unsigned-byte-p)))

(define preprocess-fn/macro=>nil-p ((fn/macro symbolp))
  "Function calls that assume-to-sva will assume are nil"
  (member-eq fn/macro '(raise cw)))

(define assume-to-sva-constp (x)
  :returns r
  (if (atom x)
      (and (symbolp x)
           (equal (symbol-package-name x) "KEYWORD"))
    (and (conspn x 2)
         (quotep x)))
  ///
  (defret pseudo-termp-<fn>
    (implies (assume-to-sva-constp x)
             (pseudo-termp x))))

(define assume-to-sva-const-listp (l)
  :returns r
  (if (atom l)
      (null l)
    (b* ((x (car l)))
      (and (assume-to-sva-constp x)
           (assume-to-sva-const-listp (cdr l)))))
  ///
  (defret pseudo-term-listp-<fn>
    (implies r
             (pseudo-term-listp l))))

(define simplify-term-fn-call ((fn symbolp)
                               (args assume-to-sva-const-listp)
                               &key
                               (state 'state))
  :guard (not (eq fn 'quote))
  :returns (r pseudo-termp)
  (b* (((mv er value)
        (acl2::magic-ev (cons fn args) ;; trm to evaluate
                        nil            ;; alist binding variables to values
                        ;; all constant, hence no bindings
                        state ;; acl2 state
                        nil   ;; hard-error-returns-nilp
                        nil))
       ((when er)
        (raise "Error attempting to simplify term: ~x0"
               (cons fn args)))
       ;; value returned is a piece of data
       (value (kwote value))
       ((unless (assume-to-sva-constp value))
        (raise "Expected a quoted constant from evaluation: ~x0" (cons fn args))))
    value))

(define simplify-term-if ((fn symbolp)
                          (args pseudo-term-listp))
  :guard (eq fn 'if)
  :returns (r :hyp :guard pseudo-termp)
  (b* (((unless (conspn args 3))
        (raise "Expected ~x0 to have 3 arguments: ~x0"
               (cons fn args)))
       (arg1 (first  args))
       (arg2 (second args))
       (arg3 (third  args)))
    (if (assume-to-sva-constp arg1)
        (if (equal arg1 (kwote nil))
            arg3
          arg2)
      (cons fn args))))

(defines
  simplify-term
  (define simplify-term ((x pseudo-termp) &key (state 'state))
    :verify-guards nil
    :returns (r pseudo-termp)
    (cond
     ((atom x)
      ;; consider using legal-variablep
      (if (and (symbolp x)
               (not (booleanp x)))
          x
        (raise "Unexpected atom: ~x0" x)))
     ((quotep x)
      (b* (((unless (conspn x 2))
            (raise "Quote expects one argument: ~x1" x)))
        x))
     (t (b* ((fn (car x))
             ((unless (symbolp fn))
              (raise "Expected a symbol in function position: ~x0" x))
             (args (cdr x))
             (args-smpl (simplify-term-list args)))
          (cond
           ((assume-to-sva-const-listp args-smpl)
            (simplify-term-fn-call fn args-smpl))

           ((not (hons-get fn *acl2-fn-to-vl*))
            (raise "~x0 is not a supported function. Please ensure its
            arguments evaluate to constants: ~x1" fn x))

           ((eq fn 'if)
            (simplify-term-if fn args-smpl))

           (t (cons fn args-smpl)))))))

  (define simplify-term-list ((xs pseudo-term-listp) &key (state 'state))
    :returns (r pseudo-term-listp)
    (if (atom xs)
        nil
      (cons (simplify-term (car xs))
            (simplify-term-list (cdr xs)))))
  ///
  (verify-guards+ simplify-term))

(defines
  assume-to-sva-preprocess1
  (define assume-to-sva-preprocess1 (x env
                                       &key
                                       ((svtv-labels symbol-listp) 'svtv-labels)
                                       (e-smpl-hyps 'e-smpl-hyps)
                                       (e-smpl-rcnst 'e-smpl-rcnst)
                                       (state 'state))
    "Preprocess an abbreviated term to be used with assume-to-sva"
    :mode :program
    ;; Input x is an abbreviated   term.
    ;; Output  is an unabbreviated term.
    (b* (((when (atom x))
          ;; take care of self-quoting atoms
          (value
           (cond ((booleanp x) (kwote x))
                 ((integerp x) (kwote x))
                 ((symbolp x)
                  (b* ((pair (hons-get x env)))
                    (cond
                     (pair (cdr pair))
                     (t    (b* ((constant
                                 (acl2::defined-constant
                                  x (w state))))
                             (or constant
                                 x))))))
                 (t (raise "Unexpected atom: ~x0" x)))))
         (fn (car x))
         ;; Convert goto reference for a SystemVerilog signal into a symbol
         ;; variable.
         ((when (goto-p x))
          (value (goto->var x svtv-labels)))

         ;; handle lambdas
         ((when (acl2::flambdap fn))
          (b* (((unless (eq (car fn) 'lambda))
                (value (raise "Expected a lambda application, but found: ~x0"
                              x)))
               (body     (acl2::lambda-body fn))
               (formals  (acl2::lambda-formals fn))
               (args     (cdr x))
               ((unless (= (len formals) (len args)))
                (value
                 (raise "Lambda application expects ~x0 arguments: ~x1"
                        (len formals) x)))
               ((mv - args-clean state)
                (assume-to-sva-preprocess1-lst args env))
               (new-env (pairlis$ formals args-clean))
               )
            (with-fast-alist new-env
              (assume-to-sva-preprocess1 body new-env ))))

         ((unless (symbolp fn))
          (value (raise "Expected a symbol in function position: ~x0" x)))
         (args (cdr x)))
      (cond

       ((quotep x) (value x))
       ;; Rewrite to nil
       ;; ((preprocess-fn/macro=>nil-p fn) (value (kwote nil)))
       ;; Rewrite to t
       ((preprocess-fn/macro=>t-p   fn) (value (kwote t)))

       ;; Simplify return-last
       ((eq fn 'return-last)
        ;; Theorem: (equal (return-last x y z) z)
        (b* (((unless (conspn args 3))
              (value (raise "~x0 expects 3 arguments: ~x1"
                            fn x))))
          (assume-to-sva-preprocess1 (third args) env)))

       ;; If special-case
       ((eq fn 'if)
        (b* (((mv - cnd state) (assume-to-sva-preprocess1 (car args) env))
             ((when (assume-to-sva-constp cnd))
              (if (equal cnd (kwote nil))
                  (assume-to-sva-preprocess1 (third args) env)
                (assume-to-sva-preprocess1 (second args) env)))
             ((mv - args-clean state)
              (assume-to-sva-preprocess1-lst args env)))
          ;; (e-smpl (cons fn args-clean) e-smpl-hyps e-smpl-rcnst)
          (value (cons fn args-clean))
          ))

       ;; simplify the term
       (t
        (b* (((mv - args-clean state)
              (assume-to-sva-preprocess1-lst args env)))
          (cond ((assume-to-sva-const-listp args-clean)
                 (value (simplify-term-fn-call fn args-clean)))

                ((assoc-equal fn acl2::*primitive-formals-and-guards*)
                 (e-smpl (cons fn args-clean) e-smpl-hyps e-smpl-rcnst))

                ((hons-get fn *acl2-fn-to-vl*)
                  (value (cons fn args-clean)))
                (t
                 (b* ((term (cons fn args-clean))
                      ((mv - new-term state)
                       (e-smpl (cons fn args-clean) e-smpl-hyps e-smpl-rcnst))
                      ((when (equal term new-term))
                       ;; expand function body
; Note: this allows recursive functions to be expanded. If the hypotheses of
; the base cases cannot be resolved, the expansion may not terminate. How
; should function-expansion of recursive functions be limited to prevent this?

; The following method uses the rewriter to perform beta
; reduction. Unfortunately, this method substitutes the formals in the body
; before the actuals have been evaluated. This can lead to the duplicate
; evaluations of expensive functions!
                       #||
                       (b* (((mv - expand-rcnst state)
                             (load-hints-into-rcnst `(:expand ,term)
                                                    e-smpl-rcnst))
                            ((mv - new-term state)
                             (e-smpl term e-smpl-hyps expand-rcnst)))
                       (assume-to-sva-preprocess1 new-term nil))
                       ||#
                       (b* ((new-env (pairlis$
                                      (acl2::formals fn (w state))
                                      args-clean)))
                         (with-fast-alist new-env
                           (assume-to-sva-preprocess1
                            (acl2::body fn nil (w state))
                            new-env)))))
                   (assume-to-sva-preprocess1 new-term nil))))))
       )))

  (define assume-to-sva-preprocess1-lst (xs env
                                            &key
                                            (acc 'nil)
                                            ((svtv-labels
                                              symbol-listp)
                                             'svtv-labels)
                                            (e-smpl-hyps 'e-smpl-hyps)
                                            (e-smpl-rcnst 'e-smpl-rcnst)
                                            (state 'state))
    (if (atom xs)
        (value (reverse acc))
      (b* ((x (car xs))
           ((mv - x-clean state)
            (assume-to-sva-preprocess1 x env)))
        (assume-to-sva-preprocess1-lst (cdr xs) env
                                       :acc (cons x-clean acc))
        )))

  )

(defines
  assume-to-sva-preprocess-member
  (define assume-to-sva-preprocess-member (rhs (arr-prefix stringp)
                                               (var-prefix stringp)
                                               &optional
                                               ((name-arrays-alst symbol-alistp) 'nil)
                                               ((member-calls symbol-alistp) 'nil)
                                               ((array-count natp) '0)
                                               ((var-count natp) '0))
    :verify-guards nil
    :returns (mv term
                 (arrays-alst :hyp (symbol-alistp name-arrays-alst) symbol-alistp)
                 (member-alst :hyp (symbol-alistp member-calls) symbol-alistp)
                 (final-array-count :hyp (natp array-count) natp)
                 (final-var-count   :hyp (natp var-count) natp))
    (if (atom rhs)
        (mv rhs name-arrays-alst member-calls array-count var-count)
      (b* ((fn (car rhs))
           (args (cdr rhs)))
        (if (eq (car rhs) 'member-equal)
            (b* (((unless (and (conspn args 2)
                               (quotep (second args))
                               (conspn (second args) 2)
                               (integer-listp
                                (unquote (second args)))))
                  (mv (raise "member-equal only takes an integer list as its
  second arugment: ~x0" rhs) nil nil 0 0))
                 (arg1 (first args))
                 (arg2 (unquote (second args)))
                 ;; SystemVerilog does not allow empty arrays.
                 ;; (member-equal x nil) = nil
                 ((when (null arg2))
                  (mv (kwote nil) name-arrays-alst member-calls array-count
                      var-count))
                 (pair (rassoc-equal arg2 name-arrays-alst))
                 ((mv array-name array array-count)
                  (if pair
                      (mv (car pair) (cdr pair) array-count)
                    (mv (intern-in-package-of-symbol
                         (str::cat arr-prefix
                                   (str::nat-to-dec-string array-count))
                         'pkg)
                        arg2
                        (1+ array-count))))
                 (var-name
                  (intern-in-package-of-symbol
                   (str::cat var-prefix (str::nat-to-dec-string
                                         var-count))
                   'pkg))
                 (var-count (1+ var-count))
                 (name-arrays-alst
                  (if pair name-arrays-alst
                    (cons (cons array-name array)
                          name-arrays-alst)))
                 (member-calls
                  (cons (cons var-name
                              `(member-equal ,arg1 ,array-name))
                        member-calls))
                 )
              (mv var-name name-arrays-alst member-calls array-count var-count))
          (b* (((mv args-clean name-arrays-alst member-calls array-count var-count)
                (assume-to-sva-preprocess-member-lst
                 args arr-prefix var-prefix name-arrays-alst member-calls
                 array-count var-count)))
            (mv (cons fn args-clean) name-arrays-alst member-calls array-count var-count))))))

  (define assume-to-sva-preprocess-member-lst
    (rhs-lst (arr-prefix stringp)
             (var-prefix stringp)
             &optional
             ((name-arrays-alst symbol-alistp) 'nil)
             ((member-calls     symbol-alistp) 'nil)
             ((array-count natp) '0)
             ((var-count   natp) '0))
    :returns (mv term
                 (arrays-alst :hyp (symbol-alistp name-arrays-alst) symbol-alistp)
                 (member-alst :hyp (symbol-alistp member-calls) symbol-alistp)
                 (final-array-count :hyp (natp array-count) natp)
                 (final-var-count   :hyp (natp var-count) natp))
    (if (atom rhs-lst)
        (mv rhs-lst name-arrays-alst member-calls array-count var-count)
      (b* (((mv rhs-clean name-arrays-alst member-calls array-count var-count)
            (assume-to-sva-preprocess-member
             (car rhs-lst) arr-prefix var-prefix name-arrays-alst member-calls
             array-count var-count))
           ((mv rhs-lst-clean name-arrays-alst member-calls array-count var-count)
            (assume-to-sva-preprocess-member-lst
             (cdr rhs-lst) arr-prefix var-prefix name-arrays-alst member-calls
             array-count var-count)))
        (mv (cons rhs-clean rhs-lst-clean)
            name-arrays-alst
            member-calls
            array-count
            var-count))))

  ///

  (local
   (defthm consp-rassoc-equal
     (implies (and (alistp y) (rassoc-equal x y))
              (consp (rassoc-equal x y)))))

  (defret natp-array-count-assume-to-sva-preprocess-member-lst
    (implies (natp array-count)
             (natp final-array-count)))

  (defret natp-var-count-assume-to-sva-preprocess-member-lst
    (implies (natp var-count)
             (natp final-var-count)))

  (verify-guards assume-to-sva-preprocess-member-fn)
  )

(define assume-to-sva-preprocess (thm (svtv (or (sv::svtv-p svtv)
                                                (null svtv)))
                                      &key (state 'state))
  :parents (|Generating SVAs from Assumptions|)
  :short "Clean and expand the assume theorem before converting to an SVA"
  :mode :program
  (b* ((- "1. Extract LHS and RHS of the thm")
       ((unless (and (conspn thm 3)
                     (equal (first thm) 'implies)))
        (prog2$ (raise "Expected input to be a theorem of the form (implies lhs rhs): "
                       thm)
                (mv nil nil nil nil state)))
       (lhs (second thm))
       (rhs (third thm))
       (- "2. Preprocess and simplify the LHS and RHS")
       ((mv ?er lhs)
        (acl2::translate-cmp lhs  ;; term to translate
                             t     ;; stobjs-out: is t for logical translation
                             t     ;; logic-modep: fail if program-mode fn.
                             nil   ;; known-stobjs: do not use any stobjs
                             'assume-to-sva-preprocess           ;; ctx
                             (w state)                           ;; w: world
                             (acl2::default-state-vars t)))
       ((mv ?er rhs)
        (acl2::translate-cmp rhs  ;; term to translate
                             t     ;; stobjs-out: is t for logical translation
                             t     ;; logic-modep: fail if program-mode fn.
                             nil   ;; known-stobjs: do not use any stobjs
                             'assume-to-sva-preprocess           ;; ctx
                             (w state)                           ;; w: world
                             (acl2::default-state-vars t)))
       (svtv-labels (sv::svtv->labels svtv))
       ((mv e-smpl-hyps e-smpl-rcnst state)
        (get-hyps-type-alist-rcnst
         (sv::svtv-autohyps svtv)
         '(:in-theory '(e-smpl-theory))
         state))
       ((mv - lhs-preprcs state)
        (assume-to-sva-preprocess1
         lhs nil :svtv-labels svtv-labels
         :e-smpl-hyps  e-smpl-hyps
         :e-smpl-rcnst e-smpl-rcnst))
       ((mv - rhs-preprcs state)
        (assume-to-sva-preprocess1
         rhs nil :svtv-labels svtv-labels
         :e-smpl-hyps  e-smpl-hyps
         :e-smpl-rcnst e-smpl-rcnst))
       ((mv - lhs-smpl state)  (e-smpl lhs-preprcs e-smpl-hyps e-smpl-rcnst))
       ((mv - rhs-smpl state)  (e-smpl rhs-preprcs e-smpl-hyps e-smpl-rcnst))
       ((mv rhs-clean arrays member-calls ?array-count ?var-count)
        (assume-to-sva-preprocess-member rhs-smpl "SVA_arr" "SVA_member_call")))
    (mv lhs-smpl rhs-clean arrays member-calls state)))

