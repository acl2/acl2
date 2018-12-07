; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "misc/without-waterfall-parallelism" :dir :system)
(include-book "gify")
(include-book "run-gified-cp")
(include-book "glcp-templates")
(include-book "generic-geval")
;; (local (include-book "gify-thms"))
(local (include-book "general-object-thms"))
;; (include-book "centaur/misc/defapply" :dir :system)

;; Now that we've proven the correctness of the generic clause processor above,
;; we now define a macro which makes a clause processor for a particular set of
;; pre-Gified functions.


;; (defthm gobjectp-nth-gobject-listp
;;   (implies (gobject-listp lst)
;;            (gobjectp (nth n lst)))
;;   :hints(("Goal" :in-theory (enable gobject-listp))))

(defun glcp-predef-cases-fn (names world)
  (declare (Xargs :mode :program))
  (if (atom names)
      `((t (let ((hyp (lbfr-hyp-fix hyp)))
             (mv nil nil hyp))))
    (cons `(,(car names)
            (b* (((gret res)
                  (glr ,(car names)
                       ,@(make-list-of-nths
                          'actuals 0
                          (len (wgetprop (car names) 'formals)))
                       hyp clk config bvar-db state)))
            (mv t res hyp)))
    (glcp-predef-cases-fn (cdr names) world))))




(defun fns-to-calls (fns world)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (cons (cons (car fns)
                (wgetprop (car fns) 'formals))
    (fns-to-calls (cdr fns) world))))











(defthmd gl-eval-car-cdr-of-gobj-listp
  (implies (gobj-listp x)
           (and (equal (car (generic-geval x env))
                       (generic-geval (car x) env))
                (equal (cdr (generic-geval x env))
                       (generic-geval (cdr x) env))))
  :hints (("goal" :expand ((:with generic-geval (generic-geval x env)))
           :in-theory (e/d* (gobj-listp)
                            (general-consp-car-correct
                             general-consp-cdr-correct)))))

;; (defthmd gl-eval-car-gobjectp
;;   (implies (consp x)
;;            (equal (generic-geval x env)
;;                   (cons (generic-geval (car x) env)
;;                         (generic-geval (cdr x) env))))
;;   :hints (("goal" :expand ((generic-geval x env))
;;            :in-theory (enable gobjectp-car-impl-not-g-types))))

(defthmd gl-eval-of-nil
  (equal (generic-geval nil env) nil))



(defthm gl-eval-consp-when-gobj-listp
  (implies (gobj-listp x)
           (equal (consp (generic-geval x env))
                  (consp x)))
  :hints (("goal" :expand ((:with generic-geval (generic-geval x env))
                           (gobj-listp x))
           :in-theory (e/d (gobj-listp)
                           (general-consp-car-correct
                            general-consp-cdr-correct)))))


;; (defthmd nth-open-constant-idx
;;   (implies (syntaxp (quotep n))
;;            (equal (nth n x)
;;            (if (zp n)
;;                (car x)
;;              (nth (1- n) (cdr x)))))
;;   :hints(("Goal" :in-theory (enable nth))))

;; (defthm open-car-kwote-lst
;;   (equal (car (acl2::kwote-lst lst))
;;          (and (consp lst) (acl2::kwote (car lst)))))

;; (defthm open-cdr-kwote-lst
;;   (equal (cdr (acl2::kwote-lst lst))
;;          (acl2::kwote-lst (cdr lst))))

;; (defthm gobj-listp-cdr
;;   (implies (gobj-listp x)
;;            (gobj-listp (cdr x)))
;;   :hints(("Goal" :in-theory (enable gobj-listp))))





;; Look for a g-evaluator whose corresponding apply function
;; recognizes all existing Gified functions.
(defun find-current-geval1 (eval-pairs gfns apply-table)
  (declare (xargs :mode :program))
  (if (atom eval-pairs)
      nil
    (b* ((apply (cdar eval-pairs))
         (apply-list (cdr (assoc-eq apply apply-table))))
      (if (acl2::hons-subset gfns apply-list)
          (caar eval-pairs)
        (find-current-geval1 (cdr eval-pairs) gfns apply-table)))))

(defun find-current-geval (world)
  (declare (xargs :mode :program))
  (find-current-geval1
   (table-alist 'eval-g-table world)
   (strip-cars (table-alist 'gl-function-info world))
   (table-alist 'g-apply-table world)))

(defun filter-recursive-fns (fns world)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (let ((rest (filter-recursive-fns (cdr fns) world)))
      (if (fgetprop (car fns) 'recursivep nil world)
          (cons (car fns) rest)
        rest))))

;; These are functions that seem particularly necessary for interpreters to be
;; able to execute directly.
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced several names by their "-equal" counterparts).]
(defconst *exec-fns*
  #!ACL2
  '(mod-expt
    header
    search-fn
    wormhole1
    len
    nonnegative-integer-quotient
    boole$
    strip-cdrs
    strip-cars
    may-need-slashes-fn
    alphorder
    nthcdr
    last
    revappend
    butlast
    string
    member-equal
    mod
    round
    remove-equal
    remove-duplicates-equal
    logcount
    expt
    subsetp-equal
    substitute
    position-equal
    string-equal
    string<
    string>
    string<=
    string>=
    string-upcase
    string-downcase
    keywordp
    char
    subst
    sublis
    assoc-equal
    rassoc-equal
    nth
    subseq
    length
    reverse
    standard-char-p
    alpha-char-p
    upper-case-p
    lower-case-p
    char<
    char>
    char<=
    char>=
    char-equal
    char-upcase
    char-downcase
    char-code
    code-char
    unary-/
    numerator
    denominator
    intern-in-package-of-symbol
    fmt-to-comment-window
    fmt-to-comment-window!))


(defconst *forbidden-apply-functions*
  '(return-last acl2::wormhole-eval))




(add-clause-proc-exec-fns *exec-fns*)
(forbid-clause-proc-exec-fns *forbidden-apply-functions*)


(defun interp-term-fnname (clause-proc)
  (incat clause-proc (symbol-name clause-proc) "-INTERP-TERM"))

(defun collect-non-fns (fns world)
  (if (atom fns)
      nil
    (if (eq (wgetprop (car fns) 'formals :none) :none)
        (cons (car fns)
              (collect-non-fns (cdr fns) world))
      (collect-non-fns (cdr fns) world))))

(defthm gobj-listp-true-listp
  (implies (gobj-listp x)
           (true-listp x))
  :hints(("Goal" :in-theory (enable gobj-listp)))
  :rule-classes :forward-chaining)


(defthm gobj-depends-on-of-nth
  (implies (not (gobj-list-depends-on k p x))
           (not (gobj-depends-on k p (nth n x))))
  :hints(("Goal" :in-theory (enable nth gobj-list-depends-on))))

(defthm gobj-depends-on-of-nil
  (not (gobj-depends-on k p nil)))





(defun def-gl-clause-processor-fn
  (clause-proc output state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((world (w state))
       ;; (current-geval (find-current-geval world))
       (geval ;;(or current-geval
        (incat clause-proc (symbol-name clause-proc) "-GEVAL"))
       (geval-ev ;;(or current-geval
        (incat clause-proc (symbol-name clause-proc) "-GEVAL-EV"))
       (geval-list (incat clause-proc (symbol-name clause-proc) "-GEVAL-LIST"))
       (geval-ev-lst ;;(or current-geval
        (incat clause-proc (symbol-name clause-proc) "-GEVAL-EV-LST"))
       (run-gified (incat clause-proc (symbol-name clause-proc) "-RUN-GIFIED"))
       (g-fns (strip-cars (table-alist 'gl-function-info world)))
       (ev (incat clause-proc (symbol-name geval) "-EV"))
       (ev-lst (incat clause-proc (symbol-name geval) "-EV-LST"))
       (ev-rules (incat clause-proc (symbol-name geval) "-EV-RULES"))
       (falsify (incat clause-proc (symbol-name geval) "-EV-FALSIFY"))
       (badguy (incat clause-proc (symbol-name geval)
                      "-EV-META-EXTRACT-GLOBAL-BADGUY"))
       (meta-facts
        (incat clause-proc (symbol-name geval) "-EV-META-EXTRACT-GLOBAL-FACTS"))
       (ctrex-thm (incat clause-proc (symbol-name geval)
                         "-EV-FALSIFY-COUNTEREXAMPLE"))
       (f-i-thm (incat geval (symbol-name geval)
                       "-IS-FUNCTIONAL-INST-OF-GENERIC-GEVAL-FOR-GL-CLAUSE-PROC"))
       (run-gified-correct
        (incat run-gified (symbol-name run-gified) "-CORRECT"))
       (run-gified-deps
        (incat run-gified (symbol-name run-gified) "-DEPS"))
       (interp-term
        (incat clause-proc (symbol-name clause-proc) "-INTERP-TERM"))
       ;; (run-parametrized
       ;;  (incat clause-proc (symbol-name clause-proc) "-RUN-PARAMETRIZED"))
       ;; (run-cases
       ;;  (incat clause-proc (symbol-name clause-proc) "-RUN-CASES"))
       (subst (glcp-name-subst clause-proc))
       (fn-names (strip-cdrs subst))
       (generic-subst (glcp-name-subst 'glcp-generic))
       (fi-subst (pairlis$ (strip-cdrs generic-subst)
                           (pairlis$ fn-names nil)))

       ;; (subst-names (append '(run-gified
       ;;                        geval
       ;;                        geval-list
       ;;                        geval-ev
       ;;                        geval-ev-lst
       ;;                        geval-ev-falsify
       ;;                        geval-ev-meta-extract-global-badguy)
       ;;                      (remove 'clause-proc *glcp-fnnames*)))
       ;; (fn-names (cons clause-proc (glcp-put-name-each clause-proc subst-names)))
       ;; (subst (pairlis$ (cons 'clause-proc subst-names) fn-names))
       ;; (fi-subst (pairlis$ (cons 'glcp-generic (glcp-put-name-each 'glcp-generic subst-names))
       ;;                     (pairlis$ fn-names nil)))
       (f-i-lemmas (incat clause-proc (symbol-name clause-proc)
                          "-FUNCTIONAL-INSTANCE-LEMMAS"))
       (correct-thm (incat clause-proc (symbol-name clause-proc) "-CORRECT")))
    `(with-output
       ,@output
       (encapsulate
         nil
         (set-state-ok t)
         (set-ignore-ok t)
         (set-irrelevant-formals-ok t)

         (local (in-theory (disable (tau-system))))

         ;; ,@(if current-geval
         ;;       nil
         (make-geval ,geval nil
                     :output nil)
         (encapsulate nil
           (set-case-split-limitations '(1 1))
           (defun ,run-gified
             (fn actuals hyp clk config bvar-db state)
             (declare (xargs :guard (and (symbolp fn)
                                         (true-listp actuals)
                                         (glcp-config-p config)
                                         (natp clk))
                             :verify-guards nil
                             :stobjs (hyp bvar-db state))
                      (ignorable state))
             (case fn
               . ,(glcp-predef-cases-fn
                   (remove 'if g-fns) world))))



         ;; ;; make the evaluator, falsifier
         ;; (local (defun dummy-label-for-make-evaluator-fn () nil))
         ;; (acl2::defevaluator-fast
         ;;  ,ev ,ev-lst
         ;;  ,(fns-to-calls
         ;;    (append `(if gl-cp-hint shape-spec-obj-in-range
         ;;               return-last use-by-hint equal acl2::typespec-check implies iff
         ;;               not cons gl-aside gl-ignore gl-error)
         ;;            (set-difference-eq
         ;;             g-fns
         ;;             `(if gl-cp-hint shape-spec-obj-in-range
         ;;                return-last use-by-hint equal not cons
         ;;                ,geval gl-aside gl-ignore gl-error)))
         ;;    world)
         ;;  :namedp t)
         ;; (local (def-ruleset! ,constraints
         ;;          (set-difference-theories
         ;;           (current-theory :here)
         ;;           (current-theory 'dummy-label-for-make-evaluator-fn))))
         (acl2::def-meta-extract ,ev ,ev-lst)
         ;; (defchoose ,falsify (a) (x)
         ;;   (not (,ev x a)))
         (local (defthm ,ctrex-thm
                  (implies (not (,ev x a))
                           (not (,ev x (,falsify x))))
                  :hints (("goal" :use ,falsify))))


         ;; Define the interpreter mutual-recursion, the
         ;; run-parametrized and run-cases functions, and the clause proc.
         ,@(sublis subst (list *glcp-interp-template*
                               *glcp-clause-proc-template*))

         ;; Prep for the run-gified correctness and gobjectp theorems
         (local
          (progn
            (eval-g-prove-f-i ,f-i-thm ,geval generic-geval)
            (eval-g-functional-instance
             gl-eval-car-cdr-of-gobj-listp ,geval generic-geval)
            (eval-g-functional-instance
             gl-eval-consp-when-gobj-listp ,geval generic-geval)
            (eval-g-functional-instance
             gl-eval-of-nil ,geval generic-geval)
            (eval-g-functional-instance
             general-concrete-obj-correct ,geval generic-geval)

            (deflabel run-gified-hyp-cong-checkpoint)
            (def-hyp-congruence ,run-gified)
            (def-ruleset! run-gified-congruences
              (set-difference-theories
               (current-theory :here)
               (current-theory 'run-gified-hyp-cong-checkpoint)))

            ;; Prove correctness of run-gified
            (defthm ,run-gified-deps
              (implies (not (gobj-list-depends-on k p actuals))
                       (not (gobj-depends-on
                             k p (mv-nth 1 (,run-gified
                                            fn actuals hyp clk config bvar-db state)))))
              :hints(("Goal" :in-theory (append '(gobj-depends-on-of-nth
                                                  gobj-depends-on-of-nil
                                                  ,run-gified)
                                                (strip-cdrs
                                                 (table-alist
                                                  'sym-counterpart-dep-thms
                                                  world))))))

            ;; Prove correctness of run-gified
            (defthm ,run-gified-correct
              (implies (and (bfr-hyp-eval hyp (car env))
                            (mv-nth 0 (,run-gified
                                       fn actuals hyp clk config bvar-db state)))
                       (equal (,geval (mv-nth 1 (,run-gified
                                                 fn actuals hyp clk config bvar-db state))
                                      env)
                              (,ev (cons fn (acl2::kwote-lst
                                             (,geval-list actuals env))) nil)))
              :hints (("goal" :clause-processor
                       (run-gified-clause-proc
                        clause
                        ',(f-i-thmname 'gl-eval-of-nil geval)
                        state))
                      (use-by-computed-hint clause)))

            (in-theory (disable ,run-gified))

            ;; Prep to prove the guards of the interpreter and the correctness of
            ;; the clause processor.
            (eval-g-functional-instance shape-spec-to-gobj-eval-env
                                        ,geval generic-geval)
            (eval-g-functional-instance mk-g-boolean-correct
                                        ,geval generic-geval)
            (eval-g-functional-instance
             generic-geval-gl-cons ,geval generic-geval)

            (eval-g-functional-instance
             gobj-to-param-space-correct ,geval generic-geval)

            (eval-g-functional-instance
             generic-geval-non-cons ,geval generic-geval)

            (def-ruleset! ,f-i-lemmas
              (append '(car-cons cdr-cons)
                      ;; (let ((constr (acl2::ruleset ',constraints)))
                      ;;   (nthcdr (- (len constr) 18) constr))
                      '(,ctrex-thm
                        ,run-gified-correct
                        ,run-gified-deps
                        (:ruleset run-gified-congruences)
                        ;; ,apply-concrete-lemma
                        ;; ,apply-concrete-state
                        ,(f-i-thmname 'generic-geval-gl-cons geval)
                        (:type-prescription ,run-gified)
                        ;; (:type-prescription ,apply-concrete)
                        ;; ,(f-i-thmname 'gobj-ite-merge-correct geval)
                        ;; ,(f-i-thmname 'gtests-nonnil-correct geval)
                        ;; ,(f-i-thmname 'gtests-obj-correct geval)
                        ,(f-i-thmname 'shape-spec-to-gobj-eval-env geval)
                        ,(f-i-thmname 'mk-g-boolean-correct geval)
                        ,(f-i-thmname 'mk-g-concrete-correct geval)
                        ,(f-i-thmname 'g-concrete-quote-correct geval)
                        ,(f-i-thmname 'mk-g-ite-correct geval)
                        ,(f-i-thmname 'generic-geval-non-cons geval)
                        ,(f-i-thmname 'gobj-to-param-space-correct geval)
                        ,(f-i-thmname 'general-concrete-obj-correct geval))))))

         (verify-guards ,run-gified
           :hints (("goal" :in-theory
                    (e/d** ((:forward-chaining gobj-listp-true-listp)
                            hyp-p
                            bfr-hyp-fix-when-hyp$ap))
                    :do-not '(preprocess))))
         ;; Verify guards of the interpreter.
         (local (in-theory nil))
         (verify-guards
           ,interp-term
           :hints (("goal" :by
                    (:functional-instance
                     glcp-generic-interp-guards-ok
                     . ,fi-subst
                     ;; (glcp-generic-apply-concrete ,apply-concrete)
                     ;; (glcp-generic-apply-concrete-guard-wrapper ,apply-concrete)
                     )
                    :do-not '(preprocess simplify)
                    :in-theory (e/d** ((:ruleset ,f-i-lemmas)))
                    :do-not-induct t)
                   '(:clause-processor dumb-clausify-cp)
                   (let ((term (car (last clause))))
                     (case-match term
                       ;; prevent the next pattern from matching run-gified congruences:
                       (('equal (fn . &) (fn . &)) '(:do-not nil))
                       (('equal (fn . args) . &)
                        (if (member fn ',(set-difference-eq fn-names
                                                            (list geval-ev
                                                                  geval-ev-lst)))
                            `(:by ,fn
                              :do-not nil)
                          '(:do-not nil)))
                       (& '(:do-not nil))))
                   (and stable-under-simplificationp
                        '(:in-theory (e/d** ((:ruleset ,f-i-lemmas)
                                             (:ruleset ,ev-rules)))))
                   (and stable-under-simplificationp
                        '(:in-theory (e/d** ((:ruleset ,f-i-lemmas)
                                             (:ruleset ,ev-rules)
                                             ;; ,apply-concrete
                                             ,(incat ev (symbol-name ev)
                                                     "-OF-FNCALL-ARGS")
                                             ,(incat ev (symbol-name ev)
                                                     "-OF-NONSYMBOL-ATOM")
                                             ,(incat ev (symbol-name ev)
                                                     "-OF-BAD-FNCALL")))))))

         ;; Prove correctness of the clause processor.
         (defthm ,correct-thm
           (implies (and (pseudo-term-listp clause)
                         (alistp alist)
                         (,meta-facts)
                         (,ev (conjoin-clauses
                               (acl2::clauses-result
                                (,clause-proc clause hints interp-st state)))
                              (,falsify
                               (conjoin-clauses
                                (acl2::clauses-result
                                 (,clause-proc clause hints interp-st state))))))
                    (,ev (disjoin clause) alist))
           :hints (("goal" :do-not-induct t
                    :in-theory (e/d** (,ctrex-thm))
                    :do-not '(preprocess)
                    :by (:functional-instance
                         glcp-generic-correct
                         . ,fi-subst))
                   '(:clause-processor dumb-clausify-cp)
                   (case-match clause
                     ((('equal (fn . args) . &))
                      (and (member fn ',(set-difference-eq fn-names
                                                           (list geval-ev
                                                                 geval-ev-lst)))
                           `(:by ,fn)))
                     (((ev ('acl2::meta-extract-global-fact+ . &)
                           . &)
                       ('not (ev ('acl2::meta-extract-global-fact+ . &)
                                 . &)))
                      '(:use ,badguy :do-not nil))
                     ((('true-listp . &) . &)
                      '(:use ,badguy :do-not nil))))
           :otf-flg t
           :rule-classes :clause-processor)

         (table latest-greatest-gl-clause-proc nil ',subst :clear)))))





(defsection def-gl-clause-processor
  :parents (reference)
  :short "Define a GL clause processor with a given set of built-in symbolic
  counterparts."

  :long "<p>Usage:</p>

@({
 (def-gl-clause-processor my-gl-clause-processor
   :output with-output-settings)
})

<p>The above form defines a GL clause processor function named
my-gl-clause-processor.  This clause processor is defined so that it can
execute all existing symbolic counterpart functions.</p>

<p>If one adds symbolic counterpart functions, either by hand-coding them,
using make-g-world, or including books that add them, one will need to define a
new GL clause processor.</p>

<p>Each GL clause processor has an associated sets of functions that it can
directly execute symbolically.  DEF-GL-CLAUSE-PROCESSOR makes a new processor
that can execute the full set of existing symbolic counterparts. (Symbolic
counterparts may be defined by hand or using make-g-world.)</p>

<p>It used to be the case that the clause processor also had a fixed set of
functions it could execute concretely.  That is no longer the case.  We still
accept the old form of def-gl-clause-processor, which takes an additional
argument after the name of the clause processor and before the :output keyword
 (if any).  However, this is deprecated and a message will be printed saying so.
</p>

<p>See @(see def-gl-thm) and @(see gl-hint) for information on using the GL
clause processor to prove theorems.</p>"

  (defmacro def-gl-clause-processor
    (name &rest rest-args
          ;; apply-fns &key (output
          ;;                 '(:off (warning warning! observation prove
          ;;                                 event summary proof-tree
          ;;                                 acl2::history)
          ;;                        :gag-mode nil))
          ;; top-apply-fns
          ;; include-nonrec
          )
    (b* (((mv oldp keys)
          (if (or (not rest-args)
                  (keywordp (car rest-args)))
              (mv nil rest-args)
            (mv t (cdr rest-args))))
         (- (and oldp
                 (cw "DEPRECATED (def-gl-clause-proc): Def-gl-clause-proc now ~
                      takes fewer arguments than it used to; in particular, ~
                      the old APPLY-FNS argument is now ignored.  See :doc ~
                      def-gl-clause-proc for the new syntax.~%")))
         (output-look (assoc-keyword :output keys))
         (output (if output-look
                     (cadr output-look)
                   '(:off (warning warning! observation prove
                                   event summary proof-tree
                                   acl2::history)
                          :gag-mode nil))))
      `(make-event
        (def-gl-clause-processor-fn
          ',name ',output state)))))




(defun add-var-bindings (vars acc)
  (declare (xargs :mode :program))
  (if (atom vars)
      acc
    (add-var-bindings (cdr vars)
    (cons (list (car vars) (g-var (car vars)))
          acc))))

(defun add-param-var-bindings (vars param-bindings)
  (declare (xargs :mode :program))
  (if (atom param-bindings)
      nil
    (b* ((bindings (cadar param-bindings))
         (missing (set-difference-eq vars (strip-cars bindings))))
      (cons (list (caar param-bindings)
                  (add-var-bindings missing bindings))
            (add-param-var-bindings vars (cdr param-bindings))))))


(defun glcp-remove-and-replace (hints)
  (declare (xargs :mode :program))
  `(:computed-hint-replacement
    ,hints
    :clause-processor acl2::remove-first-hyp-cp))

(defun glcp-combine-hints (call cov-hints hyp-hints res-hints casesplit-hints)
  (declare (xargs :mode :program))
  `(:computed-hint-replacement
    ((use-by-computed-hint clause)
     (case-match clause
       ((('not ('gl-cp-hint ('quote name) . &) . &) . rest)
        (case name
          (coverage
           (prog2$ (obs-cw "Now proving coverage~%")
                   (glcp-remove-and-replace ',cov-hints)))
          (result
           (prog2$ (obs-cw "Now proving result (should be trivial)~%")
                   ,(if res-hints
                        `(glcp-remove-and-replace ',res-hints)
                      '(case-match rest
                         ((eval . &)
                          (glcp-remove-and-replace
                           `('(:in-theory (enable ,eval)))))))))
          (param
           (prog2$ (obs-cw "Now proving hyp coverage~%")
                   ,(and hyp-hints
                         `(glcp-remove-and-replace ',hyp-hints))))
          (casesplit
           (prog2$ (obs-cw "Now proving casesplit coverage~%")
                   ,(and casesplit-hints
                         `(glcp-remove-and-replace ',casesplit-hints))))))))
    :clause-processor ,call))



(defmacro glcp-coverage-default-hint  (&key do-not-expand cov-theory-add def-alist)
  `'(:computed-hint-replacement
     ((and stable-under-simplificationp
           (let ,'((last (car (last clause))))
             (case-match last
               (,'('gl::shape-spec-obj-in-range & x . &)
                `(:computed-hint-replacement
                  ('(:in-theory
                     (union-theories
                      ,',cov-theory-add
                      (e/d** ((:ruleset shape-spec-obj-in-range-open)))))
                   (acl2::structural-decomp-hint-fast
                    clause ',x stable-under-simplificationp state
                    (append ,',def-alist (table-alist 'acl2::structural-decomp-defs (w state)))
                    (list* 'binary-and* 'booleanp ,',do-not-expand)))
                  :clause-processor (acl2::remove-irrel-cp clause ',x)))))))
     :in-theory
     (union-theories
      ,cov-theory-add
      (e/d** ((:ruleset shape-spec-obj-in-range-backchain))))
     :do-not-induct t))

(defun glcp-coverage-hints (do-not-expand cov-theory-add cov-hints
                                          cov-hints-position)
  (b* ((cov-hint-defaults (and (not (eq cov-hints-position :replace))
                               `((glcp-coverage-default-hint
                                  :do-not-expand ,do-not-expand
                                  :cov-theory-add ,cov-theory-add))))
       (cov-hint-fail '((and stable-under-simplificationp
                             (cw "
**********************************************************************
ERROR: Coverage proof appears to have failed.
See :DOC GL::COVERAGE-PROOFS.
**********************************************************************
")))))
    (case cov-hints-position
      (:replace cov-hints)
      (:first (append cov-hints
                      cov-hint-defaults
                      cov-hint-fail))
      (t (append cov-hint-defaults
                 cov-hints
                 cov-hint-fail)))))


(defmacro latest-gl-clause-proc ()
  '(cdr (assoc 'clause-proc (table-alist
                             'latest-greatest-gl-clause-proc
                             (w state)))))


;; BOZO move to da-base.lisp

(local (defun aggregate-alist-args-from-default-map (map)
         (if (atom map)
             nil
           (cons `(b* ((look (assoc ',(intern$ (symbol-name (caar map)) "KEYWORD") alist)))
                    (if look (cdr look) ,(cdar map)))
                 (aggregate-alist-args-from-default-map (cdr map))))))

(make-event
 (b* (((std::agginfo agg) (std::get-aggregate 'glcp-config (w state)))
      (default-map (pairlis$ (std::formallist->names agg.efields)
                             (std::formallist->defaults agg.efields))))
   `(defun make-glcp-config-from-alist (alist)
      (declare (xargs :guard (alistp alist)))
      (ec-call
       (glcp-config . ,(aggregate-alist-args-from-default-map default-map))))))

(defun keywordify (x)
  (declare (xargs :guard (symbolp x)))
  (intern$ (symbol-name x) "KEYWORD"))

(defun keywordify-lst (x)
  (declare (xargs :guard (Symbol-listp x)))
  (if (atom x)
      nil
    (cons (keywordify (car x))
          (keywordify-lst (cdr x)))))


(defun gl-hint-config-vars-getargs (config-vars)
  (if (atom config-vars)
      nil
    (cons `(std::getarg ,(keywordify (caar config-vars)) ,(cdar config-vars) kwd-alist)
          (gl-hint-config-vars-getargs (cdr config-vars)))))


;; arg names . default values
(defconst *gl-hint-common-args*
  '((clause-proc)
    (do-not-expand)
    (cov-theory-add)
    (cov-hints)
    (cov-hints-position)
    (acl2::hyp . ''t)
    (concl)
    (test-side-goals)
    (hyp-hints)
    (result-hints)
    (case-split-hints)))

(defconst *gl-hint-common-form-args*
  '((rule-classes . :rewrite)
    (no-defthm)))

(defconst *gl-hint-param-args*
  '((cov-bindings)
    (param-bindings)
    (param-hyp)))

(defconst *gl-hint-nonparam-args*
  '((g-bindings . cov-bindings)))

(defconst *gl-hint-nonconfig-args*
  (append *gl-hint-common-args*
          *gl-hint-param-args*
          ;; BOZO this must come after param args because of the default for g-bindings
          *gl-hint-nonparam-args*))

(make-event
 `(defconst *gl-hint-permissible-keywords*
    (keywordify-lst (union-eq (strip-cars *gl-hint-nonconfig-args*)
                              (strip-cars *gl-hint-common-form-args*)
                              ',(std::formallist->names
                                 (std::agginfo->efields (std::get-aggregate 'glcp-config (w state))))))))

(defconst *gl-hint-param-permissible-keywords*
  (set-difference-eq *gl-hint-permissible-keywords*
                     (keywordify-lst (strip-cars *gl-hint-nonparam-args*))))

(defconst *gl-hint-nonparam-permissible-keywords*
  (set-difference-eq *gl-hint-permissible-keywords*
                     (keywordify-lst (strip-cars *gl-hint-param-args*))))

(defconst *gl-hint-evaluated-args*
  '(:g-bindings
    :cov-bindings
    :param-bindings
    :hyp
    :param-hyp
    :concl
    :hyp-clk
    :concl-clk
    :n-counterexamples
    :abort-indeterminate
    :abort-ctrex
    :exec-ctrex
    :abort-vacuous
    :prof-enabledp
    :case-split-override
    :test-side-goals))

(defconst *gl-thm-quoted-args*
  '(:hyp :concl :param-hyp :term-level-counterexample-scheme))

(defun gl-hint-make-config-var-inner-bindings (vars)
  (if (atom vars)
      nil
    (cons (if (member (keywordify (car vars)) *gl-hint-evaluated-args*)
              ;; argh horrible
              ``(,',(car vars) ,,(car vars))
            ``(,',(car vars) ',,(car vars)))
          (gl-hint-make-config-var-inner-bindings (cdr vars)))))


(defun gl-thm-quote-kwd-alist-args (quote-args kwd-alist)
  (if (atom quote-args)
      kwd-alist
    (let ((look (assoc (car quote-args) kwd-alist)))
      (if look
          (gl-thm-quote-kwd-alist-args
           (cdr quote-args)
           (cons (cons (car look) (list 'quote (cdr look))) kwd-alist))
        (gl-thm-quote-kwd-alist-args (cdr quote-args) kwd-alist)))))


(make-event
  (b* ((config-vars *gl-hint-nonconfig-args*)
       (config-vars-bindings-outer (pairlis$ (strip-cars config-vars)
                                       (pairlis$ (gl-hint-config-vars-getargs config-vars) nil)))
       (config-vars-bindings-inner (cons 'list (gl-hint-make-config-var-inner-bindings (remove 'cov-bindings (strip-cars config-vars))))))

    `(defun gl-hint-fn (kwd-alist)
       (declare (xargs :mode :program))
       (b* ,config-vars-bindings-outer
         `(b* ((kwd-alist ',kwd-alist)
               
               ;; (g-bindings ,g-bindings)
               ;; (param-hyp ',param-hyp)
               ;; ((er overrides)
               ;;  (preferred-defs-to-overrides
               ;;   (table-alist 'preferred-defs (w state)) state))

               ;;,@config-vars-bindings
               
               ,@,config-vars-bindings-inner

               (clause-proc (or clause-proc  (latest-gl-clause-proc)))
               (kwd-alist (cons (cons :clause-proc clause-proc) kwd-alist))

               (config (make-glcp-config-from-alist kwd-alist))

               (cov-hints (glcp-coverage-hints
                           do-not-expand cov-theory-add cov-hints cov-hints-position))
               ((er trhyp)
                (acl2::translate acl2::hyp t t nil 'gl-hint-fn (w state) state))
               ((er trparam)
                (acl2::translate param-hyp t t nil 'gl-hint-fn (w state)
                                 state))
               ((er trconcl)
                (acl2::translate concl t t nil 'gl-hint-fn (w state) state))
               (vars (simple-term-vars trconcl))
               (missing-vars (set-difference-eq vars (strip-cars g-bindings)))
               (- (and missing-vars
                       (let ((msg (acl2::msg "~
The following variables are present in the theorem but have no symbolic object ~
bindings:
~x0~%" missing-vars)))
                         ;; (if missing-vars-ok
                         (cw "****  WARNING ****~%~@0~%" msg)
                         ;;  (er hard? 'gl-hint "~@0" msg)
                         )))
               (bindings
                (add-var-bindings missing-vars
                                  g-bindings))
               (param-bindings (add-param-var-bindings vars param-bindings))
               (call `(,(if test-side-goals 'glcp-side-goals-clause-proc clause-proc)
                       clause (list ',bindings ',param-bindings ',trhyp
                                    ',trparam ',trconcl ',concl ',config)
                       interp-st state)))
            (value (glcp-combine-hints call cov-hints hyp-hints result-hints case-split-hints)))))))




(defsection gl-hint
  :parents (reference)
  :short "Try to prove a goal using GL symbolic simulation."
  :long "<p>Usage, as a <see topic='@(url acl2::computed-hints)'>computed hint</see>:</p>

@({
 (gl-hint my-gl-clause-processor
         :bindings `((a ,(g-number (list (mk-number-list 1 1 9))))
                     (b ,(g-boolean 0)))
         :hyp '(bvecp a 8)
         :coverage-hints ('(:expand ((bvecp a 8)))))
})

<p>The above hint causes an attempt to apply the clause processor
my-gl-clause-processor to the current clause.  Such a clause processor must be
created using @(see def-gl-clause-processor).  One such clause processor,
@('glcp'), is predefined in the GL system.  Various keyword arguments control
the symbolic simulation and auxilliary proofs.</p>

<p>The full interface is as follows, with default values and brief
descriptions of each keyword argument:</p>

@({
 (gl-hint clause-processor-name

          ;; bindings of variables to symbolic object specs
          :bindings                <required>

          ;; maximum recursion depth
          :clk                     1000000

          ;; hypothesis of the theorem
          :hyp                     t

          ;; conclusion of the theorem
          :concl                   nil

          ;; hints for proving coverage
          :cov-hints               nil
          :cov-hints-position      nil
          :cov-theory-add          nil
          :do-not-expand           nil

          ;; number of counterexamples to print
          :n-counterexamples       3

          ;; abort if symbolic simulation yields a result with
          ;; indeterminate truth value.
          :abort-indeterminate     t

          ;; abort as soon as a counterexample is discovered.
          :abort-ctrex             t

          ;; execute the conclusion on each counterexample (turn off if non-executable)
          :exec-ctrex              t

          ;; abort if a hypothesis is discovered to be unsatisfiable.
          :abort-vacuous           t

          ;; enable accumulated-persistence-like rule profiling
          :prof-enabledp           nil

          ;; To perform case-splitting, set this argument:
          :param-bindings          nil

          ;; Ignored unless case-splitting:
          :param-hyp               nil
          :run-before-cases        nil
          :run-after-cases         nil)
})

<p>The keyword arguments to @('gl-hint') are similar to ones for the macros
@(see def-gl-thm) and @(see def-gl-param-thm), and are documented there.</p>"

  (defmacro gl-hint (&rest keys)
    (b* (((mv kwd-alist rest)
          (std::extract-keywords 'gl-hint *gl-hint-permissible-keywords* keys nil))
         ((when rest) (er hard? 'gl-hint "Non-keyword args to gl-hint: ~x0~%" rest)))
      (gl-hint-fn kwd-alist))))

(defmacro gl-hint-alist (kwd-alist)
  (gl-hint-fn kwd-alist))



;; just wraps with-output around all this stuff and invisiblifies the return value
(defmacro without-waterfall-parallelism (form)
  `(with-output :off :all :stack :push
     (progn
       (acl2::without-waterfall-parallelism
         (with-output :stack :pop
           ,form))
       (value-triple :invisible))))

(defun def-gl-thm-form (name kwd-alist)
  (Declare (Xargs :mode :program))
  (b* ((test-side-goals (std::getarg :test-side-goals nil kwd-alist))
       (acl2::hyp (std::getarg :hyp t kwd-alist))
       (concl (std::getarg :concl nil kwd-alist))
       (no-defthm (std::getarg :no-defthm nil kwd-alist))
       (rule-classes (std::getarg :rule-classes :rewrite kwd-alist))
       (kwd-alist (gl-thm-quote-kwd-alist-args *gl-thm-quoted-args* kwd-alist))
       (form `(without-waterfall-parallelism
                (defthm ,name
                  ,(if test-side-goals t `(implies ,acl2::hyp ,concl))
                  :hints ((gl-hint-alist ,kwd-alist))
                  . ,(if (or test-side-goals no-defthm)
                         '(:rule-classes nil)
                       `(:rule-classes ,rule-classes))))))
    (if (or test-side-goals no-defthm)
        `(with-output
           :off :all :stack :push
           (make-event (er-progn (with-output :stack :pop ,form)
                                 (value '(value-triple 'ok)))))
      form)))


(defun def-gl-thm-fn
  (name args)
  (declare (xargs :mode :program))
  (b* (((mv kwd-alist rest)
        (std::extract-keywords 'def-gl-thm *gl-hint-nonparam-permissible-keywords* args nil))
       ((when rest) (er hard? 'def-gl-thm "Non-keyword args to def-gl-thm: ~x0~%" rest))
       ((unless (and (assoc :hyp kwd-alist)
                     (assoc :concl kwd-alist)
                     (assoc :g-bindings kwd-alist)))
        (er hard 'def-gl-thm
            "The keyword arguments HYP, CONCL, and G-BINDINGS must be provided ~
in DEF-GL-THM.~%")))
    (def-gl-thm-form name kwd-alist)))
       






(defsection def-gl-thm
  :parents (reference)
  :short "Prove a theorem using GL symbolic simulation."
  :long "<p>Usage:</p>

@({
 (def-gl-thm <theorem-name>
   :hyp <hypothesis term>
   :concl <conclusion term>
   :g-bindings <shape spec binding alist>

   :rule-classes <rule classes expression>

   :hyp-clk <number> :concl-clk <number>
   :clause-proc <clause processor name>

   :n-counterexamples <number>
   :abort-indeterminate <t or nil>

   ;; Hints for coverage goals:
   :cov-theory-add <theory expression>
   :do-not-expand <list of functions>
   :cov-hints <computed hints>
   :cov-hints-position <:replace, :before, or :after>

   :test-side-goals <t or nil>)
})

<p>This form submits a @(see defthm) event for the theorem</p>

@({(implies <hyp> <concl>)})

<p>and the specified rule-classes, and gives a hint to attempt to prove it by
symbolic execution using a GL clause processor.</p>

<p>Out of the list of keyword arguments recognized by this macro, three are
necessary: @(':hyp'), @(':concl'), and @(':g-bindings').  As noted, the theorem
to be proved takes the form @('(implies <hyp> <concl>)').  The @('hyp') is also
used in proving coverage, explained below.</p>

<p>The @(':g-bindings') must be a term evaluating to an alist formatted as
follows:</p>

@({
 ((<var-name1>  <shape-spec1>)
  (<var-name2>  <shape-spec2>)
  ...)
})

<p>The shape specs must be well-formed as described in @(see shape-specs);
notably, they must not reuse BDD variable numbers or unconstrained variable
names.  Note also that this is not a dotted alist; the shape spec is the @(see
cadr), not the @(see cdr), of each entry.  If any variables mentioned in the
theorem are not bound in this alist, they will be given an unconstrained
variable binding.</p>

<p>The symbolic objects used as the inputs to the symbolic simulation are
obtained by translating each shape spec into a symbolic object.  The hyp is
symbolically executed on these symbolic inputs.  Parametrizing the symbolic
objects by the resulting predicate object yields (absent any @('G-APPLY') or
@('G-VAR') objects) symbolic objects with coverage restricted to only inputs
satisfying the hyp.</p>

<p>Here is a simple example theorem:</p>

@({
 (def-gl-thm commutativity-of-+-up-to-16
    :hyp (and (natp a) (natp b)
              (< a 16) (< b 16))
    :concl (equal (+ a b) (+ b a))
    :g-bindings '((a (:g-number (0 2 4 6 8)))
                  (b (:g-number (1 3 5 7 9)))))
})

<p>This theorem binds its free variables @('a') and @('b') to symbolic numbers
of five bits.  Note that integers are two's-complement, so to represent natural
numbers one needs one more bit than in the unsigned representation.  Therefore,
these shape specs cover negative numbers down to -16 as well as naturals less
than 16.  However, parametrization by the hypotheses will yield symbolic
objects that only cover the specified range.</p>

<p>The coverage obligation for a theorem will be a goal like this:</p>

@({
 (implies <hyp>
          (shape-spec-obj-in-range
           (list <shape-spec1> <shape-spec2> ...)
           (list <var-name1> <var-name2> ...)))
})

<p> In the example above:</p>

@({
 (implies (and (natp a) (natp b)
               (< a 16) (< b 16))
          (shape-spec-obj-in-range
           '((:g-number (0 2 4 6 8)) (:g-number (1 3 5 7 9)))
           (list a b)))
})

<p>It is often convenient to work out the coverage theorem before running the
symbolic simulation, since the symbolic simulation may take a very long time
even when successful.  The keyword argument @(':test-side-goals') may be given
a value of @('T') in order to attempt the coverage proof on its own; if
successful, no theorem will be stored by ACL2, but one can then be fairly sure
that the coverage proof will go through in the real theorem.</p>

<p>Several hints are given by default for proving coverage; see @(see
shape-specs) for details.  The keyword arguments @(':cov-theory-add'),
@(':do-not-expand'), @(':cov-hints'), and @(':cov-hints-position') affect the
coverage proof.</p>

<p>When proof by symbolic simulation fails, the clause processor will print
randomized counterexamples.  The keyword argument @(':n-counterexamples')
determines how many it prints.  The default is 3.  (For SAT-based proofs,
likely only one counterexample is available, so it may print the same
counterexample each time.)</p>

<p>By default, the clause processor will execute conclusion on the
counterexamples that it finds; this is useful for printing debugging
information.  However, sometimes the conclusion is not executable; in that
case, you may turn off execution of counterexamples using @(':exec-ctrex
nil').</p>

<p>A symbolic simulation may result in a symbolic object that can't be
syntactically determined to be non-nil; for example, the result may contain a
@(':G-APPLY') object.  In these situations, the proof attempt will abort, and
an example will be shown of inputs for which the symbolic result's value could
not be determined.  To debug this type of problem, see @(see
false-counterexamples).</p>

<p>The symbolic interpreter and all symbolic counterpart functions take a clock
argument to ensure termination.  The starting clocks for the symbolic
executions of the hyp (for parametrization) and the conclusion may be set using
the keyword arguments @(':hyp-clk') and @(':concl-clk'); the defaults are both
1000000.</p>

<p>The keyword argument @(':clause-proc') can be used to select the clause
processor to be used; see @(see def-gl-clause-processor).  By default, the
latest clause processor introduced is used.  If no @(':clause-proc') keyword
argument is given, then this macro expands to a @(see make-event), which in
turn expands to the @(see defthm) event; otherwise, this expands directly to
the @(see defthm).</p>

<p>The keyword argument @(':rule-classes') can be used to select the
rule-classes for the theorem produced, as in @(see defthm); the default is
@(':rewrite').</p>"

  ;; Define a macro that provides a drop-in replacement for DEF-G-THM and
  ;; uses the new clause processor.
  (defmacro def-gl-thm
    (name &rest args)
    (def-gl-thm-fn name args)))


(defsection gl-thm
  :parents (def-gl-thm)
  :short "Prove a theorem using GL symbolic simulation, but don't store it, like with @(see thm)."
  :long "<p>Exactly the same as @(see def-gl-thm), but does not store the
resulting theorem: @(see def-gl-thm) is to @(see gl-thm) as @(see defthm) is to
@(see thm).  The :rule-classes argument is accepted, but ignored.</p>"

  (defmacro gl-thm
    (name &rest args)
    (def-gl-thm-fn name (list* :no-defthm t args))))




(defun def-gl-param-thm-fn (name args)
  (declare (xargs :mode :program))
  (b* (((mv kwd-alist rest)
        (std::extract-keywords 'def-gl-param-thm *gl-hint-param-permissible-keywords* args nil))
       ((when rest) (er hard? 'def-gl-param-thm "Non-keyword args to def-gl-param-thm: ~x0~%" rest))
       ;; Override default value for abort-vacuous -- the default is t which is
       ;; what we want for def-gl-thm, but we want nil for def-gl-param-thm.
       (kwd-alist (let ((look (assoc :abort-vacuous kwd-alist)))
                    (if look
                        kwd-alist
                      (cons (cons :abort-vacuous nil) kwd-alist))))
       ((unless (and (assoc :hyp kwd-alist)
                     (assoc :param-hyp kwd-alist)
                     (assoc :cov-bindings kwd-alist)
                     (assoc :param-bindings kwd-alist)))
        (er hard 'def-gl-param-thm
            "The keyword arguments HYP, PARAM-HYP, CONCL, COV-BINDINGS, and ~
PARAM-BINDINGS must be provided in DEF-GL-PARAM-THM.~%")))
    (def-gl-thm-form name kwd-alist)))


(defsection def-gl-param-thm
  :parents (reference optimization)
  :short "Prove a theorem using GL symbolic simulation with parametrized
case-splitting."

  :long "<p>Usage:</p>

@({
 (def-gl-param-thm <theorem-name>
   :hyp <hypotheses>
   :concl <conclusion>
   :param-hyp <parametrized hypotheses>
   :cov-bindings <bindings for parametrization coverage>
   :param-bindings <bindings for the individual cases>

   :rule-classes <rule classes expression>

   :hyp-clk <number> :concl-clk <number>
   :clause-proc <clause processor name>

   :n-counterexamples <number>
   :abort-indeterminate <t or nil>
   :run-before-cases <term with side effects>
   :run-after-cases <term with side effects>

   ;; Hints for coverage goals:
   :cov-theory-add <theory expression>
   :do-not-expand <list of functions>
   :cov-hints <computed hints>
   :cov-hints-position <:replace, :before, or :after>

   :test-side-goals <t or nil>)
})

<p>This form submits a @(see defthm) event for the theorem @('(implies <hyp>
<concl>)') and the specified rule classes, and gives a hint to attempt to prove
it using a GL clause processor with parametrized case-splitting.  See @(see
def-gl-thm) for a simpler version that does not do case splitting.</p>

<p>Out of the list of keyword arguments recognized by this macro, five are
necessary: @(':hyp'), @(':concl'), @('param-hyp'), @(':cov-bindings'), and
@(':param-bindings').  As noted, the theorem to be proved takes the form
@('(implies <hyp> <concl>)').  The theorem is split into cases based on the
@('param-hyp'), a term containing some free variables of the theorem and some
additional variables used in case splitting.  Values are assigned to these
variables based on the entries in the @('param-bindings'), an alist of the
following form:</p>

@({
 ((<case-bindings1> <var-bindings1>)
  (<case-bindings2> <var-bindings2>)
  ...)
})

<p>Each of the case-bindings is, in turn, an alist of the following form:</p>

@({
 ((<case-var1> <obj1>)
  (<case-var2> <obj2>)
  ...)
})

<p>and each of the var-bindings is an alist of the following form:</p>

@({
 ((<thm-var1> <shape-spec1>)
  (<thm-var2> <shape-spec2>)
  ...)
})

<p>For each entry in the @('param-bindings'), the @('param-hyp') is
instantiated with the case variables bound to the objects specified in the
entry's case-bindings.  This term gives a hypothesis about the free variables
of the theorem, and the set of these terms generated from the param-bindings
gives the full case-split.  The case split must cover the theorem's hypotheses;
that is, the theorem's hypothesis must imply the disjunction of the case
hypotheses.  To prove this, we symbolically simulate this disjunction using the
shape specs given in the @('cov-bindings'), which are formatted like the
var-bindings above.  Note that this case-split coverage step is not done as
part of @(':test-side-goals'), but it happens first otherwise, so it's easy to
tell if it's successful.</p>

<p>A simple example is as follows:</p>

@({
 (def-gl-param-thm addititive-inverse-for-5-bits
   :hyp (and (integerp n) (<= -16 n) (< n 16))
   :concl (equal (- n n) 0)
   :param-hyp (if sign
                  (< n 0)
                (and (<= 0 n)
                     (equal (logand n 3) lower-bits)))
   :cov-bindings
   '((n (:g-number (0 1 2 5 6))))
   :param-bindings
   '((((sign t) (lower-bits nil)) ((n (:g-number (1 2 3 4 5)))))
     (((sign nil) (lower-bits 0)) ((n (:g-number (0 2 3 4 5)))))
     (((sign nil) (lower-bits 1)) ((n (:g-number (0 1 2 4 5)))))
     (((sign nil) (lower-bits 2)) ((n (:g-number (0 1 2 3 5)))))
     (((sign nil) (lower-bits 3)) ((n (:g-number (0 1 2 3 4)))))))
})

<p>This theorem is proved by symbolic simulation of five cases, in each of
which the param-hyp is assumed with a different setting of the sign and
lower-bits case variables; in one case @('N') is required to be negative, and
in the others it is required to be positive and have a given value on its two
low-order bits.  To show that the case-split is complete, another symbolic
simulation is performed (using the given @(':cov-bindings')) which proves that
the disjunction of the case assumptions is complete; effectively,</p>

@({
 (implies (and (integerp n) (<= -16 n) (< n 16))
          (or (< n 0)
              (and (<= 0 n) (equal (logand n 3) 0))
              (and (<= 0 n) (equal (logand n 3) 1))
              (and (<= 0 n) (equal (logand n 3) 2))
              (and (<= 0 n) (equal (logand n 3) 3))))
})

<p>Most of the remaining keyword arguments to @('DEF-GL-PARAM-THM') are also
available in @(see def-gl-thm) and are documented there.  The rest are as
follows:</p>

<p>@(':RUN-BEFORE-CASES') and @(':RUN-AFTER-CASES') cause a user-specified form to
be run between the parametrized symbolic simulations.  These may use the
variable @('id'), which is bound to the current assignment of the case-splitting
variables.  These can be used to print a message before and after running each
case so that the user can monitor the theorem's progress.</p>

<p>By default, if a counterexample is encountered on any of the cases, the proof
will abort.  Setting @(':ABORT-CTREX') to @('NIL') causes it to go on; the proof
will fail after the clause processor returns because it will produce a goal of
@('NIL').</p>

<p>By default, if any case hypothesis is unsatisfiable, the proof will abort.
Setting @(':ABORT-VACUOUS') to @('NIL') causes it to go on.</p>"

  (defmacro def-gl-param-thm
    (name &rest args)
    (def-gl-param-thm-fn name args)))

(defsection gl-param-thm
  :parents (reference optimization)
  :short "Prove a theorem using GL symbolic simulation with parametrized
case-splitting, without storing the theorem."

  :long "<p>Exactly the same as @(see def-gl-param-thm), but does not store the
resulting theorem: @(see def-gl-param-thm) is to @(see gl-param-thm) as @(see
defthm) is to @(see thm).  The :rule-classes argument is accepted, but
ignored.</p>"

  (defmacro gl-param-thm
    (name &rest args)
    (def-gl-param-thm-fn name (list* :no-defthm t args))))




(defmacro latest-gl-interp ()
  '(cdr (assoc 'interp-term
               (table-alist
                'latest-greatest-gl-clause-proc
                (w state)))))





