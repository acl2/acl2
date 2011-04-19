
(in-package "GL")




(include-book "centaur/misc/defapply" :dir :system)
(include-book "gify")
(local (include-book "gify-thms"))
(include-book "run-gified-cp")
(local (include-book "general-object-thms"))
(include-book "glcp-templates")
(include-book "gl-doc-string")
(include-book "generic-geval")
;; Now that we've proven the correctness of the generic clause processor above,
;; we now define a macro which makes a clause processor for a particular set of
;; pre-Gified functions.


(defthm gobjectp-nth-gobject-listp
  (implies (gobject-listp lst)
           (gobjectp (nth n lst)))
  :hints(("Goal" :in-theory (enable gobject-listp))))

(defun glcp-predef-cases-fn (names world)
  (declare (Xargs :mode :program))
  (if (atom names)
      `((t (mv nil nil)))
    (cons `(,(car names)
            (mv t (glr ,(car names)
                       ,@(make-list-of-nths
                          'actuals 0
                          (len (wgetprop (car names) 'formals)))
                       hyp clk)))
    (glcp-predef-cases-fn (cdr names) world))))




(defun fns-to-calls (fns world)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (cons (cons (car fns)
                (wgetprop (car fns) 'formals))
    (fns-to-calls (cdr fns) world))))











(defthmd gl-eval-car-cdr-of-gobject-listp
  (implies (gobject-listp x)
           (and (equal (car (generic-geval x env))
                       (generic-geval (car x) env))
                (equal (cdr (generic-geval x env))
                       (generic-geval (cdr x) env))))
  :hints (("goal" :expand ((:with generic-geval (generic-geval x env)))
           :in-theory (e/d* (gobjectp-car-impl-not-g-types
                             gobject-listp-impl-gobjectp
                             gobject-listp)
                            (general-consp-car-correct
                             general-consp-cdr-correct)))))

(defthmd gl-eval-car-gobjectp
  (implies (and (gobjectp x)
                (consp x)
                (gobjectp (car x)))
           (equal (generic-geval x env)
                  (cons (generic-geval (car x) env)
                        (generic-geval (cdr x) env))))
  :hints (("goal" :expand ((generic-geval x env))
           :in-theory (enable gobjectp-car-impl-not-g-types))))

(defthmd gl-eval-of-nil
  (equal (generic-geval nil env) nil))



(defthm gl-eval-consp-when-gobject-listp
  (implies (gobject-listp x)
           (equal (consp (generic-geval x env))
                  (consp x)))
  :hints (("goal" :expand ((:with generic-geval (generic-geval x env))
                           (gobject-listp x))
           :in-theory (e/d (gobjectp-car-impl-not-g-types
                            gobject-listp-impl-gobjectp
                            gobject-listp)
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
 
;; (defthm gobject-listp-cdr
;;   (implies (gobject-listp x)
;;            (gobject-listp (cdr x)))
;;   :hints(("Goal" :in-theory (enable gobject-listp))))





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

(defun def-gl-clause-processor-fn
  (clause-proc apply-fns include-nonrec top-apply-fns output state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((world (w state))
       (current-geval (find-current-geval world))
       (geval (or current-geval
                  (incat clause-proc (symbol-name clause-proc) "-GEVAL")))
       (run-gified (incat clause-proc (symbol-name clause-proc) "-RUN-GIFIED"))
       (run-gified-inner (incat clause-proc (symbol-name clause-proc) "-RUN-GIFIED-INNER"))
       (apply-concrete-inner (incat clause-proc (symbol-name clause-proc)
                                    "-APPLY-INNER"))
       (apply-concrete (incat clause-proc (symbol-name clause-proc)
                              "-APPLY"))
       (apply-concrete-inner-lemma
        (incat clause-proc (symbol-name clause-proc)
               "-APPLY-INNER-CORRECT"))
       (apply-concrete-lemma
        (incat clause-proc (symbol-name clause-proc) "-APPLY-CORRECT"))
       (apply-concrete-state-p1
        (incat clause-proc (symbol-name clause-proc) "-STATE-P1"))
       (g-fns (strip-cars (table-alist 'gl-function-info world)))
       ((mv done collected-apply-fns)
        (collect-fns-list apply-fns nil nil world))
       (- (flush-hons-get-hash-table-link done))
       (recursive-apply-fns
        (if include-nonrec
            collected-apply-fns
          (filter-recursive-fns collected-apply-fns world)))
       (auto-apply-fns (gl-clause-proc-auto-exec-fns))
       (forbid-apply-fns (gl-clause-proc-forbidden-exec-fns))
       (final-apply-fns
        (acl2::hons-remove-duplicates
         (acl2::hons-set-diff
          (append top-apply-fns apply-fns recursive-apply-fns auto-apply-fns)
          ;; no need to have g-fns in the apply
          (append g-fns forbid-apply-fns))))
       (- (cw "number of applyable functions: ~x0~%"
              (len final-apply-fns)))
       (ev (incat clause-proc (symbol-name clause-proc) "-EV"))
       (ev-lst (incat clause-proc (symbol-name clause-proc) "-EV-LST"))
       (falsify (incat clause-proc (symbol-name clause-proc) "-EV-FALSIFY"))
       (ctrex-thm (incat clause-proc (symbol-name clause-proc)
                         "-EV-FALSIFY-COUNTEREXAMPLE"))
       (constraints (incat ev (symbol-name ev) "-CONSTRAINTS"))
       (f-i-thm (incat geval (symbol-name geval)
                       "-IS-FUNCTIONAL-INST-OF-GENERIC-GEVAL-FOR-GL-CLAUSE-PROC"))
       (run-gified-inner-correct
        (incat run-gified (symbol-name run-gified) "-INNER-CORRECT"))
       (run-gified-correct
        (incat run-gified (symbol-name run-gified) "-CORRECT"))
       (run-gified-inner-gobjectp
        (incat run-gified (symbol-name run-gified) "-INNER-GOBJECTP"))
       (run-gified-gobjectp
        (incat run-gified (symbol-name run-gified) "-GOBJECTP"))
       (run-gified-state-p1
        (incat run-gified (symbol-name run-gified) "-STATE-P1"))
       (interp-term (incat clause-proc (symbol-name clause-proc) "-INTERP-TERM"))
       (interp-list (incat clause-proc (symbol-name clause-proc)
                           "-INTERP-LIST"))
       (run-parametrized (incat clause-proc (symbol-name clause-proc)
                           "-RUN-PARAMETRIZED"))
       (run-cases (incat clause-proc (symbol-name clause-proc)
                           "-RUN-CASES"))
       (subst `((interp-term . ,interp-term)
                (interp-list . ,interp-list)
                (run-parametrized . ,run-parametrized)
                (run-cases . ,run-cases)
                (clause-proc-name . ',clause-proc)
                (clause-proc . ,clause-proc)
                (geval-name . ',geval)
                (run-gified . ,run-gified)
                (apply-concrete . ,apply-concrete)))
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
        ,@(if current-geval
              nil
            `((make-geval ,geval nil
                          :output nil)))
        (encapsulate nil
          (set-case-split-limitations '(1 1))
          (defun ,run-gified-inner
            (fn actuals hyp clk)
            (declare (xargs :guard (and (symbolp fn)
                                        (gobject-listp actuals)
                                        (bfr-p hyp)
                                        (natp clk))
                            :guard-hints
                            (("goal" :in-theory
                              (e/d** (gobjectp-nth-gobject-listp
                                      (:forward-chaining gobject-listp-true-listp)))
                              :do-not '(preprocess)))))
            (case fn
              . ,(glcp-predef-cases-fn
                  (remove 'if g-fns) world)))
          (defun ,run-gified
            (fn actuals hyp clk state)
            (declare (xargs :guard (and (symbolp fn)
                                        (gobject-listp actuals)
                                        (bfr-p hyp)
                                        (natp clk))
                            :guard-hints
                            (("goal" :in-theory
                              (e/d** (gobjectp-nth-gobject-listp
                                      (:forward-chaining gobject-listp-true-listp)))
                              :do-not '(preprocess)))
                            :stobjs state))
            (mv-let (ok ans)
              (,run-gified-inner fn actuals hyp clk)
              (mv ok ans state))))

       

        ;; make the evaluator, falsifier
        (local (defun dummy-label-for-make-evaluator-fn () nil))
        (acl2::defevaluator-fast
         ,ev ,ev-lst
         ,(fns-to-calls
           (append `(if gl-cp-hint shape-spec-obj-in-range
                      return-last use-by-hint equal not cons gl-aside
                      gl-ignore
                      gl-error)
                   (set-difference-eq
                    (union-eq g-fns final-apply-fns)
                    `(if gl-cp-hint shape-spec-obj-in-range
                       return-last use-by-hint equal not cons
                       ,@*forbidden-apply-functions*
                       ,geval gl-aside gl-ignore gl-error)))
           world))
        (local (def-ruleset! ,constraints
                 (set-difference-theories
                  (current-theory :here)
                  (current-theory 'dummy-label-for-make-evaluator-fn))))
        (defchoose ,falsify (a) (x)
          (not (,ev x a)))
        (local (defthm ,ctrex-thm
                 (implies (not (,ev x a))
                          (not (,ev x (,falsify x))))
                 :hints (("goal" :use ,falsify))))

        (encapsulate
          nil
          (local (in-theory nil))
          ;; Define the apply-concrete function
          (acl2::defapply ,apply-concrete-inner ,final-apply-fns
                          :theoremsp nil)
          (defun ,apply-concrete (acl2::fn args state)
            (declare (xargs :guard (true-listp args)
                            :stobjs state))
            (mv-let (ok ans)
              (,apply-concrete-inner acl2::fn args)
              (mv ok ans state)))
                            

          (local (defthm ,apply-concrete-inner-lemma
                   (implies (mv-nth 0 (,apply-concrete-inner acl2::fn args))
                            (equal (mv-nth 1 (,apply-concrete-inner acl2::fn args))
                                   (,ev (cons acl2::fn (acl2::kwote-lst args))
                                        nil)))
                   :hints (("goal" :clause-processor
                            (acl2::apply-for-ev-cp clause nil state))
                           (acl2::use-by-computed-hint clause)
                           (acl2::use-these-hints-hint clause))))
          (defthm ,apply-concrete-lemma
            (implies (mv-nth 0 (,apply-concrete acl2::fn args state))
                     (equal (mv-nth 1 (,apply-concrete acl2::fn args
                                                       state))
                            (,ev (cons acl2::fn (acl2::kwote-lst
                                                 args))
                                 nil)))
            :hints(("Goal" :in-theory (e/d** (,apply-concrete
                                              ,apply-concrete-inner-lemma
                                              car-cons cdr-cons)))))

          (defthm ,apply-concrete-state-p1
            (implies (state-p1 state)
                     (state-p1 (mv-nth 2 (,apply-concrete acl2::fn args
                                                       state))))
            :hints(("Goal" :in-theory (e/d** (,apply-concrete)
                                             (state-p1 ,apply-concrete-inner))))))

        (in-theory (disable ,apply-concrete))

        ;; Define the interpreter mutual-recursion, the
        ;; run-parametrized and run-cases functions, and the clause proc.
        ,@(sublis subst (list *glcp-interp-template*
                              *glcp-run-parametrized-template*
                              *glcp-run-cases-template*
                              *glcp-clause-proc-template*))

        ;; Prep for the run-gified correctness and gobjectp theorems
        (local 
         (progn
           (eval-g-prove-f-i ,f-i-thm ,geval generic-geval)
           (eval-g-functional-instance
            gl-eval-car-cdr-of-gobject-listp ,geval generic-geval)
           (eval-g-functional-instance
            gl-eval-consp-when-gobject-listp ,geval generic-geval)
           (eval-g-functional-instance
            gl-eval-of-nil ,geval generic-geval)
           (eval-g-functional-instance
            general-concrete-obj-correct ,geval generic-geval)
           
           ;; Prove correctness of run-gified
           (defthm ,run-gified-inner-correct
             (implies (and (bfr-eval hyp (car env))
                           (gobject-listp actuals)
                           (mv-nth 0 (,run-gified-inner
                                      fn actuals hyp clk)))
                      (equal (,geval (mv-nth 1 (,run-gified-inner
                                                fn actuals hyp clk))
                                     env)
                             (,ev (cons fn (acl2::kwote-lst
                                            (,geval actuals env))) nil)))
             :hints (("goal" :clause-processor
                      (run-gified-clause-proc
                       clause
                       '(,(f-i-thmname
                           'gl-eval-consp-when-gobject-listp geval)
                         ,(f-i-thmname
                           'gl-eval-car-cdr-of-gobject-listp geval)
                         ,(f-i-thmname 'gl-eval-of-nil geval))
                       state))
                     (use-by-computed-hint clause)))

           (defthm ,run-gified-correct
             (implies (and (bfr-eval hyp (car env))
                           (gobject-listp actuals)
                           (mv-nth 0 (,run-gified
                                      fn actuals hyp clk state)))
                      (equal (,geval (mv-nth 1 (,run-gified
                                                fn actuals hyp clk state))
                                     env)
                             (,ev (cons fn (acl2::kwote-lst
                                            (,geval actuals env))) nil)))
             :hints (("goal" :in-theory (e/d** (,run-gified-inner-correct
                                                ,run-gified
                                                mv-nth-cons-meta)
                                               (,run-gified-inner)))))

           ;; Prove GOBJECTP of run-gified
           (defthm ,run-gified-inner-gobjectp
             (gobjectp (mv-nth 1 (,run-gified-inner
                                  fn actuals hyp clk)))
             :hints (("goal" :in-theory
                      (e/d** ((:ruleset g-gobjectp-lemmas)
                              ,run-gified-inner
                              (:compound-recognizer
                               booleanp-compound-recognizer))))))

           (defthm ,run-gified-gobjectp
             (gobjectp (mv-nth 1 (,run-gified
                                  fn actuals hyp clk state)))
             :hints (("goal" :in-theory
                      (e/d** (,run-gified
                              ,run-gified-inner-gobjectp)
                             (,run-gified-inner)))))

           (defthm ,run-gified-state-p1
             (implies (state-p1 state)
                      (state-p1 (mv-nth 2 (,run-gified
                                           fn actuals hyp clk state))))
             :hints (("goal" :in-theory (e/d** (,run-gified)
                                               (,run-gified-inner)))))
             

           (in-theory (disable ,run-gified))

           ;; Prep to prove the guards of the interpreter and the correctness of
           ;; the clause processor.
           (eval-g-functional-instance shape-spec-to-gobj-eval-env
                                       ,geval generic-geval)
           (eval-g-functional-instance mk-g-boolean-correct
                                       ,geval generic-geval)
           (eval-g-functional-instance
            gl-eval-car-gobjectp ,geval generic-geval)

           (eval-g-functional-instance
            gobj-to-param-space-correct ,geval generic-geval)

           (eval-g-functional-instance
            generic-geval-non-cons ,geval generic-geval)

           (def-ruleset! ,f-i-lemmas
             (append '(car-cons cdr-cons
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;                                 acl2::no-duplicatesp-is-no-duplicatesp-equal
                                )
                     (let ((constr (acl2::ruleset ',constraints)))
                       (nthcdr (- (len constr) 18) constr))
                     '(,ctrex-thm
                       ,run-gified-correct
                       ,run-gified-state-p1
                       ,run-gified-gobjectp
                       ,apply-concrete-lemma
                       ,apply-concrete-state-p1
                       ,(f-i-thmname 'gl-eval-car-gobjectp geval)
                       (:type-prescription ,run-gified)
                       (:type-prescription ,apply-concrete)
                       ,(f-i-thmname 'gobj-ite-merge-correct geval)
                       ,(f-i-thmname 'gtests-nonnil-correct geval)
                       ,(f-i-thmname 'gtests-obj-correct geval)
                       ,(f-i-thmname 'shape-spec-to-gobj-eval-env geval)
                       ,(f-i-thmname 'mk-g-boolean-correct geval)
                       ,(f-i-thmname 'mk-g-concrete-correct geval)
                       ,(f-i-thmname 'mk-g-ite-correct geval)
                       ,(f-i-thmname 'generic-geval-non-cons geval)
                       ,(f-i-thmname 'generic-geval-gobj-fix geval)
                       ,(f-i-thmname 'gobj-to-param-space-correct geval)
                       ,(f-i-thmname 'general-concrete-obj-correct geval))))))

        ;; Verify guards of the interpreter.
        (local (in-theory nil))
        (verify-guards 
         ,interp-term
         :hints (("goal" :by
                  (:functional-instance
                   glcp-generic-interp-guards-ok
                   (glcp-generic-interp-term ,interp-term)
                   (glcp-generic-interp-list ,interp-list)
                   (glcp-generic-ev ,ev)
                   (glcp-generic-ev-lst ,ev-lst)
                   (glcp-generic-geval ,geval)
                   (glcp-generic-run-gified ,run-gified)
                   (glcp-generic-run-gified-guard-wrapper ,run-gified)
                   (glcp-generic-ev-falsify ,falsify)
                   (glcp-generic-geval-name (lambda () ',geval))
                   (glcp-generic-apply-concrete ,apply-concrete)
                   (glcp-generic-apply-concrete-guard-wrapper ,apply-concrete))
                  :in-theory (e/d** ((:ruleset ,f-i-lemmas)))
                  :expand ((,interp-list x alist hyp clk obligs
                                         overrides world state)
                           (,interp-term x alist hyp clk obligs
                                         overrides world state))
                  :do-not-induct t)
                 (and stable-under-simplificationp
                      '(:in-theory (e/d** ((:ruleset ,f-i-lemmas)
                                           ,(incat ev (symbol-name ev)
                                                   "-CONSTRAINT-0")))))))

        ;; Prove correctness of the clause processor.
        (defthm ,correct-thm
          (implies (and (pseudo-term-listp clause)
                        (alistp alist)
                        (,ev (conjoin-clauses
                              (acl2::clauses-result
                               (,clause-proc clause hints state)))
                             (,falsify
                              (conjoin-clauses
                               (acl2::clauses-result
                                (,clause-proc clause hints state))))))
                   (,ev (disjoin clause) alist))
          :hints (("goal" :do-not-induct t
                   :in-theory (e/d** (,ctrex-thm))
                   :by (:functional-instance
                        glcp-generic-correct
                        (glcp-generic-interp-term ,interp-term)
                        (glcp-generic-interp-list ,interp-list)
                        (glcp-generic-ev ,ev)
                        (glcp-generic-ev-lst ,ev-lst)
                        (glcp-generic-geval ,geval)
                        (glcp-generic-run-gified ,run-gified)
                        (glcp-generic-run-gified-guard-wrapper ,run-gified)
                        (glcp-generic-apply-concrete ,apply-concrete)
                        (glcp-generic-apply-concrete-guard-wrapper ,apply-concrete)
                        (glcp-generic-ev-falsify ,falsify)
                        (glcp-generic-geval-name (lambda ()
                                                   ',geval))
                        (glcp-generic-run-parametrized
                         ,run-parametrized)
                        (glcp-generic-run-cases ,run-cases)
                        (glcp-generic ,clause-proc)
                        (glcp-generic-clause-proc-name
                         (lambda () ',clause-proc))))
                  (case-match clause
                    ((('equal (fn . args) . &))
                     (and (member fn '(,clause-proc
                                      ,run-parametrized
                                      ,run-cases))
                          `(:expand ((,fn . ,args)))))))
          :otf-flg t
          :rule-classes :clause-processor)

        (table latest-greatest-gl-clause-proc ',clause-proc t)))))





(defmacro def-gl-clause-processor
  (name apply-fns &key (output
                        '(:off (warning warning! observation prove
                                        event summary proof-tree
                                        acl2::expansion)
                               :gag-mode nil))
        top-apply-fns
        include-nonrec)
  ":Doc-section ACL2::GL
Define a GL clause processor with a given set of built-in functions.~/

Usage:
~bv[]
 (def-gl-clause-processor my-gl-clause-processor
   functions
   ;; optional
   :output with-output-settings
   :top-apply-fns some-more-functions
   :include-nonrec include-nonrecp)
~ev[]
where ~c[some-functions] is a form whose value is a list of function
symbols and with-output-settings is a list such as ~c[(:off :all)] of
arguments approprate for ~il[with-output].  The other two arguments are
discussed below.

The above form defines a GL clause processor function named
my-gl-clause-processor.  The list of function symbols provided and
their descendants compose the set of ACL2 functions that the clause
processor can execute directly on concrete values instead of
interpreting.~/

Each GL clause processor has two associated sets of functions: those
it can directly execute symbolically, and those it can directly
execute concretely.  DEF-GL-CLAUSE-PROCESSOR always uses the full set
of functions with defined symbolic counterparts as the first set, but
allows the user to provide the second set.  (Symbolic counterparts may
be defined by hand or using ~c[MAKE-G-WORLD].)
~l[SYMBOLIC-COUNTERPARTS] for information on defining symbolic
counterparts by hand.

The set of functions the clause processor will be able to execute
concretely is determined by the non-optional ~c[functions] argument
and the ~c[top-apply-fns] and ~c[include-nonrec] keyword arguments.
By default, the new clause processor will be able to concretely
execute the functions listed in the ~c[functions] argument and all of
their recursive ancestors, in addition to the functions listed in the
~c[top-apply-fns] argument and some functions that are always
included.  However, if ~c[include-nonrec] is set to T, then all of
these functions' ancestors are included, whether recursive or not.

~l[DEF-GL-THM] and ~il[GL-HINT] for information on using the GL
clause processor to prove theorems.~/"
  `(make-event
    (def-gl-clause-processor-fn
      ',name ,apply-fns ,include-nonrec ,top-apply-fns ',output state)))




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

(defun glcp-combine-hints (call cov-hints hyp-hints res-hints)
  (declare (xargs :mode :program))
  `(:computed-hint-replacement
    ((use-by-computed-hint clause)
     (case-match clause
       ((('not ('gl-cp-hint ('quote name) . &) . &) . rest)
        (case name
          (coverage
           (prog2$ (cw "Now proving coverage~%")
                   (glcp-remove-and-replace ',cov-hints)))
          (result
           (prog2$ (cw "Now proving result (should be trivial)~%")
                   ,(if res-hints
                        `(glcp-remove-and-replace ',res-hints)
                      '(case-match rest
                         ((eval . &)
                          (glcp-remove-and-replace
                           `('(:in-theory (enable ,eval)))))))))
          (param
           (prog2$ (cw "Now proving hyp coverage~%")
                   ,(and hyp-hints
                         `(glcp-remove-and-replace ',hyp-hints))))))))
    :clause-processor ,call))



(defmacro glcp-coverage-default-hint  (&key do-not-expand cov-theory-add)
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


(defun gl-hint-fn (clause-proc bindings param-bindings hyp param-hyp
                               concl hyp-clk concl-clk param-clk
                               cov-hints cov-hints-position cov-theory-add
                               do-not-expand hyp-hints result-hints
                               n-counterexamples abort-indeterminate abort-ctrex
                               run-before-cases run-after-cases test-side-goals)
  (declare (xargs :mode :program))
  `(b* (((mv clause-proc bindings param-bindings hyp param-hyp concl
             hyp-clk concl-clk param-clk cov-hints cov-hints-position
             cov-theory-add do-not-expand hyp-hints result-hints
             n-counterexamples abort-indeterminate abort-ctrex
             run-before-cases run-after-cases test-side-goals)
         (mv ',clause-proc ,bindings ,param-bindings ,hyp ,param-hyp
             ,concl ,hyp-clk ,concl-clk ,param-clk ',cov-hints
             ',cov-hints-position ',cov-theory-add ',do-not-expand
             ',hyp-hints ',result-hints ,n-counterexamples
             ,abort-indeterminate ,abort-ctrex ',run-before-cases ',run-after-cases
             ,test-side-goals))
        (cov-hints (glcp-coverage-hints
                    do-not-expand cov-theory-add cov-hints cov-hints-position)) 
        ((er trhyp)
         (acl2::translate hyp t t nil 'gl-hint-fn (w state) state))
        ((er trparam)
         (acl2::translate param-hyp t t nil 'gl-hint-fn (w state)
                          state))
        ((er trconcl)
         (acl2::translate concl t t nil 'gl-hint-fn (w state) state))
        (vars (collect-vars trconcl))
        (bindings
         (add-var-bindings (set-difference-eq
                            vars (strip-cars bindings))
                           bindings))
        (param-bindings (add-param-var-bindings vars param-bindings))
        (call `(,(if test-side-goals 'glcp-side-goals-clause-proc clause-proc)
                clause (list ',bindings ',param-bindings ',trhyp
                             ',trparam ',trconcl ',concl ,hyp-clk ,concl-clk
                             ,param-clk ,n-counterexamples
                             ,abort-indeterminate ,abort-ctrex
                             ',(and (not test-side-goals) run-before-cases)
                             ',(and (not test-side-goals) run-after-cases))
                state)))
     (value (glcp-combine-hints call cov-hints hyp-hints result-hints))))

(defmacro gl-hint (clause-proc &key
                               bindings param-bindings
                               (hyp-clk '1000000)
                               (concl-clk '1000000)
                               (param-clk '1000000)
                               cov-hints cov-hints-position
                               cov-theory-add do-not-expand
                               hyp-hints
                               result-hints
                               (hyp ''t) param-hyp concl
                               (n-counterexamples '3)
                               (abort-indeterminate 't)
                               (abort-ctrex 't)
                               run-before-cases run-after-cases
                               test-side-goals)
  ":Doc-section ACL2::GL
Try to prove a goal using GL symbolic simulation.~/

Usage, as a computed hint (~l[using-computed-hints]):
~bv[]
 (gl-hint my-gl-clause-processor
         :bindings `((a ,(g-number (list (mk-number-list 1 1 9))))
                     (b ,(g-boolean 0)))
         :hyp '(bvecp a 8)
         :coverage-hints ('(:expand ((bvecp a 8)))))
~ev[]

The above hint causes an attempt to apply the clause processor
my-gl-clause-processor to the current clause.  Such a clause processor
must be created using ~il[DEF-GL-CLAUSE-PROCESSOR].  One such
clause processor, ~c[GL::GLCP], is predefined in the GL system.
Various keyword arguments control the symbolic simulation and
auxilliary proofs.~/

The full interface is as follows, with default values and brief
descriptions of each keyword argument:
~bv[]
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

          ;; To perform case-splitting, set this argument:
          :param-bindings          nil

          ;; Ignored unless case-splitting:
          :param-hyp               nil
          :run-before-cases        nil
          :run-after-cases         nil
          :param-clk               1000000)
~ev[]

The keyword arguments to ~c[GL-HINT] are similar to ones for the
macros ~il[DEF-GL-THM] and ~il[DEF-GL-PARAM-THM], and are
documented there.
~/"

  (gl-hint-fn clause-proc bindings param-bindings hyp param-hyp concl
              hyp-clk concl-clk param-clk cov-hints cov-hints-position
              cov-theory-add do-not-expand hyp-hints result-hints
              n-counterexamples abort-indeterminate abort-ctrex
              run-before-cases run-after-cases test-side-goals))


(defun def-gl-thm-fn
  (name clause-proc rest)
  (declare (xargs :mode :program))
  (b* (((list hyp hyp-p concl concl-p g-bindings g-bindings-p cov-hints
              cov-hints-position cov-theory-add do-not-expand hyp-clk concl-clk
              n-counterexamples abort-indeterminate abort-ctrex test-side-goals
              rule-classes) rest)
       ((unless (and hyp-p concl-p g-bindings-p))
        (er hard 'def-gl-thm
            "The keyword arguments HYP, CONCL, and G-BINDINGS must be provided ~
in DEF-GL-THM.~%"))
       (form `(defthm ,name
                ,(if test-side-goals t `(implies ,hyp ,concl))
                :hints ((gl-hint
                         ,clause-proc
                         :bindings ,g-bindings
                         :hyp-clk ,hyp-clk
                         :concl-clk ,concl-clk
                         :cov-hints ,cov-hints
                         :cov-hints-position ,cov-hints-position
                         :cov-theory-add ,cov-theory-add
                         :do-not-expand ,do-not-expand
                         :hyp ',hyp
                         :concl ',concl
                         :n-counterexamples ,n-counterexamples
                         :abort-indeterminate ,abort-indeterminate
                         :abort-ctrex ,abort-ctrex
                         :test-side-goals ,test-side-goals))
                . ,(if test-side-goals
                       '(:rule-classes nil)
                     `(:rule-classes ,rule-classes)))))
    (if test-side-goals
        `(with-output
          :off :all :stack :push
          (make-event (er-progn (with-output :stack :pop ,form)
                                (value '(value-triple 'test-side-goals)))))
      form)))
                       

;; If a clause-processor name is supplied, this creates a defthm event
;; using def-gl-thm-fn.  Otherwise, this creates a make-event which
;; looks up the most recently defined clause processor in the table
;; latest-greatest-gl-clause-proc and uses def-gl-thm-fn with this
;; clause processor setting.
(defun def-gl-thm-find-cp (name clause-proc clause-procp rest)
  (declare (xargs :mode :program))
  (if clause-procp
      (def-gl-thm-fn name clause-proc rest)
    `(make-event
      (let ((clause-proc
             (caar (table-alist
                    'latest-greatest-gl-clause-proc
                    (w state)))))
        (def-gl-thm-fn ',name clause-proc ',rest)))))



;; Define a macro that provides a drop-in replacement for DEF-G-THM and
;; uses the new clause processor.
(defmacro def-gl-thm
  (name &key (clause-proc 'nil clause-procp)
        skip-g-proofs
        (hyp 'nil hyp-p)
        (concl 'nil concl-p)
        (g-bindings 'nil g-bindings-p)
        cov-hints cov-hints-position
        cov-theory-add
        do-not-expand 
        (hyp-clk '1000000)
        (concl-clk '1000000)
        (n-counterexamples '3)
        (abort-indeterminate 't) (abort-ctrex 't)
        local
        test-side-goals
        (rule-classes ':rewrite))
  ":Doc-section ACL2::GL
Prove a theorem using GL symbolic simulation~/

Usage:
~bv[]
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
~ev[]

This form submits a ~c[DEFTHM] event for the theorem
~c[(implies <hyp> <concl>)] and the specified rule-classes, and gives a hint to
attempt to prove it by symbolic execution using a GL clause processor.~/

Out of the list of keyword arguments recognized by this macro, three are
necessary: ~c[:hyp], ~c[:concl], and ~c[:g-bindings].  As noted, the theorem to
be proved takes the form ~c[(implies <hyp> <concl>)].  The ~c[hyp] is also used
in proving coverage, explained below.

The ~c[g-bindings] must be a term evaluating to an alist formatted as follows:
~bv[]
 ((<var-name1>  <shape-spec1>)
  (<var-name2>  <shape-spec2>)
  ...)
~ev[]
The shape specs must be well-formed as described in ~il[GL::SHAPE-SPECS]; notably,
they must not reuse BDD variable numbers or unconstrainted variable names.
Note also that this is not a dotted alist; the shape spec is the ~c[CADR], not
the ~c[CDR], of each entry.  If any variables mentioned in the theorem are not
bound in this alist, they will be given an unconstrained variable binding.

The symbolic objects used as the inputs to the symbolic simulation are obtained
by translating each shape spec into a symbolic object.  The hyp is symbolically
executed on these symbolic inputs.  Parametrizing the symbolic objects by the
resulting predicate object yields (absent any ~c[G-APPLY] or ~c[G-VAR] objects)
symbolic objects with coverage restricted to only inputs satisfying the hyp.

Here is a simple example theorem:
~bv[]
 (def-gl-thm commutativity-of-+-up-to-16
    :hyp (and (natp a) (natp b)
              (< a 16) (< b 16))
    :concl (equal (+ a b) (+ b a))
    :g-bindings '((a (:g-number (0 2 4 6 8)))
                  (b (:g-number (1 3 5 7 9)))))
~ev[]

This theorem binds its free variables ~c[A] and ~c[B] to symbolic numbers of
five bits.  Note that integers are two's-complement, so to represent natural
numbers one needs one more bit than in the unsigned representation.  Therefore,
these shape specs cover negative numbers down to -16 as well as naturals less
than 16.  However, parametrization by the hypotheses will yield symbolic
objects that only cover the specified range.

The coverage obligation for a theorem will be a goal like this:
~bv[]
 (implies <hyp>
          (shape-spec-obj-in-range
           (list <shape-spec1> <shape-spec2> ...)
           (list <var-name1> <var-name2> ...)))
~ev[]
In the example above:
~bv[]
 (implies (and (natp a) (natp b)
               (< a 16) (< b 16))
          (shape-spec-obj-in-range
           '((:g-number (0 2 4 6 8)) (:g-number (1 3 5 7 9)))
           (list a b)))
~ev[]

It is often convenient to work out the coverage theorem before running the
symbolic simulation, since the symbolic simulation may take a very long time
even when successful.  The keyword argument ~c[:test-side-goals] may be given a
value of ~c[T] in order to attempt the coverage proof on its own; if
successful, no theorem will be stored by ACL2, but one can then be fairly sure
that the coverage proof will go through in the real theorem.

Several hints are given by default for proving coverage; see
~il[GL::SHAPE-SPECS] for details.  The keyword arguments ~c[:cov-theory-add],
~c[:do-not-expand], ~c[:cov-hints], and ~c[cov-hints-position] affect the
coverage proof.

When proof by symbolic simulation fails, the clause processor will print
randomized counterexamples.  The keyword argument ~c[:n-counterexamples]
determines how many it prints.  The default is 3.

A symbolic simulation may result in a symbolic object that can't be
syntactically determined to be non-nil; for example, the result may contain a
~c[:G-APPLY] object.  In these situations, the proof attempt will
abort, and an example will be shown of inputs for which the symbolic result's
value could not be determined.  To debug this type of problem, see
~il[GL::DEBUGGING-INDETERMINATE-RESULTS].

The symbolic interpreter and all symbolic counterpart functions take a clock
argument to ensure termination.  The starting clocks for the symbolic
executions of the hyp (for parametrization) and the conclusion may be set using
the keyword arguments ~c[:hyp-clk] and ~c[:concl-clk]; the defaults are both
1000000.

The keyword argument ~c[:clause-proc] can be used to select the clause
processor to be used; see ~c[DEF-GL-CLAUSE-PROCESSOR].  By default, the latest
clause processor introduced is used.  If no ~c[:clause-proc] keyword argument
is given, then this macro expands to a ~c[make-event], which in turn expands to
the ~c[defthm] event; otherwise, this expands directly to the ~c[defthm].

The keyword argument ~c[:rule-classes] can be used to select the rule-classes
for the theorem produced, as in ~c[defthm]; the default is ~c[:rewrite].
~/
"
  (declare (ignore skip-g-proofs local))
  (def-gl-thm-find-cp name clause-proc clause-procp
    (list hyp hyp-p concl concl-p g-bindings g-bindings-p cov-hints
          cov-hints-position cov-theory-add do-not-expand hyp-clk concl-clk
          n-counterexamples abort-indeterminate abort-ctrex test-side-goals
          rule-classes)))





(defun def-gl-param-thm-fn (name clause-proc rest)
  (declare (xargs :mode :program))
  (b* (((list hyp hyp-p param-hyp param-hyp-p concl concl-p cov-bindings
              cov-bindings-p param-bindings param-bindings-p
              cov-hints cov-hints-position cov-theory-add do-not-expand
              hyp-clk concl-clk param-clk n-counterexamples
              abort-indeterminate abort-ctrex run-before-cases run-after-cases
              test-side-goals rule-classes)
        rest)
       ((unless (and hyp-p param-hyp-p concl-p cov-bindings-p
                     param-bindings-p))
        (er hard 'def-gl-param-thm
            "The keyword arguments HYP, PARAM-HYP, CONCL, COV-BINDINGS, and ~
PARAM-BINDINGS must be provided in DEF-GL-PARAM-THM.~%"))
       (form `(defthm ,name
                ,(if test-side-goals t `(implies ,hyp ,concl))
                :hints ((gl-hint
                         ,clause-proc
                         :bindings ,cov-bindings
                         :param-bindings ,param-bindings
                         :hyp-clk ,hyp-clk
                         :concl-clk ,concl-clk
                         :param-clk ,param-clk
                         :cov-hints ,cov-hints
                         :cov-hints-position ,cov-hints-position
                         :cov-theory-add ,cov-theory-add
                         :do-not-expand ,do-not-expand
                         :hyp ',hyp
                         :param-hyp ',param-hyp
                         :concl ',concl
                         :n-counterexamples ,n-counterexamples
                         :abort-indeterminate ,abort-indeterminate
                         :abort-ctrex ,abort-ctrex
                         :run-before-cases ,run-before-cases
                         :run-after-cases ,run-after-cases
                         :test-side-goals ,test-side-goals))
                . ,(if test-side-goals
                       '(:rule-classes nil)
                     `(:rule-classes ,rule-classes)))))
    (if test-side-goals
        `(with-output
          :off :all :stack :push
          (make-event (er-progn (with-output :stack :pop ,form)
                                (value '(value-triple 'test-side-goals)))))
      form)))

;; If a clause-processor name is supplied, this creates a defthm event
;; using def-gl-param-thm-fn.  Otherwise, this creates a make-event which
;; looks up the most recently defined clause processor in the table
;; latest-greatest-gl-clause-proc and uses def-gl-param-thm-fn with this
;; clause processor setting.
(defun def-gl-param-thm-find-cp
  (name clause-proc clause-procp rest)
  (declare (xargs :mode :program))
  (if clause-procp
      (def-gl-param-thm-fn name clause-proc rest)
    `(make-event
      (let ((clause-proc
             (caar (table-alist
                    'latest-greatest-gl-clause-proc
                    (w state)))))
        (def-gl-param-thm-fn ',name clause-proc ',rest)))))


(defmacro def-gl-param-thm
  (name &key (clause-proc 'nil clause-procp)
        skip-g-proofs
        (hyp 'nil hyp-p)
        (param-hyp 'nil param-hyp-p)
        (concl 'nil concl-p)
        (cov-bindings 'nil cov-bindings-p)
        (param-bindings 'nil param-bindings-p)
        cov-hints cov-hints-position
        cov-theory-add
        do-not-expand 
        (hyp-clk '1000000)
        (concl-clk '1000000)
        (param-clk '1000000)
        (n-counterexamples '3)
        (abort-indeterminate 't) (abort-ctrex 't)
        run-before-cases run-after-cases local test-side-goals
        (rule-classes ':rewrite))
  ":Doc-section ACL2::GL
Prove a theorem using GL symbolic simulation with parametrized case-splitting.~/

Usage:
~bv[]
 (def-gl-param-thm <theorem-name>
   :hyp <hypotheses>
   :concl <conclusion>
   :param-hyp <parametrized hypotheses>
   :cov-bindings <bindings for parametrization coverage>
   :param-bindings <bindings for the individual cases>

   :rule-classes <rule classes expression>

   :hyp-clk <number> :concl-clk <number> :param-clk <number>
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
~ev[]

This form submits a ~c[DEFTHM] event for the theorem
~c[(implies <hyp> <concl>)] and the specified rule classes, and gives a hint to
attempt to prove it using a GL clause processor with parametrized
case-splitting.  See ~il[def-gl-thm] for a simpler version that does not do
case splitting.~/

Out of the list of keyword arguments recognized by this macro, five are
necessary: ~c[:hyp], ~c[:concl], ~c[param-hyp], ~c[:cov-bindings], and
~c[:param-bindings].  As noted, the theorem to be proved takes the form
~c[(implies <hyp> <concl>)].  The theorem is split into cases based on the
~c[param-hyp], a term containing some free variables of the theorem and some
additional variables used in case splitting.  Values are assigned to these
variables based on the entries in the ~c[param-bindings], an alist of the
following form:
~bv[]
 ((<case-bindings1> <var-bindings1>)
  (<case-bindings2> <var-bindings2>)
  ...)
~ev[]
Each of the case-bindings is, in turn, an alist of the following form:
~bv[]
 ((<case-var1> <obj1>)
  (<case-var2> <obj2>)
  ...)
~ev[]
and each of the var-bindings is an alist of the following form:
~bv[]
 ((<thm-var1> <shape-spec1>)
  (<thm-var2> <shape-spec2>)
  ...)
~ev[]

For each entry in the ~c[param-bindings], the ~c[param-hyp] is instantiated
with the case variables bound to the objects specified in the entry's
case-bindings.  This term gives a hypothesis about the free variables of the
theorem, and the set of these terms generated from the param-bindings gives the
full case-split.  The case split must cover the theorem's hypotheses; that is,
the theorem's hypothesis must imply the disjunction of the case hypotheses.  To
prove this, we symbolically simulate this disjunction using the shape specs
given in the ~c[cov-bindings], which are formatted like the var-bindings above.

A simple example is as follows:
~bv[]
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
~ev[]

This theorem is proved by symbolic simulation of five cases, in each of which
the param-hyp is assumed with a different setting of the sign and lower-bits
case variables; in one case ~c[N] is required to be negative, and in the others
it is required to be positive and have a given value on its two low-order
bits.  To show that the case-split is complete, another symbolic simulation is
performed (using the given ~c[:cov-bindings]) which proves that the disjunction
of the case assumptions is complete; effectively,
~bv[]
 (implies (and (integerp n) (<= -16 n) (< n 16))
          (or (< n 0)
              (and (<= 0 n) (equal (logand n 3) 0))
              (and (<= 0 n) (equal (logand n 3) 1))
              (and (<= 0 n) (equal (logand n 3) 2))
              (and (<= 0 n) (equal (logand n 3) 3))))
~ev[]

Most of the remaining keyword arguments to ~c[DEF-GL-PARAM-THM] are also
available in ~il[DEF-GL-THM] and are documented there.  The rest are as
follows:

~c[:RUN-BEFORE-CASES] and ~c[:RUN-AFTER-CASES] cause a user-specified form to
be run between the parametrized symbolic simulations.  These may use the
variable ~c[id], which is bound to the current assignment of the case-splitting
variables.  These can be used to print a message before and after running each
case so that the user can monitor the theorem's progress.

~c[:PARAM-CLK] is similar to ~c[:HYP-CLK] and ~c[:CONCL-CLK]
 (~l[DEF-GL-THM]); it governs the recursion depth of the symbolic simulation
showing that the disjunction of the case assumptions is complete.  Its default
is 1000000.

By default, if a counterexample is encountered on any of the cases, the proof
will abort.  Setting ~c[:ABORT-CTREX] to ~c[NIL] causes it to go on; the proof
will fail after the clause processor returns because it will produce a goal of
~c[NIL].

~/   
"
  (declare (ignore skip-g-proofs local))
  (def-gl-param-thm-find-cp name clause-proc clause-procp
    (list hyp hyp-p param-hyp param-hyp-p concl concl-p cov-bindings
          cov-bindings-p param-bindings param-bindings-p cov-hints
          cov-hints-position cov-theory-add do-not-expand hyp-clk concl-clk
          param-clk n-counterexamples abort-indeterminate abort-ctrex run-before-cases
          run-after-cases test-side-goals rule-classes)))



