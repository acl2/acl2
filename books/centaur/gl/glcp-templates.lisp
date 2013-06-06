

(in-package "GL")

(include-book "tools/flag" :dir :system)

(defconst *glcp-interp-template*
  '(mutual-recursion
 (defun interp-term
   (x alist pathcond clk obligs config state)
   (declare (xargs
             :measure (list clk 20 (acl2-count x) 20)
             :well-founded-relation acl2::nat-list-<
             :hints (("goal"
                      :in-theory (e/d** ((:rules-of-class :executable-counterpart :here)
                                         acl2::open-nat-list-<
                                         acl2-count len nfix fix
                                         car-cons cdr-cons commutativity-of-+
                                         unicity-of-0 null atom
                                         eq acl2-count-last-cdr-when-cadr-hack
                                         car-cdr-elim natp-compound-recognizer
                                         acl2::zp-compound-recognizer
                                         acl2::posp-compound-recognizer
                                         pos-fix
                                         g-ite-depth-sum-of-glcp-interp-args-split-ite-then
                                         g-ite-depth-sum-of-glcp-interp-args-split-ite-else
                                         (:type-prescription acl2-count)))))
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp x)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* (((when (zp clk))
         (glcp-interp-error "The clock ran out.~%"))
        ((when (null x)) (glcp-value nil))
        ((when (symbolp x))
         (glcp-value (cdr (hons-assoc-equal x alist))))
        ((when (atom x))
         (glcp-interp-error
          (acl2::msg "GLCP:  The unquoted atom ~x0 is not a term~%"
                     x)))
        ((when (eq (car x) 'quote))
         (glcp-value (g-concrete-quote (car (cdr x)))))
        ((when (consp (car x)))
         (b*
           (((glcp-er actuals)
             (interp-list (cdr x)
                                       alist pathcond clk obligs config state))
            (formals (car (cdar x)))
            (body (car (cdr (cdar x)))))
           (if (and (mbt (and (equal (len actuals) (len formals))
                              (symbol-listp formals)))
                    (acl2::fast-no-duplicatesp formals)
                    (not (member-eq nil formals)))
               (interp-term body (pairlis$ formals actuals)
                                         pathcond clk obligs config state)
             (glcp-interp-error (acl2::msg "Badly formed lambda application: ~x0~%"
                                           x)))))
        ((when (eq (car x) 'if))
         (let ((test (car (cdr x)))
               (tbr (car (cdr (cdr x))))
               (fbr (car (cdr (cdr (cdr x))))))
           (interp-if test tbr fbr alist pathcond clk obligs
                                   config state)))
        
        ((when (eq (car x) 'gl-aside))
         (if (eql (len x) 2)
             (prog2$ (gl-aside-wormhole (cadr x) alist)
                     (glcp-value nil))
           (glcp-interp-error "Error: wrong number of args to GL-ASIDE~%")))
        ((when (eq (car x) 'gl-ignore))
         (glcp-value nil))
        ((when (eq (car x) 'gl-error))
         (if (eql (len x) 2)
             (b* (((glcp-er result)
                   (interp-term (cadr x)
                                             alist pathcond clk obligs config state))
                  (state (f-put-global 'gl-error-result
                                       result state)))
               (glcp-interp-error
                (acl2::msg
                 "Error: GL-ERROR call encountered.  Data associated with the ~
                      error is accessible using (@ ~x0).~%"
                 'gl-error-result)))
           (glcp-interp-error "Error: wrong number of args to GL-ERROR~%")))
        ((when (eq (car x) 'return-last))
         (if (eql (len x) 4)
             (if (equal (cadr x) ''acl2::time$1-raw)
                 (b* (((mv err & time$-args state)
                       (interp-term (caddr x)
                                                 alist pathcond clk obligs config state)))
                   (mbe :logic (interp-term
                                (car (last x)) alist pathcond clk obligs config state)
                        :exec
                        (if (and (not err)
                                 (general-concretep time$-args))
                            (return-last
                             'acl2::time$1-raw
                             (general-concrete-obj time$-args)
                             (interp-term (car (last x))
                                                       alist pathcond clk obligs config state))
                          (time$
                           (interp-term (car (last x))
                                                     alist pathcond clk obligs config state)))))
               (interp-term (car (last x))
                                         alist pathcond clk obligs config state))
           (glcp-interp-error "Error: wrong number of args to RETURN-LAST~%")))
        (fn (car x))
        ;; outside-in rewriting?
        ((glcp-er actuals)
         (interp-list (cdr x)
                                   alist pathcond clk obligs config state)))
     (interp-fncall-ifs fn actuals x pathcond clk obligs config
                                     state)))

 (defun interp-fncall-ifs
   (fn actuals x pathcond clk obligs config state)
   (declare (xargs
             :measure (list (pos-fix clk) 15 (g-ite-depth-sum actuals) 20)
             :guard (and (posp clk)
                         (symbolp fn)
                         (not (eq fn 'quote))
                         (gobj-listp actuals)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* (((mv has-if test then-args else-args)
         (glcp-interp-args-split-ite actuals))
        ((when has-if)
         (b* ((hyp pathcond))
           (glcp-if
            test
            (interp-fncall-ifs fn then-args x hyp clk obligs config state)
            (interp-fncall-ifs fn else-args x hyp clk obligs config
                                            state)))))
     (interp-fncall fn actuals x pathcond clk obligs config state)))


 (defun interp-fncall
   (fn actuals x pathcond clk obligs config state)
   (declare (xargs
             :measure (list (pos-fix clk) 14 0 20)
             :guard (and (posp clk)
                         (symbolp fn)
                         (not (eq fn 'quote))
                         (gobj-listp actuals)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* (((mv fncall-failed ans)
         (if (general-concrete-listp actuals)
             (acl2::magic-ev-fncall fn (general-concrete-obj-list actuals)
                                    state t nil)
           (mv t nil)))
        ((unless fncall-failed)
         (glcp-value (mk-g-concrete ans)))
        ((mv erp obligs1 successp term bindings state)
         (rewrite-fncall fn actuals pathcond clk obligs config state))
        ((when erp) (mv erp obligs nil state))
        ((when successp)
         (interp-term term bindings pathcond (1- clk) obligs1 config state))
        ((mv ok ans)
         (run-gified fn actuals pathcond clk state))
        ((when ok) (glcp-value ans))
        ((mv erp body formals obligs)
         (acl2::interp-function-lookup fn
                                       obligs (glcp-config->overrides config)
                                       (w state)))
        ((when erp) (glcp-interp-error erp))
        ((unless (equal (len formals) (len actuals)))
         (glcp-interp-error
          (acl2::msg
           "~
In the function call ~x0, function ~x1 is given ~x2 arguments,
but its arity is ~x3.  Its formal parameters are ~x4."
           x fn (len actuals)
           (len formals)
           formals))))
     (interp-term body (pairlis$ formals actuals)
                               pathcond (1- clk)
                               obligs config state)))

 (defun interp-if (test tbr fbr alist pathcond clk obligs
                                     config state)
   (declare (xargs
             :measure (list clk 20 (+ 1 (+ (acl2-count test)
                                           (acl2-count tbr)
                                           (acl2-count fbr))) 10)
             :verify-guards nil
             :guard (and (natp clk)
                         (pseudo-termp test)
                         (pseudo-termp tbr)
                         (pseudo-termp fbr)
                         (acl2::interp-defs-alistp obligs)
                         (glcp-config-p config)
                         (acl2::interp-defs-alistp (glcp-config->overrides config)))
             :stobjs state))
   (b* ((hyp pathcond)
        ((glcp-er test-obj)
         (interp-term test alist hyp clk obligs config state)))
     ;; BOZO glcp-or and glcp-if assume we're using the variable name HYP
     ;; for pathcond
     (if (hons-equal test tbr)
         (glcp-or
          test-obj
          (interp-term fbr alist hyp clk obligs config state))
       (glcp-if
        test-obj
        (interp-term tbr alist hyp clk obligs config state)
        (interp-term fbr
                                  alist hyp clk obligs config state)))))

 (defun rewrite-fncall (fn actuals pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 12 0 0)))
   
   ;; (mv erp obligs1 successp term bindings state)
   (b* ((rules (cdr (hons-assoc-equal fn (table-alist 'gl-rewrite-rules (w state)))))
        ;; or perhaps we should pass the table in the obligs? see if this is
        ;; expensive
        ((unless (and rules (true-listp rules))) ;; optimization (important?)
         (mv nil obligs nil nil nil state))
        (fn-rewrites (getprop fn 'acl2::lemmas nil 'current-acl2-world (w state))))
     (rewrite-fncall-apply-rules
      fn-rewrites rules fn actuals pathcond clk obligs config state)))
 
 
 (defun rewrite-fncall-apply-rules
   (fn-rewrites rules fn actuals pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (true-listp rules)
                               (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 8 (len fn-rewrites) 0)))
   (b* (((when (atom fn-rewrites))
         ;; no more rules, fail
         (mv nil obligs nil nil nil state))
        (rule (car fn-rewrites))
        ((unless (acl2::weak-rewrite-rule-p rule))
         (cw "malformed rewrite rule?? ~x0~%" rule)
         (rewrite-fncall-apply-rules
          (cdr fn-rewrites) rules fn actuals pathcond clk obligs config state))
        ((unless (member-equal (acl2::rewrite-rule->rune rule) rules))
         (rewrite-fncall-apply-rules
          (cdr fn-rewrites) rules fn actuals pathcond clk obligs config state))
        ((mv erp obligs1 successp term bindings state)
         (rewrite-fncall-apply-rule
          rule fn actuals pathcond clk obligs config state))
        ((when erp)
         (mv erp obligs nil nil nil state))
        ((when successp)
         (mv nil obligs1 successp term bindings state)))
     (rewrite-fncall-apply-rules
      (cdr fn-rewrites) rules fn actuals pathcond clk obligs config state)))

 (defun rewrite-fncall-apply-rule
   (rule fn actuals pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (acl2::weak-rewrite-rule-p rule)
                               (posp clk)
                               (symbolp fn)
                               (not (eq fn 'quote))
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 4 0 0)))
   (b* (((rewrite-rule rule) rule)
        ((unless (and (eq rule.equiv 'equal)
                      (not (eq rule.subclass 'acl2::meta))
                      (pseudo-termp rule.lhs)
                      (consp rule.lhs)
                      (eq (car rule.lhs) fn)))
         (cw "malformed gl rewrite rule (lhs)?? ~x0~%" rule)
         (mv nil obligs nil nil nil state))
        ((mv unify-ok gobj-bindings)
         (glcp-unify-term/gobj-list (cdr rule.lhs) actuals nil))
        ((unless unify-ok)
         (mv nil obligs nil nil nil state))
        ((unless (pseudo-term-listp rule.hyps))
         (cw "malformed gl rewrite rule (hyps)?? ~x0~%" rule)
         (mv nil obligs nil nil nil state))
        ((mv erp obligs1 hyps-ok gobj-bindings state)
         (relieve-hyps rule.hyps gobj-bindings pathcond clk obligs config state))
        ((when erp)
         (mv erp obligs nil nil nil state))
        ((unless hyps-ok)
         (mv nil obligs nil nil nil state))
        ((unless (pseudo-termp rule.rhs))
         (cw "malformed gl rewrite rule (rhs)?? ~x0~%" rule)
         (mv nil obligs nil nil nil state)))
     (mv nil obligs1 t rule.rhs gobj-bindings state)))

 (defun relieve-hyps (hyps bindings pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (pseudo-term-listp hyps)
                               (posp clk)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 2 (len hyps) 0)))
   (b* (((when (atom hyps))
         (mv nil obligs t bindings state))
        ((mv erp obligs ok bindings state)
         (relieve-hyp (car hyps) bindings pathcond clk obligs
                                   config state))
        ((when (or erp (not ok)))
         (mv erp obligs ok bindings state)))
     (relieve-hyps (cdr hyps) bindings pathcond clk obligs config
                                state)))

 (defun relieve-hyp (hyp bindings pathcond clk obligs config state)
   (declare (xargs :stobjs state
                   :guard (and (pseudo-termp hyp)
                               (posp clk)
                               (acl2::interp-defs-alistp obligs)
                               (glcp-config-p config)
                               (acl2::interp-defs-alistp
                                (glcp-config->overrides config)))
                   :measure (list (pos-fix clk) 1 0 0)))
   ;; "Simple" version for now; maybe free variable bindings, syntaxp, etc later...
   (b* (((when (and (consp hyp) (eq (car hyp) 'synp)))
         (b* (((mv erp successp bindings)
               (glcp-relieve-hyp-synp hyp bindings state)))
           (mv erp obligs successp bindings state)))
         ((mv erp obligs val state)
         (interp-term hyp bindings pathcond (1- clk) obligs config
                                   state))
        ((when erp)
         (mv erp obligs nil nil state))
        (test (gtests val pathcond))
        ((when (and (eq (gtests-nonnil test) t)
                    (eq (gtests-unknown test) nil)))
         (mv nil obligs t bindings state)))
     (mv nil obligs nil bindings state)))

 (defun interp-list
   (x alist pathcond clk obligs config state)
   (declare
    (xargs
     :measure (list clk 20 (acl2-count x) 20)
     :guard (and (natp clk)
                 (pseudo-term-listp x)
                 (acl2::interp-defs-alistp obligs)
                 (glcp-config-p config)
                 (acl2::interp-defs-alistp (glcp-config->overrides config)))
     :stobjs state))
   (if (atom x)
       (glcp-value nil)
     (b* (((glcp-er car)
           (interp-term (car x)
                                     alist pathcond clk obligs config state))
          ((glcp-er cdr)
           (interp-list (cdr x)
                                     alist pathcond clk obligs config state)))
       (glcp-value (gl-cons car cdr)))))))

(defconst *glcp-run-parametrized-template*
  '(defun run-parametrized
     (hyp concl vars bindings id obligs config state)
     (b* ((bound-vars (strip-cars bindings))
          ((glcp-config config) config)
          ((er hyp)
           (if (pseudo-termp hyp)
               (let ((hyp-unbound-vars
                      (set-difference-eq (collect-vars hyp)
                                         bound-vars)))
                 (if hyp-unbound-vars
                     (prog2$ (flush-hons-get-hash-table-link obligs)
                             (glcp-error (acl2::msg "~
In ~@0: The hyp contains the following unbound variables: ~x1~%"
                                                    id hyp-unbound-vars)))
                   (value hyp)))
             (glcp-error "The hyp is not a pseudo-term.~%")))
          ((unless (shape-spec-bindingsp bindings))
           (flush-hons-get-hash-table-link obligs)
           (glcp-error
            (acl2::msg "~
In ~@0: the bindings don't satisfy shape-spec-bindingsp: ~x1"
                       id bindings)))
          (obj (strip-cadrs bindings))
          ((unless (and (acl2::fast-no-duplicatesp (shape-spec-indices obj))
                        (acl2::fast-no-duplicatesp-equal (shape-spec-vars obj))))
           (flush-hons-get-hash-table-link obligs)
           (glcp-error
            (acl2::msg "~
In ~@0: the indices or variables contain duplicates in bindings ~x1"
                       id bindings)))
          ((unless (subsetp-equal vars bound-vars))
           (flush-hons-get-hash-table-link obligs)
           (glcp-error
            (acl2::msg "~
In ~@0: The conclusion countains the following unbound variables: ~x1~%"
                       id (set-difference-eq vars bound-vars))))
          (al (shape-specs-to-interp-al bindings))
          (cov-clause
           (list '(not (gl-cp-hint 'coverage))
                 (dumb-negate-lit hyp)
                 `(shape-spec-obj-in-range
                   ',obj
                   ,(list*-macro (append (strip-cars bindings)
                                         (list ''nil))))))
          ((mv er obligs1 hyp-val state)
           (interp-term hyp al t config.hyp-clk obligs config state))
          ((when er)
           (flush-hons-get-hash-table-link obligs1)
           (glcp-error
            (acl2::msg
             "~x0 failed to run the hyp, error: ~@1~%"
             config.clause-proc-name er)))
          (hyp-test (gtests hyp-val t))
          (hyp-bdd (bfr-or (gtests-nonnil hyp-test)
                           (gtests-unknown hyp-test)))
          ((when (not hyp-bdd))
           (if config.abort-vacuous
               (glcp-error "Hypothesis is not satisfiable.")
             (prog2$ (cw "NOTE: Hypothesis is not satisfiable~%")
                     (value (cons (list cov-clause) obligs1)))))
          (param-al (gobj-alist-to-param-space al hyp-bdd))
          (hyp-param (bfr-to-param-space hyp-bdd hyp-bdd))
          ((mv er obligs2 val state)
           (interp-term concl param-al hyp-param config.concl-clk obligs1 config state))
          ((when er)
           (flush-hons-get-hash-table-link obligs2)
           (glcp-error
            (acl2::msg
             "~x0 failed with error: ~@1~%" config.clause-proc-name er)))
          ((er val-clause)
           (glcp-analyze-interp-result
            val bindings hyp-bdd id concl config state)))
       (value (cons (list val-clause cov-clause) obligs2)))))

     ;; abort-unknown abort-ctrex exec-ctrex abort-vacuous nexamples hyp-clk concl-clk
     ;; clause-proc-name overrides  run-before run-after case-split-override


(defconst *glcp-run-cases-template*
  '(defun run-cases
     (param-alist concl vars obligs config state)
     (if (atom param-alist)
         (value (cons nil obligs))
       (b* (((er (cons rest obligs))
             (run-cases
              (cdr param-alist) concl vars obligs config state))
            (hyp (caar param-alist))
            (id (cadar param-alist))
            (g-bindings (cddar param-alist))
            (- (glcp-cases-wormhole (glcp-config->run-before config) id))
            ((er (cons clauses obligs))
             (run-parametrized
              hyp concl vars g-bindings id obligs config state))
            (- (glcp-cases-wormhole (glcp-config->run-after config) id)))
         (value (cons (append clauses rest) obligs))))))

(defconst *glcp-clause-proc-template*
  '(defun clause-proc (clause hints state)
     (b* (;; ((unless (sym-counterparts-ok (w state)))
          ;;  (glcp-error "The installed symbolic counterparts didn't satisfy all our checks"))
          ((list bindings param-bindings hyp param-hyp concl ?untrans-concl config) hints)
          ((er overrides)
           (preferred-defs-to-overrides
            (table-alist 'preferred-defs (w state)) state))
          (config (change-glcp-config config :overrides overrides))
          ((er hyp)
           (if (pseudo-termp hyp)
               (value hyp)
             (glcp-error "The hyp is not a pseudo-term.~%")))
          (hyp-clause (cons '(not (gl-cp-hint 'hyp))
                            (append clause (list hyp))))
          ((er concl)
           (if (pseudo-termp concl)
               (value concl)
             (glcp-error "The concl is not a pseudo-term.~%")))
          (concl-clause (cons '(not (gl-cp-hint 'concl))
                              (append clause (list (list 'not concl))))))
       (if param-bindings
           ;; Case splitting.
           (b* (((er param-hyp)
                 (if (pseudo-termp param-hyp)
                     (value param-hyp)
                   (glcp-error "The param-hyp is not a pseudo-term.~%")))
                (full-hyp (conjoin (list param-hyp hyp)))
                (param-alist (param-bindings-to-alist
                              full-hyp param-bindings))
                ;; If the hyp holds, then one of the cases in the
                ;; param-alist holds.
                (params-cov-term (disjoin (strip-cars param-alist)))
                (params-cov-vars (collect-vars params-cov-term))
                (- (cw "Checking case split coverage ...~%"))
                ((er (cons params-cov-res-clauses obligs0))
                 (if (glcp-config->case-split-override config)
                     (value (cons (list `((not (gl-cp-hint 'casesplit))
                                          (not ,hyp)
                                          ,params-cov-term))
                                  'obligs))
                   (run-parametrized
                    hyp params-cov-term params-cov-vars bindings
                    "case-split coverage" 'obligs config state)))
                (- (cw "Case-split coverage OK~%"))
                ((er (cons cases-res-clauses obligs1))
                 (run-cases
                  param-alist concl (collect-vars concl) obligs0 config state)))
             (value (list* hyp-clause concl-clause
                           (append cases-res-clauses
                                   params-cov-res-clauses
                                   (acl2::interp-defs-alist-clauses 
                                    (flush-hons-get-hash-table-link obligs1))))))
         ;; No case-splitting.
         (b* (((er (cons res-clauses obligs))
               (run-parametrized
                hyp concl (collect-vars concl) bindings
                "main theorem" nil config state)))
           (cw "GL symbolic simulation OK~%")
           (value (list* hyp-clause concl-clause
                         (append res-clauses
                                 (acl2::interp-defs-alist-clauses
                                  (flush-hons-get-hash-table-link obligs))))))))))

