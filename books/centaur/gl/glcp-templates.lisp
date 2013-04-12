

(in-package "GL")

(include-book "tools/flag" :dir :system)

(defconst *glcp-interp-template*
  '(mutual-recursion
    (defun interp-term (x alist hyp clk obligs config state)
      (declare (xargs :measure (make-ord 1 (1+ (nfix clk)) (acl2-count x))
                      :hints (("goal" :in-theory
                               (e/d**
                                ((:rules-of-class :executable-counterpart :here)
                                 acl2-count len make-ord nfix o-finp o-first-coeff
                                 fix o-first-expt o-p o-rst o< car-cons cdr-cons
                                 commutativity-of-+ ;  fold-constants-in-plus
                                 nfix unicity-of-0 null atom eq
                                 acl2-count-last-cdr-when-cadr-hack
                                 car-cdr-elim natp-compound-recognizer
                                 acl2::zp-compound-recognizer
                                 acl2::posp-compound-recognizer
                                 (:type-prescription acl2-count)))))
                      :verify-guards nil
                      :guard (and (natp clk)
                                  (pseudo-termp x)
                                  (bfr-p hyp)
                                  (acl2::interp-defs-alistp obligs)
                                  (glcp-config-p config)
                                  (acl2::interp-defs-alistp (glcp-config->overrides config))
                                  (gobject-vals-alistp alist))
                      :stobjs state))
      (cond ((zp clk)
             (glcp-interp-error "The clock ran out.~%"))

            ((null x) (glcp-value nil))

            ;; X is a variable; look it up in the alist; the result must be a
            ;; g-object because of the gobject-vals-alistp guard.
            ((symbolp x)
             (glcp-value (mbe :logic (gobj-fix (cdr (hons-assoc-equal x alist)))
                              :exec (cdr (hons-assoc-equal x alist)))))
                 
            ((atom x)
             (glcp-interp-error
              (acl2::msg "GLCP:  The unquoted atom ~x0 is not a term~%"
                            x)))

            ;; X is a quoted (concrete) object.  g-concrete-quote creates a
            ;; constant-valued symbolic object.  We used to call mk-g-concrete
            ;; here but that scans through the whole cons tree which can be
            ;; expensive.  G-concrete-quote just wraps a g-concrete around the
            ;; object unless it's a non-g-keyword atom.
            ((eq (car x) 'quote) (glcp-value (g-concrete-quote
                                              (car (cdr x)))))

            ;; X is a lambda application; interpret each of the actuals, pair up
            ;; the formals with these values, then interpret the body.
            ((consp (car x))
             (b* (((glcp-er actuals)
                   (interp-list (cdr x) alist hyp clk obligs config state))
                  (formals (car (cdar x)))
                  (body (car (cdr (cdar x)))))
               (if (and (equal (len actuals) (len formals))
                        (nonnil-symbol-listp formals)
                        (acl2::fast-no-duplicatesp formals))
                   (interp-term
                    body (pairlis$ formals actuals)
                    hyp clk obligs config state)
                 (glcp-interp-error
                  (acl2::msg "Badly formed lambda application: ~x0~%" x)))))

            ;; X is an IF; determine first whether it's an OR, then run the
            ;; necessary cases.  Note that gli-or and gli-if are macros and the
            ;; arguments are not necessarily all evaluated.
            ((eq (car x) 'if)
             (if (equal (len x) 4)
                 (let ((test (car (cdr x)))
                       (tbr (car (cdr (cdr x))))
                       (fbr (car (cdr (cdr (cdr x))))))
                   (if (hons-equal test tbr)
                       (glcp-or
                        (interp-term test alist hyp clk obligs config state)
                        (interp-term fbr alist hyp clk obligs config state))
                     (glcp-if
                      (interp-term test alist hyp clk obligs config state)
                      (interp-term tbr alist hyp clk obligs config state)
                      (interp-term fbr alist hyp clk obligs config state))))
               (glcp-interp-error
                "Error: wrong number of args to IF~%")))

            ;; GL-ASIDE call: run the arg in a wormhole and produce
            ;; nil.
            ((eq (car x) 'gl-aside)
             (if (eql (len x) 2)
                 (prog2$ (gl-aside-wormhole (cadr x) alist)
                         (glcp-value nil))
               (glcp-interp-error
                "Error: wrong number of args to GL-ASIDE~%")))

            ;; GL-IGNORE call: don't run the arg
            ((eq (car x) 'gl-ignore)
             (glcp-value nil))

            ;; GL-ERROR call: symbolically execute the arg and store the result in a
            ;; state global, then quit the interpreter.
            ((eq (car x) 'gl-error)
             (if (eql (len x) 2)
                 (b* (((glcp-er result)
                       (interp-term (cadr x) alist hyp clk obligs config
                                    state))
                      (state (acl2::f-put-global 'gl-error-result result state)))
                   (glcp-interp-error
                    (acl2::msg
                     "Error: GL-ERROR call encountered.  Data associated with the ~
                      error is accessible using (@ ~x0).~%"
                     'gl-error-result)))
               (glcp-interp-error
                "Error: wrong number of args to GL-ERROR~%")))

            ;; RETURN-LAST - interpret the last argument, i.e. the logical
            ;; value of the term.  Insert exceptions before this point.
            ((eq (car x) 'acl2::return-last)
             (if (eql (len x) 4)
                 (if (equal (cadr x) ''acl2::time$1-raw)
                     (b* (((mv err & time$-args state)
                           (interp-term (caddr x) alist hyp clk obligs config state)))
                       (mbe :logic (interp-term (car (last x)) alist hyp clk obligs config state)
                            :exec (if (and (not err) (general-concretep time$-args))
                                      (return-last
                                       'acl2::time$1-raw
                                       (general-concrete-obj time$-args)
                                       (interp-term (car (last x)) alist hyp clk obligs config state))
                                    (time$ (interp-term (car (last x)) alist hyp clk obligs config state)))))
                   (interp-term (car (last x)) alist hyp clk obligs config state))
               (glcp-interp-error
                "Error: wrong number of args to RETURN-LAST~%")))

            ;; X is a function call.
            (t (b* ((fn (car x))

                    ;; Interpret the actuals first.
                    ((glcp-er actuals)
                     (interp-list (cdr x) alist hyp clk obligs config state))

                    ;; This function returns the correct result if the function has
                    ;; a symbolic counterpart which is known to it.
                    ((mv ok ans state)
                     (run-gified fn actuals hyp clk state))
                    ((when ok) (glcp-value ans))

                    ((mv ok ans state)
                     (if (general-concrete-listp actuals)
                         (apply-concrete
                          fn (general-concrete-obj-list actuals) state)
                       (mv nil nil state)))
                    ((when ok) (glcp-value (mk-g-concrete ans)))
                 
                    ((mv erp body formals obligs)
                     (acl2::interp-function-lookup
                      fn obligs (glcp-config->overrides config) (w state)))
                    ((when erp) (glcp-interp-error erp))
                    ((unless (equal (len formals) (len actuals)))
                     (glcp-interp-error
                      (acl2::msg "~
In the function call ~x0, function ~x1 is given ~x2 arguments,
but its arity is ~x3.  Its formal parameters are ~x4."
                                 x fn (len actuals) (len formals) formals))))
                 (interp-term
                  body (pairlis$ formals actuals) hyp (1- clk)
                  obligs config state)))))
    (defun interp-list (x alist hyp clk obligs config state)
      (declare (xargs :measure (make-ord 1 (1+ (nfix clk)) (acl2-count x))
                      :guard (and (natp clk)
                                  (bfr-p hyp)
                                  (pseudo-term-listp x)
                                  (acl2::interp-defs-alistp obligs)
                                  (glcp-config-p config)
                                  (acl2::interp-defs-alistp (glcp-config->overrides config))
                                  (gobject-vals-alistp alist))
                      :stobjs state))
      (if (atom x)
          (glcp-value nil)
        (b* (((glcp-er car)
              (interp-term (car x) alist hyp clk obligs config state))
             ((glcp-er cdr)
              (interp-list (cdr x) alist hyp clk obligs config state)))
          (glcp-value (cons car cdr)))))))

(defconst *glcp-run-parametrized-template*
  '(defun run-parametrized
     (hyp concl untrans-concl vars bindings id obligs config state)
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
            val bindings hyp-bdd id untrans-concl config state)))
       (value (cons (list val-clause cov-clause) obligs2)))))

     ;; abort-unknown abort-ctrex exec-ctrex abort-vacuous nexamples hyp-clk concl-clk
     ;; clause-proc-name overrides  run-before run-after case-split-override


(defconst *glcp-run-cases-template*
  '(defun run-cases
     (param-alist concl untrans-concl vars obligs config state)
     (if (atom param-alist)
         (value (cons nil obligs))
       (b* (((er (cons rest obligs))
             (run-cases
              (cdr param-alist) concl untrans-concl vars obligs config state))
            (hyp (caar param-alist))
            (id (cadar param-alist))
            (g-bindings (cddar param-alist))
            (- (glcp-cases-wormhole (glcp-config->run-before config) id))
            ((er (cons clauses obligs))
             (run-parametrized
              hyp concl untrans-concl vars g-bindings id obligs config state))
            (- (glcp-cases-wormhole (glcp-config->run-after config) id)))
         (value (cons (append clauses rest) obligs))))))

(defconst *glcp-clause-proc-template*
  '(defun clause-proc (clause hints state)
     (b* (((list bindings param-bindings hyp param-hyp concl untrans-concl config) hints)
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
                    hyp params-cov-term params-cov-term params-cov-vars bindings
                    "case-split coverage" 'obligs config state)))
                (- (cw "Case-split coverage OK~%"))
                ((er (cons cases-res-clauses obligs1))
                 (run-cases
                  param-alist concl untrans-concl (collect-vars concl) obligs0 config state)))
             (value (list* hyp-clause concl-clause
                           (append cases-res-clauses
                                   params-cov-res-clauses
                                   (acl2::interp-defs-alist-clauses 
                                    (flush-hons-get-hash-table-link obligs1))))))
         ;; No case-splitting.
         (b* (((er (cons res-clauses obligs))
               (run-parametrized
                hyp concl untrans-concl (collect-vars concl) bindings
                "main theorem" nil config state)))
           (cw "GL symbolic simulation OK~%")
           (value (list* hyp-clause concl-clause
                         (append res-clauses
                                 (acl2::interp-defs-alist-clauses
                                  (flush-hons-get-hash-table-link obligs))))))))))

