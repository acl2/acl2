; APT (Automated Program Transformations) -- Package
;
; Copyright (C) 2016-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "APT" (append *std-pkg-symbols*
                      '(add-numbered-name-in-use
                        add-suffix-to-fn
                        alist-to-doublets
                        all-calls
                        apply-term
                        apply-term*
                        body
                        conjoin
                        conjoin2
                        control-screen-output
                        cw-event
                        def-error-checker
                        doublets-to-alist
                        dumb-negate-lit
                        ensure-boolean$
                        ensure-boolean-or-auto-and-return-boolean$
                        ensure-doublet-list$
                        ensure-function-defined$
                        ensure-function-guard-verified$
                        ensure-function-has-args$
                        ensure-function-known-measure$
                        ensure-function-logic-mode$
                        ensure-function-name-or-numbered-wildcard$
                        ensure-function-no-stobjs$
                        ensure-function-not-in-termination-thm$
                        ensure-function-number-of-results$
                        ensure-function-singly-recursive$
                        ensure-function/lambda-arity$
                        ensure-function/lambda-closed$
                        ensure-function/lambda-guard-verified-exec-fns$
                        ensure-function/lambda-logic-mode$
                        ensure-function/lambda-no-stobjs$
                        ensure-function/lambda/term-number-of-results$
                        ensure-function/macro/lambda$
                        ensure-list-no-duplicates$
                        ensure-list-subset$
                        ensure-named-formulas
                        ensure-symbol$
                        ensure-symbol-list$
                        ensure-symbol-new-event-name$
                        ensure-term$
                        ensure-term-does-not-call$
                        ensure-term-free-vars-subset$
                        ensure-term-ground$
                        ensure-term-guard-verified-exec-fns$
                        ensure-term-if-call$
                        ensure-term-logic-mode$
                        ensure-term-no-stobjs$
                        fargs
                        formals
                        fquotep
                        fresh-name-in-world-with-$s
                        function-intro-macro
                        fundef-enabledp
                        genvar
                        guard-verified-p
                        implicate
                        impossible
                        install-not-norm-event
                        lambda-body
                        lambda-formals
                        make-lambda
                        measure
                        msg-downcase-first
                        named-formulas-to-thm-events
                        next-numbered-name
                        non-executablep
                        packn
                        pseudo-event-formp
                        pseudo-fn/lambda-p
                        pseudo-lambdap
                        pseudo-tests-and-call-listp
                        recursive-calls
                        recursivep
                        remove-keyword
                        remove-lambdas
                        resolve-numbered-name-wildcard
                        run-when
                        str::intern-list
                        str::symbol-list-names
                        subcor-var
                        subst-expr
                        subst-expr1
                        subst-var
                        symbol-symbol-alistp
                        term-guard-obligation
                        tests-and-call
                        theorem-intro-macro
                        ubody
                        untranslate-lst
                        unwrapped-nonexec-body
                        variablep
                        well-founded-relation)))
