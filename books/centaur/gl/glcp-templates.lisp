; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "tools/flag" :dir :system)

(defconst *glcp-common-inputs*
  '(pathcond clk obligs config bvar-db state))

(defconst *glcp-common-guards*
  '((acl2::interp-defs-alistp obligs)
    (glcp-config-p config)
    (acl2::interp-defs-alistp (glcp-config->overrides config))))

(defconst *glcp-interp-template*
  `(mutual-recursion
    (defun interp-test
      (x alist intro-bvars . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 12 0 0)
                :verify-guards nil
                :guard (and (posp clk)
                            (pseudo-termp x)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* ((clk (1- clk))
           ((glcp-er xobj)
            (interp-term-equivs x alist '(iff) . ,*glcp-common-inputs*)))
        (simplify-if-test xobj intro-bvars . ,*glcp-common-inputs*)))

    (defun interp-term-equivs
      (x alist contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list clk 2020 (acl2-count x) 40)
                :guard (and (natp clk)
                            (pseudo-termp x)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((when (zp clk))
            (glcp-interp-error "The clock ran out.~%"))
           ((glcp-er xobj)
            (interp-term x alist contexts . ,*glcp-common-inputs*))
           ((mv er xobj) (try-equivalences-loop xobj pathcond contexts clk
                                                (glcp-config->param-bfr config)
                                                bvar-db state)))
        (mv er obligs xobj bvar-db state)))



    (defun interp-term
      (x alist contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 2020 (acl2-count x) 20)
                :well-founded-relation acl2::nat-list-<
                :hints (("goal"
                         :in-theory (e/d** ((:rules-of-class :executable-counterpart :here)
                                            acl2::open-nat-list-<
                                            acl2-count len nfix fix
                                            acl2-count-of-general-consp-car
                                            acl2-count-of-general-consp-cdr
                                            car-cons cdr-cons commutativity-of-+
                                            unicity-of-0 null atom
                                            eq acl2-count-last-cdr-when-cadr-hack
                                            car-cdr-elim natp-compound-recognizer
                                            acl2::zp-compound-recognizer
                                            acl2::posp-compound-recognizer
                                            pos-fix
                                            g-ite-depth-sum-of-gl-args-split-ite-then
                                            g-ite-depth-sum-of-gl-args-split-ite-else
                                            g-ite->test-acl2-count-decr
                                            g-ite->then-acl2-count-decr
                                            g-ite->else-acl2-count-decr
                                            g-apply->args-acl2-count-thm
                                            acl2-count-of-car-g-apply->args
                                            acl2-count-of-cadr-g-apply->args
                                            acl2-count-of-car
                                            (:type-prescription acl2-count)
                                            (:t len)))))
                :verify-guards nil
                :guard (and (posp clk)
                            (pseudo-termp x)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((when (null x)) (glcp-value nil))
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
                             alist . ,*glcp-common-inputs*))
               (formals (car (cdar x)))
               (body (car (cdr (cdar x)))))
              (if (and (mbt (and (equal (len actuals) (len formals))
                                 (symbol-listp formals)))
                       (acl2::fast-no-duplicatesp formals)
                       (not (member-eq nil formals)))
                  (interp-term body (pairlis$ formals actuals)
                               contexts . ,*glcp-common-inputs*)
                (glcp-interp-error (acl2::msg "Badly formed lambda application: ~x0~%"
                                              x)))))
           ((when (eq (car x) 'if))
            (let ((test (car (cdr x)))
                  (tbr (car (cdr (cdr x))))
                  (fbr (car (cdr (cdr (cdr x))))))
              (interp-if/or test tbr fbr alist contexts . ,*glcp-common-inputs*)))

           ((when (eq (car x) 'gl-aside))
            (if (eql (len x) 2)
                (prog2$ (gl-aside-wormhole (cadr x) alist)
                        (glcp-value nil))
              (glcp-interp-error "Error: wrong number of args to GL-ASIDE~%")))
           ((when (eq (car x) 'gl-ignore))
            (glcp-value nil))
           ((when (eq (car x) 'gl-hide))
            (glcp-value (gl-term-to-apply-obj x alist)))
           ((when (eq (car x) 'gl-error))
            (if (eql (len x) 2)
                (b* (((glcp-er result)
                      (interp-term (cadr x)
                                   alist nil . ,*glcp-common-inputs*))
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
                    (b* (((mv err & time$-args bvar-db state)
                          (let ((clk (1- clk)))
                            (interp-term-equivs
                             (caddr x)
                             alist nil . ,*glcp-common-inputs*))))
                      (mbe :logic (interp-term
                                   (car (last x)) alist contexts . ,*glcp-common-inputs*)
                           :exec
                           (if (and (not err)
                                    (general-concretep time$-args))
                               (return-last
                                'acl2::time$1-raw
                                (general-concrete-obj time$-args)
                                (interp-term (car (last x))
                                             alist contexts . ,*glcp-common-inputs*))
                             (time$
                              (interp-term (car (last x))
                                           alist contexts . ,*glcp-common-inputs*)))))
                  (interp-term (car (last x))
                               alist contexts . ,*glcp-common-inputs*))
              (glcp-interp-error "Error: wrong number of args to RETURN-LAST~%")))
           (fn (car x))
           ;; outside-in rewriting?
           ((glcp-er actuals)
            (interp-list (cdr x)
                         alist . ,*glcp-common-inputs*)))
        (interp-fncall-ifs fn actuals x contexts . ,*glcp-common-inputs*)))

    (defun interp-fncall-ifs
      (fn actuals x contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 1919 (g-ite-depth-sum actuals) 20)
                :guard (and (posp clk)
                            (symbolp fn)
                            (contextsp contexts)
                            (not (eq fn 'quote))
                            (true-listp actuals)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((unless (glcp-lift-ifsp fn (glcp-config->lift-ifsp config)
                                    (w state)))
            (interp-fncall fn actuals x contexts . ,*glcp-common-inputs*))
           ((mv has-if test then-args else-args)
            (gl-args-split-ite actuals))
           ((unless has-if)
            (interp-fncall fn actuals x contexts . ,*glcp-common-inputs*))
           ((glcp-er test-bfr)
            (simplify-if-test test t . ,*glcp-common-inputs*))
           ((glcp-er then-obj)
            (maybe-interp-fncall-ifs fn then-args x contexts test-bfr
                                     . ,*glcp-common-inputs*))
           ((glcp-er else-obj)
            (maybe-interp-fncall-ifs fn else-args x contexts (bfr-not test-bfr)
                                     . ,*glcp-common-inputs*)))
        (merge-branches test-bfr then-obj else-obj nil contexts . ,*glcp-common-inputs*)))


    (defun maybe-interp-fncall-ifs (fn actuals x contexts branchcond . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 1919 (g-ite-depth-sum actuals) 45)
                :verify-guards nil
                :guard (and (posp clk)
                            (symbolp fn)
                            (contextsp contexts)
                            (not (eq fn 'quote))
                            (true-listp actuals)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (let ((branchcond (hyp-fix branchcond pathcond)))
        (if branchcond
            (let ((pathcond (bfr-and pathcond branchcond)))
              (interp-fncall-ifs
               fn actuals x contexts . ,*glcp-common-inputs*))
          (glcp-value nil))))

    (defun interp-fncall
      (fn actuals x contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 1414 0 20)
                :guard (and (posp clk)
                            (symbolp fn)
                            (not (eq fn 'quote))
                            (true-listp actuals)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* ((uninterp (cdr (hons-assoc-equal fn (table-alist
                                                'gl-uninterpreted-functions (w
                                                                             state)))))
           ((mv fncall-failed ans)
            (if (and (not uninterp)
                     (general-concrete-listp actuals))
                (acl2::magic-ev-fncall fn (general-concrete-obj-list actuals)
                                       state t nil)
              (mv t nil)))
           ((unless fncall-failed)
            (glcp-value (mk-g-concrete ans)))
           ((mv erp obligs successp term bindings bvar-db state)
            (rewrite
             fn actuals :fncall contexts . ,*glcp-common-inputs*))
           ((when erp) (mv erp obligs nil bvar-db state))
           ((when successp)
            (b* ((clk (1- clk)))
              (interp-term-equivs term bindings contexts . ,*glcp-common-inputs*)))
           ((mv ok ans)
            (run-gified fn actuals pathcond clk config bvar-db state))
           ((when ok) (glcp-value ans))
           ((when (cdr (hons-assoc-equal fn (table-alist 'gl-uninterpreted-functions (w state)))))
            (glcp-value (g-apply fn actuals)))
           ((mv erp body formals obligs1)
            (acl2::interp-function-lookup fn
                                          obligs (glcp-config->overrides config)
                                          (w state)))
           ((when erp) (glcp-interp-error erp))
           (obligs obligs1)
           ((unless (equal (len formals) (len actuals)))
            (glcp-interp-error
             (acl2::msg
              "~
In the function call ~x0, function ~x1 is given ~x2 arguments,
but its arity is ~x3.  Its formal parameters are ~x4."
              x fn (len actuals)
              (len formals)
              formals)))
           (clk (1- clk)))
        (interp-term-equivs body (pairlis$ formals actuals)
                            contexts . ,*glcp-common-inputs*)))

    (defun interp-if/or (test tbr fbr alist contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 2020 (+ (acl2-count test)
                                                     (acl2-count tbr)
                                                     (acl2-count fbr)) 60)
                :verify-guards nil
                :guard (and (posp clk)
                            (pseudo-termp test)
                            (pseudo-termp tbr)
                            (pseudo-termp fbr)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (if (hqual test tbr)
          (interp-or test fbr alist contexts . ,*glcp-common-inputs*)
        (interp-if test tbr fbr alist contexts . ,*glcp-common-inputs*)))

    (defun maybe-interp (x alist contexts branchcond . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 2020 (acl2-count x) 45)
                :verify-guards nil
                :guard (and (natp clk)
                            (pseudo-termp x)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (let ((branchcond (hyp-fix branchcond pathcond)))
        (if branchcond
            (let ((pathcond (bfr-and pathcond branchcond)))
              (interp-term-equivs
               x alist contexts . ,*glcp-common-inputs*))
          (glcp-value nil))))

    (defun interp-or (test fbr alist contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 2020 (+ (acl2-count test)
                                                     (acl2-count fbr)) 50)
                :verify-guards nil
                :guard (and (posp clk)
                            (pseudo-termp test)
                            (pseudo-termp fbr)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((glcp-er test-obj)
            (interp-term-equivs
             test alist (glcp-or-test-contexts contexts)  . ,*glcp-common-inputs*))
           ((glcp-er test-bfr)
            (simplify-if-test test-obj t . ,*glcp-common-inputs*))
           ((glcp-er else)
            (maybe-interp
             fbr alist contexts (bfr-not test-bfr) . ,*glcp-common-inputs*)))
        (merge-branches test-bfr test-obj else nil contexts . ,*glcp-common-inputs*)))

    (defun interp-if (test tbr fbr alist contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 2020 (+ (acl2-count test)
                                                     (acl2-count tbr)
                                                     (acl2-count fbr)) 50)
                :verify-guards nil
                :guard (and (posp clk)
                            (pseudo-termp test)
                            (pseudo-termp tbr)
                            (pseudo-termp fbr)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((glcp-er test-bfr)
            (interp-test
             test alist t . ,*glcp-common-inputs*))
           ((glcp-er then)
            (maybe-interp
             tbr alist contexts test-bfr . ,*glcp-common-inputs*))
           ((glcp-er else)
            (maybe-interp
             fbr alist contexts (bfr-not test-bfr) . ,*glcp-common-inputs*)))
        (merge-branches test-bfr then else nil contexts . ,*glcp-common-inputs*)))

    (defun merge-branches (test-bfr then else switchedp contexts . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list (pos-fix clk) 1818
                               (+ (acl2-count then) (acl2-count else))
                               (if switchedp 20 30))
                :verify-guards nil
                :guard (and (posp clk)
                            (contextsp contexts)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((when (eq test-bfr t)) (glcp-value then))
           ((when (eq test-bfr nil)) (glcp-value else))
           ((when (hons-equal then else)) (glcp-value then))
           ((when (or (atom then)
                      (and (g-keyword-symbolp (tag then))
                           (or (not (eq (tag then) :g-apply))
                               (not (symbolp (g-apply->fn then)))
                               (eq (g-apply->fn then) 'quote)))))
            (if switchedp
                (merge-branch-subterms
                 (bfr-not test-bfr) else then . ,*glcp-common-inputs*)
              (merge-branches (bfr-not test-bfr) else then t contexts . ,*glcp-common-inputs*)))
           (fn (if (eq (tag then) :g-apply)
                   (g-apply->fn then)
                 'cons))
           (rules (glcp-get-branch-merge-rules fn (w state)))
           (runes (rewrite-rules->runes rules))
           ((mv erp obligs successp term bindings bvar-db state)
            (rewrite-apply-rules
             rules runes 'if (list (g-boolean test-bfr) then else)
             contexts . ,*glcp-common-inputs*))
           ((when erp)
            (mv erp obligs nil bvar-db state))
           ((when successp)
            (b* ((clk (1- clk)))
              (interp-term-equivs term bindings contexts . ,*glcp-common-inputs*))))
        (if switchedp
            (merge-branch-subterms (bfr-not test-bfr) else then . ,*glcp-common-inputs*)
          (merge-branches (bfr-not test-bfr) else then t contexts . ,*glcp-common-inputs*))))

    (defun merge-branch-subterms (test-bfr then else
                                           . ,*glcp-common-inputs*)
      (declare (xargs :measure (list (pos-fix clk) 1818
                                     (+ (acl2-count then) (acl2-count else))
                                     15)
                      :guard (and (posp clk)
                                  . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((when (or (atom then)
                      (atom else)
                      (xor (eq (tag then) :g-apply)
                           (eq (tag else) :g-apply))
                      (not (or (eq (tag then) :g-apply)
                               (and (general-consp then)
                                    (general-consp else))))
                      (and (eq (tag then) :g-apply)
                           (not (and (symbolp (g-apply->fn then))
                                     (not (eq (g-apply->fn then) 'quote))
                                     (eq (g-apply->fn then) (g-apply->fn else))
                                     (int= (len (g-apply->args then))
                                           (len (g-apply->args else))))))))
            (glcp-value (gobj-ite-merge test-bfr then else pathcond)))
           ((unless (eq (tag then) :g-apply))
            (b* (((glcp-er car) (merge-branches test-bfr
                                                (general-consp-car then)
                                                (general-consp-car else)
                                                nil nil . ,*glcp-common-inputs*))
                 ((glcp-er cdr) (merge-branches test-bfr
                                                (general-consp-cdr then)
                                                (general-consp-cdr else)
                                                nil nil . ,*glcp-common-inputs*)))
              (glcp-value ;; (gl-cons-split-ite car cdr)
               (gl-cons-maybe-split car cdr
                                    (glcp-config->split-conses config)
                                    (w state)))))
           ((glcp-er args)
            (merge-branch-subterm-lists test-bfr
                                        (g-apply->args then)
                                        (g-apply->args else)
                                        . ,*glcp-common-inputs*)))
        (glcp-value (gl-fncall-maybe-split
                     (g-apply->fn then) args
                     (glcp-config->split-fncalls config)
                     (w state)))))

    (defun merge-branch-subterm-lists (test-bfr then else
                                                . ,*glcp-common-inputs*)
      (declare (xargs :measure (list (pos-fix clk) 1818
                                     (+ (acl2-count then) (acl2-count else))
                                     15)
                      :guard (and (posp clk)
                                  (equal (len then) (len else))
                                  . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (b* (((when (atom then))
            (glcp-value nil))
           ((cons then1 thenr) then)
           ((cons else1 elser) else)
           ((glcp-er rest) (merge-branch-subterm-lists test-bfr thenr elser
                                                       . ,*glcp-common-inputs*))
           ((glcp-er first) (merge-branches test-bfr then1 else1 nil nil
                                            . ,*glcp-common-inputs*)))
        (glcp-value (cons first rest))))

    ;; returns a glcp-value of a bfr
    (defun simplify-if-test (test-obj intro-bvars . ,*glcp-common-inputs*)
      (declare (xargs
                :measure (list clk 1300 (acl2-count test-obj) 10)
                :verify-guards nil
                :guard (and (natp clk)
                            . ,*glcp-common-guards*)
                :stobjs (bvar-db state)))
      (if (atom test-obj)
          (glcp-value (and test-obj t))
        (pattern-match test-obj
          ((g-boolean bfr) (glcp-value (hyp-fix bfr pathcond)))
          ((g-number &) (glcp-value t))
          ((g-concrete v) (glcp-value (and v t)))
          ((g-var &)
           (b* (((mv bvar bvar-db) (add-term-bvar-unique test-obj bvar-db))
                (bvar-db (maybe-add-equiv-term test-obj bvar bvar-db state)))
             (glcp-value (hyp-fix
                          (bfr-to-param-space (glcp-config->param-bfr config)
                                              (bfr-var bvar))
                          pathcond))))
          ((g-ite test then else)
           (b* ((hyp pathcond)
                ((glcp-er test-bfr) (simplify-if-test
                                     test intro-bvars . ,*glcp-common-inputs*))
                (then-hyp test-bfr)
                (else-hyp (bfr-not test-bfr))
                ((glcp-er then-bfr)
                 (if then-hyp
                     (let ((pathcond (bfr-and hyp then-hyp)))
                       (simplify-if-test
                        then intro-bvars . ,*glcp-common-inputs*))
                   (glcp-value nil)))
                ((glcp-er else-bfr)
                 (if else-hyp
                     (let ((pathcond (bfr-and hyp else-hyp)))
                       (simplify-if-test
                        else intro-bvars . ,*glcp-common-inputs*))
                   (glcp-value nil))))
             ;; Seems unlikely that hyp-fix would give any reductions here:
             ;; maybe test this
             (glcp-value (bfr-ite test-bfr then-bfr else-bfr))))
          ((g-apply fn args)
           (b* (((when (or (not (symbolp fn))
                           (eq fn 'quote)))
                 (glcp-interp-error (acl2::msg "Non function symbol in g-apply: ~x0" fn)))

                ((when (and (eq fn 'not)
                            (eql (len args) 1)))
                 (b* (((glcp-er neg-bfr)
                       (simplify-if-test (first args) intro-bvars . ,*glcp-common-inputs*)))
                   (glcp-value (bfr-not neg-bfr))))
                ((when (and (eq fn 'equal)
                            (eql (len args) 2)
                            (or (eq (car args) nil)
                                (eq (cadr args) nil))))
                 (b* (((glcp-er neg-bfr)
                       (simplify-if-test (or (car args) (cadr args)) intro-bvars . ,*glcp-common-inputs*)))
                   (glcp-value (bfr-not neg-bfr))))

                ((when (and (eq fn 'gl-force-check)
                            (eql (len args) 1)))
                 (b* (((glcp-er sub-bfr)
                       (simplify-if-test (first args) intro-bvars . ,*glcp-common-inputs*)))
                   (glcp-value (bfr-constcheck sub-bfr))))

                ((when (and (eq fn 'gl-force-check-strong)
                            (eql (len args) 1)))
                 (b* (((glcp-er sub-bfr)
                       (simplify-if-test (first args) intro-bvars . ,*glcp-common-inputs*)))
                   (glcp-value (bfr-constcheck-pathcond sub-bfr pathcond))))

                ((when (and (eq fn 'gl-force-true)
                            (eql (len args) 1)))
                 (b* (((glcp-er sub-bfr)
                       (simplify-if-test (first args) intro-bvars . ,*glcp-common-inputs*)))
                   (glcp-value (bfr-check-true sub-bfr))))

                ((when (and (eq fn 'gl-force-false)
                            (eql (len args) 1)))
                 (b* (((glcp-er sub-bfr)
                       (simplify-if-test (first args) intro-bvars . ,*glcp-common-inputs*)))
                   (glcp-value (bfr-check-false sub-bfr))))

                ((when (zp clk))
                 (glcp-interp-error "Clock ran out in simplify-if-test"))

                ((mv erp obligs successp term bindings bvar-db state)
                 (rewrite fn args :if-test '(iff) . ,*glcp-common-inputs*))
                ((when erp) (mv erp obligs nil bvar-db state))
                ((when successp)
                 (interp-test term bindings intro-bvars
                              . ,*glcp-common-inputs*))
                ((unless intro-bvars)
                 (mv :intro-bvars-fail obligs nil bvar-db state))
                ((mv bvar bvar-db) (add-term-bvar-unique test-obj bvar-db))
                (bvar-db (maybe-add-equiv-term test-obj bvar bvar-db state)))
             (glcp-value (hyp-fix (bfr-to-param-space (glcp-config->param-bfr config)
                                                      (bfr-var bvar))
                                  pathcond))))
          (& ;; cons
           (glcp-value t)))))




    (defun rewrite (fn actuals rwtype contexts . ,*glcp-common-inputs*)
      (declare (xargs :stobjs (bvar-db state)
                      :guard (and (posp clk)
                                  (symbolp fn)
                                  (not (eq fn 'quote))
                                  (contextsp contexts)
                                  . ,*glcp-common-guards*)
                      :measure (list (pos-fix clk) 1212 0 0))
               (ignorable rwtype))

      ;; (mv erp obligs1 successp term bindings bvar-db state)
      (b* ((rules (cdr (hons-assoc-equal fn (table-alist 'gl-rewrite-rules (w state)))))
           ;; or perhaps we should pass the table in the obligs? see if this is
           ;; expensive
           ((unless (and rules (true-listp rules))) ;; optimization (important?)
            (mv nil obligs nil nil nil bvar-db state))
           (fn-rewrites (getprop fn 'acl2::lemmas nil 'current-acl2-world (w state))))
        (rewrite-apply-rules
         fn-rewrites rules fn actuals contexts . ,*glcp-common-inputs*)))


    (defun rewrite-apply-rules
      (fn-rewrites rules fn actuals contexts . ,*glcp-common-inputs*)
      (declare (xargs :stobjs (bvar-db state)
                      :guard (and (true-listp rules)
                                  (posp clk)
                                  (symbolp fn)
                                  (not (eq fn 'quote))
                                  (contextsp contexts)
                                  . ,*glcp-common-guards*)
                      :measure (list (pos-fix clk) 88 (len fn-rewrites) 0)))
      (b* (((when (atom fn-rewrites))
            ;; no more rules, fail
            (mv nil obligs nil nil nil bvar-db state))
           (rule (car fn-rewrites))
           ((unless (acl2::weak-rewrite-rule-p rule))
            (cw "malformed rewrite rule?? ~x0~%" rule)
            (rewrite-apply-rules
             (cdr fn-rewrites) rules fn actuals contexts . ,*glcp-common-inputs*))
           ((unless (member-equal (acl2::rewrite-rule->rune rule) rules))
            (rewrite-apply-rules
             (cdr fn-rewrites) rules fn actuals contexts . ,*glcp-common-inputs*))
           ((mv erp obligs successp term bindings bvar-db state)
            (rewrite-apply-rule
             rule fn actuals contexts . ,*glcp-common-inputs*))
           ((when erp)
            (mv erp obligs nil nil nil bvar-db state))
           ((when successp)
            (mv nil obligs successp term bindings bvar-db state)))
        (rewrite-apply-rules
         (cdr fn-rewrites) rules fn actuals contexts . ,*glcp-common-inputs*)))

    (defun rewrite-apply-rule
      (rule fn actuals contexts . ,*glcp-common-inputs*)
      (declare (xargs :stobjs (bvar-db state)
                      :guard (and (acl2::weak-rewrite-rule-p rule)
                                  (posp clk)
                                  (symbolp fn)
                                  (not (eq fn 'quote))
                                  (contextsp contexts)
                                  . ,*glcp-common-guards*)
                      :measure (list (pos-fix clk) 44 0 0)))
      (b* (((rewrite-rule rule) rule)
           ((unless (and (symbolp rule.equiv)
                         (not (eq rule.equiv 'quote))
                         ;; (ensure-equiv-relationp rule.equiv (w state))
                         (not (eq rule.subclass 'acl2::meta))
                         (pseudo-termp rule.lhs)
                         (consp rule.lhs)
                         (eq (car rule.lhs) fn)))
            (cw "malformed gl rewrite rule (lhs)?? ~x0~%" rule)
            (mv nil obligs nil nil nil bvar-db state))
           ((unless (or (eq rule.equiv 'equal)
                        ;; bozo check refinements
                        (member rule.equiv contexts)))
            (mv nil obligs nil nil nil bvar-db state))
           ((mv unify-ok gobj-bindings)
            (glcp-unify-term/gobj-list (cdr rule.lhs) actuals nil))
           ((unless unify-ok)
            (mv nil obligs nil nil nil bvar-db state))
           ((unless (pseudo-term-listp rule.hyps))
            (cw "malformed gl rewrite rule (hyps)?? ~x0~%" rule)
            (mv nil obligs nil nil nil bvar-db state))
           ((mv erp obligs hyps-ok gobj-bindings bvar-db state)
            (relieve-hyps rule.rune rule.hyps gobj-bindings . ,*glcp-common-inputs*))
           ((when erp)
            (mv erp obligs nil nil nil bvar-db state))
           ((unless hyps-ok)
            (mv nil obligs nil nil nil bvar-db state))
           ((unless (pseudo-termp rule.rhs))
            (cw "malformed gl rewrite rule (rhs)?? ~x0~%" rule)
            (mv nil obligs nil nil nil bvar-db state)))
        (mv nil obligs t rule.rhs gobj-bindings bvar-db state)))

    (defun relieve-hyps (rune hyps bindings . ,*glcp-common-inputs*)
      (declare (xargs :stobjs (bvar-db state)
                      :guard (and (pseudo-term-listp hyps)
                                  (posp clk)
                                  . ,*glcp-common-guards*)
                      :measure (list (pos-fix clk) 22 (len hyps) 0))
               (ignorable rune))
      (b* (((when (atom hyps))
            (mv nil obligs t bindings bvar-db state))
           ((mv erp obligs ok bindings bvar-db state)
            (relieve-hyp rune (car hyps) bindings . ,*glcp-common-inputs*))
           ((when (or erp (not ok)))
            (mv erp obligs ok bindings bvar-db state)))
        (relieve-hyps rune (cdr hyps) bindings . ,*glcp-common-inputs*)))

    (defun relieve-hyp (rune hyp bindings . ,*glcp-common-inputs*)
      (declare (xargs :stobjs (bvar-db state)
                      :guard (and (pseudo-termp hyp)
                                  (posp clk)
                                  . ,*glcp-common-guards*)
                      :measure (list (pos-fix clk) 15 0 0))
               (ignorable rune))
      ;; "Simple" version for now; maybe free variable bindings, syntaxp, etc later...
      (b* (((when (and (consp hyp) (eq (car hyp) 'synp)))
            (b* (((mv erp successp bindings)
                  (glcp-relieve-hyp-synp hyp bindings state)))
              (mv erp obligs successp bindings bvar-db state)))
           ((mv erp obligs bfr bvar-db state)
            (interp-test hyp bindings nil . ,*glcp-common-inputs*))
           ((when erp)
            (mv nil obligs nil bindings bvar-db state))
           ((when (eq bfr t))
            (mv nil obligs t bindings bvar-db state)))
        (mv nil obligs nil bindings bvar-db state)))

    (defun interp-list
      (x alist . ,*glcp-common-inputs*)
      (declare
       (xargs
        :measure (list (pos-fix clk) 2020 (acl2-count x) 20)
        :guard (and (natp clk)
                    (pseudo-term-listp x)
                    . ,*glcp-common-guards*)
        :stobjs (bvar-db state)))
      (if (atom x)
          (glcp-value nil)
        (b* (((glcp-er car)
              (interp-term-equivs (car x)
                                  alist nil . ,*glcp-common-inputs*))
             ((glcp-er cdr)
              (interp-list (cdr x)
                           alist . ,*glcp-common-inputs*)))
          (glcp-value (cons car cdr)))))))

(defconst *glcp-interp-wrappers-template*
  `(progn
     (defund interp-top-level-term
       (term alist . ,*glcp-common-inputs*)
       (declare (xargs :guard (and (pseudo-termp term)
                                   (natp clk)
                                   . ,*glcp-common-guards*)
                       :stobjs (bvar-db state)
                       :verify-guards nil))
       (b* ((config (glcp-config-update-term term config)))
         (interp-test
          term alist t . ,*glcp-common-inputs*)))

     (defund interp-concl
       (term alist pathcond clk obligs config bvar-db1 bvar-db state)
       (declare (xargs :guard (and (pseudo-termp term)
                                   (natp clk)
                                   . ,*glcp-common-guards*)
                       :stobjs (bvar-db bvar-db1 state)
                       :verify-guards nil))
       (b* ((al (gobj-alist-to-param-space alist pathcond))
            (bvar-db (init-bvar-db (base-bvar bvar-db1) bvar-db))
            (bvar-db (parametrize-bvar-db pathcond bvar-db1 bvar-db))
            (config (glcp-config-update-param pathcond config))
            ((unless pathcond)
             (mv nil obligs nil bvar-db state))
            (pathcond (bfr-to-param-space pathcond pathcond)))
         (interp-top-level-term
          term al . ,*glcp-common-inputs*)))

     (defund interp-hyp/concl
       (hyp concl alist clk obligs config next-bvar bvar-db bvar-db1 state)
       (declare (xargs :guard (and (pseudo-termp hyp)
                                   (pseudo-termp concl)
                                   (natp clk)
                                   . ,*glcp-common-guards*)
                       :stobjs (bvar-db bvar-db1 state)
                       :verify-guards nil))
       (b* ((bvar-db (init-bvar-db next-bvar bvar-db))
            (bvar-db1 (init-bvar-db next-bvar bvar-db1))
            (config (glcp-config-update-param t config))
            ((mv er obligs hyp-bfr bvar-db state)
             (let ((pathcond t))
               (interp-top-level-term
                hyp alist . ,*glcp-common-inputs*)))
            ((when er)
             (mv er obligs hyp-bfr nil bvar-db bvar-db1 state))
            ((when (and (glcp-config->abort-vacuous config)
                        (not hyp-bfr)))
             (mv "Hypothesis is not satisfiable"
                 obligs hyp-bfr nil bvar-db bvar-db1 state))
            (- (and (not hyp-bfr)
                    (cw "Note: hypothesis is not satisfiable~%")))
            ((mv er obligs concl-bfr bvar-db1 state)
             (interp-concl
              concl alist hyp-bfr clk obligs config bvar-db bvar-db1 state)))
         (mv er obligs hyp-bfr concl-bfr bvar-db bvar-db1 state)))))


#||

"GL"
(trace$ (glcp-rewrite-fncall-apply-rule
         :cond (b* (((rewrite-rule rule) rule)
                    ((unless (eq (cadr rule.rune) 'logand-of-logapp))
                     nil)
                    ((unless (and (eq rule.equiv 'equal)
                                  (not (eq rule.subclass 'acl2::meta))
                                  (pseudo-termp rule.lhs)
                                  (consp rule.lhs)
                                  (eq (car rule.lhs) fn)))
                     (cw "malformed gl rewrite rule (lhs)?? ~x0~%" rule))
                    ((mv unify-ok ?gobj-bindings)
                     (glcp-unify-term/gobj-list (cdr rule.lhs) actuals nil)))
                 unify-ok)))


||#

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
          ((unless (and (acl2::fast-no-duplicatesp (shape-spec-list-indices obj))
                        (acl2::fast-no-duplicatesp-equal (shape-spec-list-vars obj))))
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
          (config (change-glcp-config config :shape-spec-alist bindings))
          (al (shape-specs-to-interp-al bindings))
          (cov-clause
           (list '(not (gl-cp-hint 'coverage))
                 (dumb-negate-lit hyp)
                 (shape-spec-list-oblig-term
                  obj
                  (strip-cars bindings))))
          ((acl2::local-stobjs bvar-db bvar-db1)
           (mv erp val state bvar-db bvar-db1))
          (next-bvar (shape-spec-max-bvar-list (strip-cadrs bindings)))
          ((mv er obligs1 hyp-bfr concl-bfr bvar-db bvar-db1 state)
           (interp-hyp/concl
            hyp concl al config.concl-clk obligs config next-bvar bvar-db
            bvar-db1 state))
          ((when er)
           (flush-hons-get-hash-table-link obligs1)
           (mv er nil state bvar-db bvar-db1))
          ((mv erp val-clause state)
           (glcp-analyze-interp-result
            concl-bfr bindings hyp-bfr id concl config bvar-db1 state))
          ((when erp)
           (mv erp nil state bvar-db bvar-db1))
          ((mv erp val state)
           (value (list val-clause cov-clause obligs1))))
       (mv erp val state bvar-db bvar-db1))))

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
            ((er (list val-clause cov-clause obligs))
             (run-parametrized
              hyp concl vars g-bindings id obligs config state))
            (- (glcp-cases-wormhole (glcp-config->run-after config) id)))
         (value (cons (list* val-clause cov-clause rest) obligs))))))

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
                ((er (list params-cov-res-clause
                           params-cov-cov-clause obligs0))
                 (if (glcp-config->case-split-override config)
                     (value (list `((not (gl-cp-hint 'casesplit))
                                    (not ,hyp)
                                    ,params-cov-term)
                                  '('t)
                                  'obligs))
                   (run-parametrized
                    hyp params-cov-term params-cov-vars bindings
                    "case-split coverage" 'obligs config state)))
                (- (cw "Case-split coverage OK~%"))
                ((er (cons cases-res-clauses obligs1))
                 (run-cases
                  param-alist concl (collect-vars concl) obligs0 config state)))
             (clear-memoize-table 'glcp-get-branch-merge-rules)
             (value (list* hyp-clause concl-clause
                           (append cases-res-clauses
                                   (list* params-cov-res-clause
                                          params-cov-cov-clause
                                          (acl2::interp-defs-alist-clauses
                                           (flush-hons-get-hash-table-link obligs1)))))))
         ;; No case-splitting.
         (b* (((er (list res-clause cov-clause obligs))
               (run-parametrized
                hyp concl (collect-vars concl) bindings
                "main theorem" nil config state)))
           (cw "GL symbolic simulation OK~%")
           (clear-memoize-table 'glcp-get-branch-merge-rules)
           (value (list* hyp-clause concl-clause
                         res-clause cov-clause
                         (acl2::interp-defs-alist-clauses
                          (flush-hons-get-hash-table-link obligs)))))))))

