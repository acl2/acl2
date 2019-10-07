; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")

(include-book "tools/templates" :dir :system)
(include-book "primitives-stub")
(include-book "def-fgl-rewrite")
(include-book "centaur/meta/def-formula-checks" :dir :system)
(set-state-ok t)


(defmacro def-formula-checks (name fns)
  `(progn (cmr::def-formula-checks ,name ,fns :evl fgl-ev :evl-base-fns *fgl-ev-base-fns*)
          (table fgl-formula-checks ',name
                 (cdr (assoc ',name (table-alist 'cmr::formula-checkers world))))))




(defun def-fgl-meta-fn (name body formula-check-fn prepwork)
  (declare (Xargs :mode :program))
  (acl2::template-subst
   '(define <metafn> ((call fgl-object-p)
                      (interp-st interp-st-bfrs-ok)
                      state)
      :guard (interp-st-bfr-listp (fgl-object-bfrlist call))
      :returns (mv successp
                   rhs
                   bindings
                   new-interp-st
                   new-state)
      :prepwork <prepwork>
      <body>
      ///
      <thms>

      (defret eval-of-<metafn>
        (implies (and successp
                      (equal contexts (interp-st->equiv-contexts interp-st))
                      (fgl-ev-meta-extract-global-facts :state st)
                      <formula-check>
                      (equal (w st) (w state))
                      (interp-st-bfrs-ok interp-st)
                      (interp-st-bfr-listp (fgl-object-bfrlist call))
                      (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                              (interp-st->constraint interp-st)
                                              (interp-st->logicman interp-st))
                      (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                              (interp-st->pathcond interp-st)
                                              (interp-st->logicman interp-st)))
                 (fgl-ev-context-equiv-forall-extensions
                  contexts
                  (fgl-object-eval call env (interp-st->logicman interp-st))
                  rhs
                  (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))))

      (table fgl-metafns '<metafn> t))
   :splice-alist `((<thms> . ,*fgl-meta-rule-thms*)
                   (<formula-check> . 
                                    ,(and formula-check-fn
                                          `((,formula-check-fn st)))))
   :atom-alist `((<metafn> . ,name)
                 (<body> . ,body)
                 (<prepwork> . ,prepwork))
   :str-alist `(("<METAFN>" . ,(symbol-name name)))))


(defmacro def-fgl-meta (name body &key (formula-check) (prepwork))
  (def-fgl-meta-fn name body formula-check prepwork))


(defun def-fgl-primitive-fn (fn formals body name-override formula-check-fn updates-state prepwork)
  (declare (Xargs :mode :program))
  (b* ((primfn (or name-override
                   (intern-in-package-of-symbol
                    (concatenate 'string "FGL-" (symbol-name fn) "-PRIMITIVE")
                    'fgl-package))))
    (acl2::template-subst
     '(define <primfn> ((call fgl-object-p)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        :guard (interp-st-bfr-listp (fgl-object-bfrlist call))
        :returns (mv successp
                     ans
                     new-interp-st
                     new-state)
        :prepwork <prepwork>
        (fgl-object-case call
          :g-apply (if (and (eq call.fn '<fn>)
                            (eql (len call.args) <arity>))
                       (b* (((list <formals>) (fgl-objectlist-fix call.args)))
                         (:@ (not :updates-state)
                          (b* (((mv successp ans interp-st) <body>))
                            (mv successp ans interp-st state)))
                         (:@ :updates-state <body>))
                     (mv nil nil interp-st state))
          :otherwise (mv nil nil interp-st state))
        ///
        <thms>

        (defret eval-of-<fn>-primitive
          (implies (and successp
                        (equal contexts (interp-st->equiv-contexts interp-st))
                        (fgl-ev-meta-extract-global-facts :state st)
                        <formula-check>
                        (equal (w st) (w state))
                        (interp-st-bfrs-ok interp-st)
                        (interp-st-bfr-listp (fgl-object-bfrlist call))
                        (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                (interp-st->constraint interp-st)
                                                (interp-st->logicman interp-st))
                        (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                (interp-st->pathcond interp-st)
                                                (interp-st->logicman interp-st)))
                   (equal (fgl-ev-context-fix contexts
                                              (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
                          (fgl-ev-context-fix contexts
                                              (fgl-object-eval call env (interp-st->logicman interp-st))))))

        (table fgl-primitives '<primfn> '<fn>)
        (add-fgl-primitive <fn> <primfn>)
        )
     :splice-alist `((<formals> . ,formals)
                     (<thms> . ,*fgl-primitive-rule-thms*)
                     (<formula-check> . 
                                      ,(and formula-check-fn
                                            `((,formula-check-fn st)))))
     :atom-alist `((<primfn> . ,primfn)
                   (<fn> . ,fn)
                   (<arity> . ,(len formals))
                   (<body> . ,body)
                   (<prepwork> . ,prepwork))
     :str-alist `(("<FN>" . ,(symbol-name fn)))
     :features (and updates-state '(:updates-state)))))

(defun def-fgl-primitive-as-metafn (fn formals body name-override formula-check-fn updates-state prepwork)
  (declare (Xargs :mode :program))
  (b* ((primfn (or name-override
                   (intern-in-package-of-symbol
                    (concatenate 'string "FGL-" (symbol-name fn) "-PRIMITIVE")
                    'fgl-package))))
    (acl2::template-subst
     '(progn
        (def-fgl-meta <primfn>
          (fgl-object-case call
            :g-apply (if (and (eq call.fn '<fn>)
                              (eql (len call.args) <arity>))
                         (b* (((list <formals>) (fgl-objectlist-fix call.args))
                              (:@ (not :updates-state)
                               ((mv successp ans interp-st) <body>))
                              (:@ :updates-state
                               ((mv successp ans interp-st state) <body>)))
                           (mv successp 'x `((x . ,ans)) interp-st state))
                       (mv nil nil nil interp-st state))
            :otherwise (mv nil nil nil interp-st state))
          :prepwork <prepwork>
          <formula-check>)

        (add-fgl-meta <fn> <primfn>))
     :splice-alist `((<formals> . ,formals)
                     (<formula-check> . 
                                      ,(and formula-check-fn
                                            `(:formula-check ,formula-check-fn))))
     :atom-alist `((<primfn> . ,primfn)
                   (<fn> . ,fn)
                   (<arity> . ,(len formals))
                   (<body> . ,body)
                   (<prepwork> . ,prepwork))
     :str-alist `(("<FN>" . ,(symbol-name fn)))
     :features (and updates-state '(:updates-state))
     :pkg-sym primfn)))


(defmacro def-fgl-primitive (fn formals body &key (fnname) (formula-check) (prepwork) (updates-state))
  `(make-event
    (def-fgl-primitive-fn ',fn ',formals ',body ',fnname ',formula-check ',updates-state ',prepwork)))







(defun member-atoms (x tree)
  (if (Atom tree)
      (equal tree x)
    (or (member-atoms x (car tree))
        (member-atoms x (cdr tree)))))




(defun fgl-primitive-fncall-entries (table last)
  (Declare (Xargs :mode :program))
  (if (atom table)
      `((otherwise ,last))
    (b* ((fn (caar table)))
      (cons (acl2::template-subst
             '(<fn> (<fn> call interp-st state))
             :atom-alist `((<fn> . ,fn)))
            (fgl-primitive-fncall-entries (cdr table) last)))))

(defun formula-check-thms (name table)
  (if (atom table)
      nil
    (b* ((check-name (caar table))
         (thmname (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name check-name) "-WHEN-" (symbol-name name))
                   name)))
      (cons `(defthm ,thmname
               (implies (,name st)
                        (,check-name st))
               :hints (("Goal" :in-theory '(,name ,check-name))))
            (formula-check-thms name (cdr table))))))


(defun install-fgl-primitives-fn (prefix state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       (name-formula-checks (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name prefix) "-FORMULA-CHECKS")
                             prefix))
       (formula-checks-table (table-alist 'fgl-formula-checks wrld))
       (formula-check-fns (set::mergesort (append-alist-vals formula-checks-table)))
       (formula-check-thms (formula-check-thms name-formula-checks formula-checks-table))
       )
    (acl2::template-subst
     '(progn
        ;; (def-fgl-object-eval <prefix> nil :union-previous t)
        (cmr::def-formula-checker <prefix>-formula-checks <formula-check-fns>)
        (progn . <formula-check-thms>)

        ;; (make-event
        ;;  (cons 'progn
        ;;        (instantiate-fgl-primitive-correctness-thms-fn
        ;;         (table-alist 'fgl-primitives (w state)))))

        (define <prefix>-primitive-fncall ((primfn pseudo-fnsym-p)
                                           (call fgl-object-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
          :guard (interp-st-bfr-listp (fgl-object-bfrlist call))
          :returns (mv successp ans new-interp-st new-state)
          :ignore-ok t
          (case (pseudo-fnsym-fix primfn)
            . <entries>) ;;,(fgl-primitive-fncall-entries (table-alist 'fgl-primitives wrld)))
          ///
          <thms>
          (defret eval-of-<fn>
            (implies (and successp
                          (equal contexts (interp-st->equiv-contexts interp-st))
                          (fgl-ev-meta-extract-global-facts :state st)
                          ;; (,name-formula-checks st)
                          (<prefix>-formula-checks st)
                          (equal (w st) (w state))
                          (interp-st-bfrs-ok interp-st)
                          (interp-st-bfr-listp (fgl-object-bfrlist call))
                          (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                  (interp-st->constraint interp-st)
                                                  (interp-st->logicman interp-st))
                          (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                  (interp-st->pathcond interp-st)
                                                  (interp-st->logicman interp-st)))
                     (equal (fgl-ev-context-fix contexts
                                                (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
                            (fgl-ev-context-fix contexts
                                                (fgl-object-eval call env (interp-st->logicman interp-st))))))
          (fty::deffixequiv <prefix>-primitive-fncall))

        ;; bozo, dumb theorem needed to prove fixequiv hook
        (local (defthm pseudo-fnsym-fix-equal-forward
                 (implies (equal (pseudo-fnsym-fix x) (pseudo-fnsym-fix y))
                          (pseudo-fnsym-equiv x y))
                 :rule-classes :forward-chaining))

        (defattach
          ;; BOZO add all these back in as well as substitutions for -concretize functions
          ;; if we support adding new evaluators.
          ;; (fgl-ev <prefix>-ev)
          ;; (fgl-ev-list <prefix>-ev-list)
          ;; (fgl-apply <prefix>-apply :attach nil)
          ;; (fgl-object-eval-fn <prefix>-object-eval-fn :attach nil)
          ;; (fgl-objectlist-eval-fn <prefix>-objectlist-eval-fn :attach nil)
          ;; (fgl-object-alist-eval-fn <prefix>-object-alist-eval-fn :attach nil)
          ;; (fgl-ev-falsify <prefix>-ev-falsify :attach nil)
          ;; (fgl-ev-meta-extract-global-badguy <prefix>-ev-meta-extract-global-badguy :attach nil)
          (fgl-primitive-fncall-stub <prefix>-primitive-fncall)
          (fgl-primitive-formula-checks-stub <prefix>-formula-checks)
          :hints(("Goal"
                  :do-not '(preprocess simplify)
                  :clause-processor dumb-clausify-cp)
                 (let ((term (car (last clause))))
                   (case-match term
                     (('equal (fn . &) . &)
                      `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                        :do-not nil))
                     (& (cond ((member-atoms '<prefix>-primitive-fncall term)
                               '(:do-not nil))
                              (t '(:do-not nil)))))))
          ))
     :str-alist `(("<PREFIX>" ,(symbol-name prefix) . ,prefix))
     :atom-alist `(;; (<all-formulas> . ,all-formulas)
                   ;; (<formula-check-thms> . ,formula-check-thms)
                   (<entries> . ,(fgl-primitive-fncall-entries (table-alist 'fgl-primitives wrld) '(mv nil nil interp-st state)))
                   ;; (<all-formulas> . ,all-formulas)
                   (<formula-check-thms> . ,formula-check-thms)
                   (<formula-check-fns> . ,formula-check-fns))
     :splice-alist `((<thms> . ,*fgl-primitive-rule-thms*)))
    
    ))

(defmacro install-fgl-primitives (name)
  `(make-event
    (install-fgl-primitives-fn ',name state)))


(defun install-fgl-metafns-fn (prefix state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       (name-formula-checks (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name prefix) "-FORMULA-CHECKS")
                             prefix))
       (formula-checks-table (table-alist 'fgl-formula-checks wrld))
       (formula-check-fns (set::mergesort (append-alist-vals formula-checks-table)))
       (formula-check-thms (formula-check-thms name-formula-checks formula-checks-table))
       )
    (acl2::template-subst
     '(progn
        ;; (def-fgl-object-eval <prefix> nil :union-previous t)
        (cmr::def-formula-checker <prefix>-formula-checks <formula-check-fns>)
        (progn . <formula-check-thms>)

        ;; (make-event
        ;;  (cons 'progn
        ;;        (instantiate-fgl-primitive-correctness-thms-fn
        ;;         (table-alist 'fgl-primitives (w state)))))

        (define <prefix>-meta-fncall ((metafn pseudo-fnsym-p)
                                      (call fgl-object-p)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
          :guard (interp-st-bfr-listp (fgl-object-bfrlist call))
          :returns (mv successp rhs bindings new-interp-st new-state)
          :ignore-ok t
          (case (pseudo-fnsym-fix metafn)
            . <entries>) ;;,(fgl-primitive-fncall-entries (table-alist 'fgl-primitives wrld)))
          ///
          <thms>
          (defret eval-of-<fn>
            (implies (and successp
                          (equal contexts (interp-st->equiv-contexts interp-st))
                          (fgl-ev-meta-extract-global-facts :state st)
                          ;; (,name-formula-checks st)
                          (<prefix>-formula-checks st)
                          (equal (w st) (w state))
                          (interp-st-bfrs-ok interp-st)
                          (interp-st-bfr-listp (fgl-object-bfrlist call))
                          (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                  (interp-st->constraint interp-st)
                                                  (interp-st->logicman interp-st))
                          (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                  (interp-st->pathcond interp-st)
                                                  (interp-st->logicman interp-st)))
                     (fgl-ev-context-equiv-forall-extensions
                      contexts
                      (fgl-object-eval call env (interp-st->logicman interp-st))
                      rhs
                      (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))))
          (fty::deffixequiv <prefix>-meta-fncall))

        ;; bozo, dumb theorem needed to prove fixequiv hook
        (local (defthm pseudo-fnsym-fix-equal-forward
                 (implies (equal (pseudo-fnsym-fix x) (pseudo-fnsym-fix y))
                          (pseudo-fnsym-equiv x y))
                 :rule-classes :forward-chaining))

        (defattach
          ;; BOZO add all these back in as well as substitutions for -concretize functions
          ;; if we support adding new evaluators.
          ;; (fgl-ev <prefix>-ev)
          ;; (fgl-ev-list <prefix>-ev-list)
          ;; (fgl-apply <prefix>-apply :attach nil)
          ;; (fgl-object-eval-fn <prefix>-object-eval-fn :attach nil)
          ;; (fgl-objectlist-eval-fn <prefix>-objectlist-eval-fn :attach nil)
          ;; (fgl-object-alist-eval-fn <prefix>-object-alist-eval-fn :attach nil)
          ;; (fgl-ev-falsify <prefix>-ev-falsify :attach nil)
          ;; (fgl-ev-meta-extract-global-badguy <prefix>-ev-meta-extract-global-badguy :attach nil)
          (fgl-meta-fncall-stub <prefix>-meta-fncall)
          (fgl-meta-formula-checks-stub <prefix>-formula-checks)
          :hints(("Goal"
                  :do-not '(preprocess simplify)
                  :clause-processor dumb-clausify-cp)
                 (let ((term (car (last clause))))
                   (case-match term
                     (('equal (fn . &) . &)
                      `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                        :do-not nil))
                     (& (cond ((member-atoms '<prefix>-meta-fncall term)
                               '(:do-not nil))
                              (t '(:do-not nil)))))))
          ))
     :str-alist `(("<PREFIX>" ,(symbol-name prefix) . ,prefix))
     :atom-alist `(;; (<all-formulas> . ,all-formulas)
                   ;; (<formula-check-thms> . ,formula-check-thms)
                   (<entries> . ,(fgl-primitive-fncall-entries (table-alist 'fgl-metafns wrld) '(mv nil nil nil interp-st state)))
                   ;; (<all-formulas> . ,all-formulas)
                   (<formula-check-thms> . ,formula-check-thms)
                   (<formula-check-fns> . ,formula-check-fns))
     :splice-alist `((<thms> . ,*fgl-meta-rule-thms*)))
    
    ))

(defmacro install-fgl-metafns (name)
  `(make-event
    (install-fgl-metafns-fn ',name state)))


