; GL - A Symbolic Simulation Framework for ACL2
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
(set-state-ok t)


(defun gl-primitive-formula-checks (formulas state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom formulas)
      nil
    (cons `(equal (meta-extract-formula ',(car formulas) state)
                  ',(meta-extract-formula (car formulas) state))
          (gl-primitive-formula-checks (cdr formulas) state))))

(defun def-gl-formula-checks-fn (name formulas state)
  (declare (xargs :stobjs state :mode :program))
  `(define ,name (state)
     :returns (ok)
     (and . ,(gl-primitive-formula-checks formulas state))
     ///
     (table gl-formula-checks ',name ',formulas)))

(defmacro def-gl-formula-checks (name formulas)
  `(make-event
    (def-gl-formula-checks-fn ',name ',formulas state)))

(defun gl-primitive-formula-checks-lemmas (name formulas state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom formulas)
      nil
    (cons `(defthm ,(intern-in-package-of-symbol
                     (concatenate 'string "META-EXTRACT-FORMULA-" (symbol-name (car formulas))
                                  "-WHEN-" (symbol-name name))
                     name)
             (implies (,name state)
                      (equal (meta-extract-formula ',(car formulas) state)
                             ',(meta-extract-formula (car formulas) state)))
             :hints(("Goal" :in-theory (enable ,name))))
          (gl-primitive-formula-checks-lemmas name (cdr formulas) state))))

(defun def-gl-formula-checks-lemmas-fn (name state)
  (declare (xargs :stobjs state :mode :program))
  (let ((formulas (cdr (assoc name (table-alist 'gl-formula-checks (w state))))))
    `(defsection ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name name) "-LEMMAS")
                   name)
       . ,(gl-primitive-formula-checks-lemmas name formulas state))))

(defmacro def-gl-formula-checks-lemmas (name)
  `(make-event
    (def-gl-formula-checks-lemmas-fn ',name state)))


(defun def-gl-primitive-fn (fn formals body name-override formula-check-fn prepwork wrld)
  (declare (Xargs :mode :program))
  (b* ((primfn (or name-override
                   (intern-in-package-of-symbol
                    (concatenate 'string "GL-" (symbol-name fn) "-PRIMITIVE")
                    'gl-package)))
       (eval-prefix (cdr (assoc ':last (table-alist 'fgl-last-evaluator wrld)))))
    (acl2::template-subst
     '(define gl-<fn>-primitive ((args gl-objectlist-p)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :returns (mv successp
                     ans
                     new-interp-st)
        :prepwork <prepwork>
        (if (eql (len args) <arity>)
            (b* (((list <formals>) (gl-objectlist-fix args)))
              <body>)
          (mv nil nil interp-st))
        ///
        <thms>

        (defret get-bvar->term-eval-of-<fn>-primitive
          (b* ((bvar-db (interp-st->bvar-db interp-st)))
            (implies (and (interp-st-bfrs-ok interp-st)
                          (<= (base-bvar$a bvar-db) (nfix n))
                          (< (nfix n) (next-bvar$a bvar-db)))
                     (iff (<prefix>-object-eval (get-bvar->term$a n (interp-st->bvar-db new-interp-st))
                                           env
                                           (interp-st->logicman new-interp-st))
                          (<prefix>-object-eval (get-bvar->term$a n bvar-db)
                                                env
                                                (interp-st->logicman interp-st))))))

        

        (defret major-stack-concretize-of-<fn>
          (implies (interp-st-bfrs-ok interp-st)
                   (equal (<prefix>-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))
                          (<prefix>-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))))

        (defret eval-of-<fn>-primitive
          (implies (and successp
                        (<prefix>-ev-meta-extract-global-facts :state st)
                        <formula-check>
                        (equal (w st) (w state))
                        (interp-st-bfrs-ok interp-st)
                        (interp-st-bfr-listp (gl-objectlist-bfrlist args)))
                   (equal (<prefix>-object-eval ans env (interp-st->logicman new-interp-st))
                          (<prefix>-ev (cons '<fn>
                                             (kwote-lst (<prefix>-objectlist-eval args env (interp-st->logicman interp-st))))
                                       nil))))

        (table gl-primitives '<fn> '<prefix>))
     :splice-alist `((<formals> . ,formals)
                     (<thms> . ,*gl-primitive-thms*)
                     (<formula-check> . 
                                      ,(and formula-check-fn
                                            `((,formula-check-fn st)))))
     :atom-alist `((<primfn> . ,primfn)
                   (<fn> . ,fn)
                   (<arity> . ,(len formals))
                   (<body> . ,body)
                   (<prepwork> . ,prepwork)
                   (<prefix> . ,eval-prefix))
     :str-alist `(("<FN>" . ,(symbol-name fn))
                  ("<PREFIX>" ,(symbol-name eval-prefix) . ,eval-prefix))
     :pkg-sym eval-prefix)))


(defmacro def-gl-primitive (fn formals body &key (fnname) (formula-check) (prepwork))
  `(make-event
    (def-gl-primitive-fn ',fn ',formals ',body ',fnname ',formula-check ',prepwork (w state))))






(defun member-atoms (x tree)
  (if (Atom tree)
      (equal tree x)
    (or (member-atoms x (car tree))
        (member-atoms x (cdr tree)))))
  
(defun def-gl-object-eval-inst-fn (thmname orig-prefix wrld)
  (declare (xargs :mode :program))
  (b* ((curr-prefix (cdr (assoc :last (table-alist 'fgl-last-evaluator wrld)))))
    ;; BOZO The functional substitution needs to be extended with all the -concretize functions,
    ;; once we make a macro that defines a set of them for a new prefix.
    (acl2::template-subst
     '(acl2::def-functional-instance
        <thmname>-for-<curr-prefix>-ev
        <thmname>
        ((<prefix>-ev <curr-prefix>-ev)
         (<prefix>-ev-list <curr-prefix>-ev-list)
         (<prefix>-apply <curr-prefix>-apply)
         (<prefix>-object-eval-fn <curr-prefix>-object-eval-fn)
         (<prefix>-objectlist-eval-fn <curr-prefix>-objectlist-eval-fn)
         (<prefix>-object-alist-eval-fn <curr-prefix>-object-alist-eval-fn)
         (<prefix>-ev-falsify <curr-prefix>-ev-falsify)
         (<prefix>-ev-meta-extract-global-badguy <curr-prefix>-ev-meta-extract-global-badguy))
        :hints(("Goal"
                :in-theory (enable <curr-prefix>-ev-of-fncall-args
                                          <curr-prefix>-ev-of-nonsymbol-atom
                                          <curr-prefix>-ev-of-bad-fncall)
                :do-not '(preprocess simplify))
               '(:clause-processor dumb-clausify-cp)
               (let ((term (car (last clause))))
                 (case-match term
                   (('equal (fn . &) . &)
                    (cond ((member fn '(<curr-prefix>-ev
                                        <curr-prefix>-ev-list))
                           '(:do-not nil))
                          ;; ((member fn '(<curr-prefix>-ev-falsify
                          ;;               <curr-prefix>-meta-extract-global-badguy))
                          ;;  `(:by 
                          (t `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                               :do-not nil))))
                   (& (cond ((member-atoms '<curr-prefix>-ev-meta-extract-global-badguy term)
                             '(:by <curr-prefix>-ev-meta-extract-global-badguy))
                            ((member-atoms '<curr-prefix>-ev-falsify term)
                             `(:clause-processor (beta-reduce-by-hint-cp clause '<curr-prefix>-ev-falsify state)
                               :do-not nil))
                            (t '(:do-not nil))))))))
     :atom-alist `((<thmname> . ,thmname))
     :str-alist `(("<THMNAME>" ,(symbol-name thmname) . ,thmname)
                  ("<PREFIX>" ,(symbol-name orig-prefix) . ,orig-prefix)
                  ("<CURR-PREFIX>" ,(symbol-name curr-prefix) . ,curr-prefix)))))

(defmacro def-gl-object-eval-inst (thmname &optional (prefix 'fgl))
  `(make-event
    (def-gl-object-eval-inst-fn ',thmname ',prefix (w state))))




(defun gl-primitive-fncall-entries (table)
  (Declare (Xargs :mode :program))
  (if (atom table)
      `((otherwise (mv nil nil interp-st)))
    (b* ((fn (caar table)))
      (cons (acl2::template-subst
             '(<fn> (gl-<fn>-primitive args interp-st state))
             :atom-alist `((<fn> . ,fn))
             :str-alist `(("<FN>" . ,(symbol-name fn)))
             :pkg-sym 'fgl)
            (gl-primitive-fncall-entries (cdr table))))))

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

;; BROKEN by design for now -- using a new evaluator for primitives is going to
;; require adding a macro to define a new analogue of all the -concretize
;; functions, like we have now for object evaluators.
(defun instantiate-gl-primitive-correctness-thms-fn (table)
  ;; table maps <fn> to <eval-prefix>
  (declare (xargs :mode :program))
  (if (atom table)
      nil
    (b* (((cons fn prefix) (car table)))
      (cons (acl2::template-subst
             '(progn (def-gl-object-eval-inst get-bvar->term-eval-of-<fn>-primitive <prefix>)
                     (def-gl-object-eval-inst get-bvar->term-eval-of-<fn>-primitive <prefix>)
                     (def-gl-object-eval-inst eval-of-<fn>-primitive <prefix>))
             :str-alist `(("<FN>" . ,(symbol-name fn)))
             :atom-alist `((<prefix> . ,prefix)))
            (instantiate-gl-primitive-correctness-thms-fn (cdr table))))))

(defun install-gl-primitives-fn (prefix state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       
       (eval-prefix (cdr (assoc ':last (table-alist 'fgl-last-evaluator wrld))))
       (name-formula-checks (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name prefix) "-FORMULA-CHECKS")
                             prefix))
       (formula-checks-table (table-alist 'gl-formula-checks wrld))
       (all-formulas (gl-primitive-formula-checks
                      (set::mergesort (append-alist-vals formula-checks-table))
                      state))
       (formula-check-thms (formula-check-thms name-formula-checks formula-checks-table))
       )
    (acl2::template-subst
     '(progn
        ;; (def-gl-object-eval <prefix> nil :union-previous t)
        (define <prefix>-formula-checks (state)
          :ignore-ok t
          :irrelevant-formals-ok t
          (and . <all-formulas>)
          ///
          . <formula-check-thms>)

        ;; (make-event
        ;;  (cons 'progn
        ;;        (instantiate-gl-primitive-correctness-thms-fn
        ;;         (table-alist 'gl-primitives (w state)))))

        (define <prefix>-primitive-fncall ((fn pseudo-fnsym-p)
                                           (args gl-objectlist-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
          :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
          :returns (mv successp ans new-interp-st)
          (case (pseudo-fnsym-fix fn)
            . <entries>) ;;,(gl-primitive-fncall-entries (table-alist 'gl-primitives wrld)))
          ///
          <thms> ;; ,@*gl-primitive-thms*
          (defret major-stack-concretize-of-<fn>
            (implies (interp-st-bfrs-ok interp-st)
                     (equal (<eval-prefix>-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))
                            (<eval-prefix>-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))))

          (defret get-bvar->term-eval-of-<fn>
            (b* ((bvar-db (interp-st->bvar-db interp-st)))
              (implies (and (interp-st-bfrs-ok interp-st)
                            (<= (base-bvar$a bvar-db) (nfix n))
                            (< (nfix n) (next-bvar$a bvar-db)))
                       (iff (<eval-prefix>-object-eval (get-bvar->term$a n (interp-st->bvar-db new-interp-st))
                                             env
                                             (interp-st->logicman new-interp-st))
                            (<eval-prefix>-object-eval (get-bvar->term$a n bvar-db)
                                                  env
                                                  (interp-st->logicman interp-st))))))
          (defret eval-of-<fn>
            (implies (and successp
                          (<eval-prefix>-ev-meta-extract-global-facts :state st)
                          ;; (,name-formula-checks st)
                          (<prefix>-formula-checks st)
                          (equal (w st) (w state))
                          (interp-st-bfrs-ok interp-st)
                          (interp-st-bfr-listp (gl-objectlist-bfrlist args)))
                     (equal (<eval-prefix>-object-eval ans env (interp-st->logicman new-interp-st))
                            (<eval-prefix>-ev (cons (pseudo-fnsym-fix fn)
                                               (kwote-lst (<eval-prefix>-objectlist-eval args env (interp-st->logicman interp-st))))
                                         nil))))
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
          (gl-primitive-fncall-stub <prefix>-primitive-fncall)
          (gl-primitive-formula-checks-stub <prefix>-formula-checks)
          :hints(("Goal"
                  :in-theory (enable <eval-prefix>-ev-of-fncall-args
                                     <eval-prefix>-ev-of-nonsymbol-atom
                                     <eval-prefix>-ev-of-bad-fncall)
                  :do-not '(preprocess simplify)
                  :clause-processor dumb-clausify-cp)
                 (let ((term (car (last clause))))
                   (case-match term
                     (('equal (fn . &) . &)
                      (cond ((member fn '(<prefix>-ev
                                          <prefix>-ev-list))
                             '(:do-not nil))
                            ;; ((member fn '(<prefix>-ev-falsify
                            ;;               <prefix>-meta-extract-global-badguy))
                            ;;  `(:by 
                            (t `(:clause-processor (beta-reduce-by-hint-cp clause ',fn state)
                                 :do-not nil))))
                     (& (cond ((member-atoms '<prefix>-primitive-fncall term)
                               '(:do-not nil))
                              ((member-atoms '<prefix>-ev-meta-extract-global-badguy term)
                               '(:by <prefix>-ev-meta-extract-global-badguy))
                              ((member-atoms '<prefix>-ev-falsify term)
                               `(:clause-processor (beta-reduce-by-hint-cp clause '<prefix>-ev-falsify state)
                                 :do-not nil))
                              (t '(:do-not nil)))))))
          ))
     :str-alist `(("<PREFIX>" ,(symbol-name prefix) . ,prefix)
                  ("<EVAL-PREFIX>" ,(symbol-name eval-prefix) . ,eval-prefix))
     :atom-alist `(;; (<all-formulas> . ,all-formulas)
                   ;; (<formula-check-thms> . ,formula-check-thms)
                   (<entries> . ,(gl-primitive-fncall-entries (table-alist 'gl-primitives wrld)))
                   (<all-formulas> . ,all-formulas)
                   (<formula-check-thms> . ,formula-check-thms))
     :splice-alist `((<thms> . ,*gl-primitive-thms*)))
    
    ))

(defmacro install-gl-primitives (name)
  `(make-event
    (install-gl-primitives-fn ',name state)))
