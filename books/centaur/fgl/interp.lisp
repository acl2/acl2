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

(include-book "interp-st")
(include-book "bvar-db-equivs")
(include-book "bfr-arithmetic")
(include-book "glcp-unify-defs")
(include-book "centaur/meta/bindinglist" :dir :system)
(include-book "syntax-bind")
;; (define glcp-unify-alist-bfrlist ((x glcp-unify-alist-p))
;;   :measure (len (glcp-unify-alist-fix x))
;;   (b* ((x (glcp-unify-alist-fix x))
;;        ((when (atom x)) nil)
;;        ((cons key val) (car x)))
;;     (append (gl-object-bfrlist val)
;;             (glcp-unify-alist-bfrlist (cdr x))))
;;   ///
;;   (defthm member-bfrlist-of-glcp-unify-alist-lookup
;;     (implies (and (not (member bfr (glcp-unify-alist-bfrlist x)))
;;                   (acl2::pseudo-var-p v))
;;              (not (member bfr (cdr (hons-assoc-equal v x))))))
  
;;   (defthm member-glcp-unify-alist-bfrlist-of-cons
;;     (implies (and (not (member bfr (glcp-unify-alist-bfrlist x)))
;;                   (not (member bfr (gl-object-bfrlist val))))
;;              (not (member bfr (glcp-unify-alist-bfrlist (cons (cons key val) x)))))))

;; Trace this!
(define glcp-interp-error-message ((str stringp)
                                   (arglist))
  :returns (error-message (or (consp error-message)
                              (stringp error-message))
                          :rule-classes :type-prescription)
  (if arglist
      (cons (str-fix str) arglist)
    (str-fix str)))

(defmacro gl-msg (str &rest args)
  `(glcp-interp-error-message ,str ,(make-fmt-bindings acl2::*base-10-chars* args)))



;; (define glcp-interp-error (msg &key (interp-st 'interp-st)
;;                                (state 'state))
;;   :returns (mv errmsg
;;                result
;;                new-interp-st
;;                new-state)
;;   (mv msg nil interp-st state))

(defmacro glcp-value (obj)
  `(mv nil ,obj interp-st state))


;; should we look for equivalence assumptions for this object?
(define glcp-term-obj-p ((x gl-object-p))
  (declare (xargs :guard t))
  (gl-object-case x
    :g-ite t
    :g-var t
    :g-apply t
    :otherwise nil))


(fty::defbitstruct gl-function-mode
  ((dont-concrete-exec booleanp)
   (dont-expand-def booleanp)
   (dont-rewrite booleanp)
   (dont-primitive-exec booleanp)))

(define gl-function-mode-fix! (x)
  :guard-hints(("Goal" :in-theory (enable gl-function-mode-fix)))
  :enabled t
  (mbe :logic (gl-function-mode-fix x)
       :exec (loghead 4 (ifix x))))

(define g-concretelist-p ((x gl-objectlist-p))
  (if (atom x)
      t
    (and (gl-object-case (car x) :g-concrete)
         (g-concretelist-p (Cdr x)))))

(define g-concretelist-vals ((x gl-objectlist-p))
  :guard (g-concretelist-p x)
  :guard-hints (("goal" :in-theory (enable g-concretelist-p)))
  (if (atom x)
      nil
    (cons (g-concrete->val (car x))
          (g-concretelist-vals (cdr x)))))

(define fncall-try-concrete-eval ((fn pseudo-fn-p)
                                  (args gl-objectlist-p)
                                  (dont-concrete-exec)
                                  state)
  :returns (mv ok ans)
  (b* (((gl-function-mode mode))
       ((when (or dont-concrete-exec
                  (not (g-concretelist-p args))))
        (mv nil nil))
       ((mv err ans)
        (magic-ev-fncall fn (g-concretelist-vals args) state t nil)))
    (mv (not err) ans)))


(def-b*-binder gl-interp-recursive-call
  :body
  `(b* (((mv . ,args)
         (mbe :logic
              (b* ((reclimit (interp-st->reclimit interp-st))
                   ((mv . ,args) . ,forms)
                   (interp-st (update-interp-st->reclimit reclimit interp-st)))
                (mv . ,args))
              :exec (progn$ . ,forms))))
     ,rest-expr))


(define gl-interp-time$-arg ((arg gl-object-p) (x pseudo-termp))
  (b* ((arg (gl-object-case arg :g-concrete (and (true-listp arg.val) arg.val) :otherwise nil))
       (term-descrip (pseudo-term-case x :fncall x.fn :otherwise x)))
    (if arg
        (b* ((msg (nth 3 arg)))
          (if msg
              arg
            (append (take 3 arg)
                    (list "Gl-interp ~x0: ~st real, ~sc cpu, ~sa bytes~%"
                          (list term-descrip)))))
      (list 0 nil nil "Gl-interp ~x0: ~st real, ~sc cpu, ~sa bytes~%"
            (list term-descrip)))))

(local (defthm assoc-when-key
         (implies k
                  (equal (assoc k a)
                         (hons-assoc-equal k a)))))

(define match-syntax-bind-synp ((synp pseudo-termp))
  :returns (mv ok (form pseudo-termp) untrans)
  (b* (((mv ok alist) (cmr::pseudo-term-unify '(synp nil untrans-form trans-form)
                                              synp nil))
       ((unless ok) (mv nil nil nil))
       (untrans-form (cdr (assoc 'untrans-form alist)))
       (trans-form   (cdr (assoc 'trans-form alist)))
       ((unless (and (pseudo-term-case untrans-form :quote)
                     (pseudo-term-case trans-form :quote)))
        (mv nil nil nil))
       (val (acl2::pseudo-term-quote->val trans-form)))
    (if (pseudo-termp val)
        (mv t val untrans-form)
      (mv nil nil nil))))


         

(define gl-interp-syntax-bind ((synp-arg pseudo-termp)
                               (x pseudo-termp)
                               interp-st
                               state)
  :returns (mv err
               (ans gl-object-p)
               new-interp-st
               new-state)
  :prepwork ((local (defthm symbol-alistp-when-gl-object-alist-p
                      (implies (gl-object-alist-p x)
                               (symbol-alistp x))
                      :hints(("Goal" :in-theory (enable gl-object-alist-p))))))
  (b* (((mv synp-ok synp-term untrans) (match-syntax-bind-synp synp-arg))
       ((unless (and synp-ok (pseudo-term-case x :var)))
        ;; We could go ahead and simulate x anyway but this does seem like an error.
        (mv (gl-msg "Bad syntax-bind form: args ~x0, ~x1." synp-arg x)
            nil interp-st state))
       (varname (acl2::pseudo-term-var->name x))
       (bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st)))
       ((when (assoc-eq varname bindings))
        (mv (gl-msg "Syntax-bind error: ~x0 was supposed to be bound in a ~
                       syntax-bind form but was already bound" varname)
            nil interp-st state))
       ((mv ok val) (acl2::magic-ev synp-term bindings state t t))
       ((unless ok)
        (mv (gl-msg "Syntax-bind error: ~x0 failed to evaluate -- translated: ~x1" untrans synp-term)
            nil interp-st state))
       (val-obj (g-concrete val))
       (interp-st (interp-st-add-binding varname val-obj interp-st)))
    (mv nil val-obj interp-st state)))


(define gl-interp-or-test-equiv-contexts ((contexts equiv-contextsp))
  :returns (new-contexts equiv-contextsp)
  (and (equal contexts '(iff)) '(iff)))

(defines gl-interp
  (define gl-interp-test ((x pseudo-termp)
                          interp-st
                          state)
    ;; Translate a term to a GL object under the given alist substitution, preserving IFF.
    :measure (list (nfix (interp-st->reclimit interp-st))
                   12 (pseudo-term-binding-count x) 0)
    :well-founded-relation acl2::nat-list-<
    :guard (bfr-listp (glcp-unify-alist-bfrlist alist) (interp-st->bfrstate interp-st))
    :returns (mv err
                 (xobj gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((interp-st-bind
           (equiv-contexts '(iff)))
          ((gl-interp-recursive-call err xobj interp-st state)
           (gl-interp-term-equivs x interp-st state)))
         ((when err)
          (mv err nil interp-st state)))
      (gl-interp-simplify-if-test xobj interp-st state)))

  (define gl-interp-term-equivs ((x pseudo-termp)
                                 interp-st
                                 state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 2020 (pseudo-term-binding-count x) 40)
    :returns (mv err
                 (xobj gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((mv err xobj interp-st state)
          (gl-interp-term x interp-st state))
         ((when err) (mv err nil interp-st state))
         ((unless (glcp-term-obj-p xobj))
          (glcp-value xobj))
         (contexts (interp-st->equiv-contexts interp-st)))
      (stobj-let ((pathcond (interp-st->pathcond interp-st))
                  (logicman (interp-st->logicman interp-st))
                  (bvar-db (interp-st->bvar-db interp-st)))
                 (replacedp val pathcond)
                 (try-equivalences-loop
                  xobj contexts 100 ;; bozo, configure reclimit for try-equivalences-loop?
                  pathcond bvar-db logicman state)
                 (glcp-value val))))

  (define gl-interp-term ((x pseudo-termp)
                          interp-st
                          state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020 (pseudo-term-binding-count x) 20)
    :returns (mv err
                 (xobj gl-object-p)
                 new-interp-st
                 new-state)
    (b* ((interp-st (interp-st-fix interp-st)))
      (pseudo-term-case x
        :const (glcp-value (g-concrete x.val))
        :var (b* ((minor-look (assoc-eq x.name (interp-st-minor-bindings interp-st)))
                  ((when minor-look)
                   (glcp-value (cdr minor-look))))
               (glcp-value (cdr (assoc-eq x.name (interp-st-bindings interp-st)))))
        :lambda
        (b* (((mv x-bindings body) (lambda-nest-to-bindinglist x))
             (interp-st (interp-st-push-minor-frame interp-st))
             (interp-st (interp-st-set-minor-debug x interp-st))
             ((interp-st-bind
               (equiv-contexts nil))
              ((gl-interp-recursive-call err interp-st state)
               ;; replaces the top of stack with the bindings
               (gl-interp-bindinglist bindings interp-st state)))

             ((when err)
              (b* ((interp-st (interp-st-pop-minor-frame interp-st)))
                (mv err nil interp-st state)))
             ((mv err val interp-st state)
              (gl-interp-term-equivs body interp-st state))
             (interp-st (interp-st-pop-minor-frame interp-st)))
          (mv err val interp-st state))
        :fncall 
        (b* (((when (and** (eq x.fn 'if) (eql (len x.args) 3)))
              (gl-interp-if/or (first x.args)
                               (second x.args)
                               (third x.args)
                               interp-st state))
             ((when (and** (eq x.fn 'return-last) (eql (len x.args) 3)))
              (gl-interp-return-last (first x.args)
                                     (second x.args)
                                     (third x.args)
                                     interp-st state))
             ((interp-st-bind
               (equiv-contexts nil))
              ((gl-interp-recursive-call err interp-st state)
               ;; pushes the results from the args onto the scratch frame
               (gl-interp-arglist x.args interp-st state)))

             ((when err)
              (mv err nil interp-st state)))
          (gl-interp-fncall x.fn (len x.args) interp-st state)))))

  (define gl-interp-arglist ((args pseudo-term-listp)
                             interp-st
                             state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020 (pseudo-term-list-binding-count args) 20)
    :returns (mv err
                 new-interp-st
                 new-state)
    (b* (((when (atom args)) (mv nil interp-st state))
         ((gl-interp-recursive-call err arg1 interp-st state)
          (gl-interp-term-equivs (car args) interp-st state))
         ((when err) (mv err interp-st state))
         (interp-st (interp-st-push-scratch arg1 interp-st)))
      (gl-interp-arglist (cdr args) interp-st state)))

  (define gl-interp-bindinglist ((bindings bindinglist-p)
                                 interp-st
                                 state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020
                   (bindinglist-count bindings)
                   20)
    :returns (mv err
                 new-interp-st
                 state)
    (b* (((when (atom bindings)) (mv nil interp-st state))
         ((binding x1) (car x))
         ((gl-interp-recursive-call err interp-st state)
          (gl-interp-arglist x1.args interp-st state))
         ((when err) (mv err interp-st state))
         (argslen (len x1.args))
         (args (interp-st-peek-scratch argslen interp-st))
         (interp-st (interp-st-pop-scratch argslen interp-st))
         (interp-st (interp-st-add-minor-bindings (pairlis$ x1.formals args) interp-st)))
      (gl-interp-bindinglist (cdr bindings) interp-st state)))
         
  (define gl-interp-fncall ((fn pseudo-fnsym-p)
                            (arity natp)
                            interp-st
                            state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   0 0 1)
    :returns (mv err
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((gl-function-mode fn-mode)
          (gl-function-mode-fix!
           (cdr (hons-assoc-equal fn (table-alist 'gl-fn-modes (w state))))))
         (args (interp-st-peek-scratch arity interp-st))
         (interp-st (interp-st-pop-scratch arity interp-st))
         ((mv successp ans)
          (fncall-try-concrete-eval fn args fn-mode.dont-concrete-exec state))
         ((when successp)
          (mv nil ans interp-st state))
         (reclimit (interp-st->reclimit interp-st))
         ((when (zp reclimit))
          (mv (gl-msg "The recursion limit ran out.") nil interp-st state))
         ((interp-st-bind
           (reclimit (1- reclimit) reclimit))
          ((gl-interp-recursive-call err successp ans interp-st state)
           (gl-rewrite-fncall fn args fn-mode.dont-rewrite interp-st state)))
         ((when err)
          (mv err nil interp-st state))
         ((when successp)
          (mv nil ans interp-st state))
         ((mv successp ans interp-st state)
          (gl-primitive-fncall fn args fn-mode.dont-primitive-exec interp-st state))
         ((when successp)
          (mv nil ans interp-st state))
         ((interp-st-bind
           (reclimit (1- reclimit) reclimit))
          ((mv err successp ans interp-st state)
           (gl-interp-fn-definition fn args fn-mode.dont-expand-def interp-st state)))
         ((when err)
          (mv err nil interp-st state))
         ((when successp)
          (mv nil ans interp-st state)))
      (mv nil (g-apply fn args) interp-st state)))

  (define gl-interp-fn-definition ((fn pseudo-fnsym-p)
                                   (args gl-objectlist-p)
                                   (dont)
                                   interp-st
                                   state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
    :returns (mv err successp
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((when dont)
          (mv nil nil nil interp-st state))
         ((mv ok body formals)
          (acl2::fn-get-def fn state))
         ((unless ok)
          (mv nil nil nil interp-st state))
         ((unless (eql (len formals) arity))
          (mv (gl-msg "Error interpreting a call of ~x0: it was given ~x1 arguments but has ~x2 formals."
                   fn arity (len formals))
              nil nil interp-st state))
         (interp-st (interp-st-push-frame (pairlis$ formals args) interp-st))
         (interp-st (interp-st-set-debug fn interp-st))
         ((mv err ans interp-st state)
          (gl-interp-term-equivs body interp-st state))
         (interp-st (interp-st-pop-frame interp-st)))
      (mv err ans interp-st state)))


  (define gl-rewrite-fncall ((fn pseudo-fnsym-p)
                             (args gl-objectlist-p)
                             (dont)
                             interp-st
                             state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
    :returns (mv err successp
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((when dont)
          (mv nil nil nil interp-st state))
         (rules (fn-rewrite-rules fn (glcp-config->rewrite-rule-table
                                      (interp-st->config interp-st))
                                  (w state)))
         ((unless rules)
          (mv nil nil nil interp-st state))
         (reclimit (interp-st->reclimit interp-st))
         ((when (zp reclimit))
          (mv (gl-msg "The recursion limit ran out.")
              nil nil interp-st state)))
      (gl-rewrite-try-rules rules fn args interp-st state)))

  (define gl-rewrite-try-rules ((rules pseudo-rewrite-rule-listp)
                                (fn pseudo-fnsym-p)
                                (args gl-objectlist-p)
                                interp-st
                                state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 10000 (len rules) 0)
    :returns (mv err successp
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((when (atom rules))
          (mv nil nil nil interp-st state))
         ((gl-interp-recursive-call err successp ans interp-st state)
          (gl-rewrite-try-rule (car rules) fn args interp-st state))
         ((when (or err successp))
          (mv err successp ans interp-st state)))
      (gl-rewrite-try-rules (cdr rules) fn args interp-st state)))

  (define gl-rewrite-try-rule ((rule pseudo-rewrite-rule-p)
                               (fn pseudo-fnsym-p)
                               (args gl-objectlist-p)
                               interp-st
                               state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 0)
    :returns (mv err successp
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((acl2::rewrite-rule rule))
         ((unless (and** (mbt (and* (symbolp rule.equiv)
                                    (not (eq rule.equiv 'quote))
                                    ;; (ensure-equiv-relationp rule.equiv (w state))
                                    (not (eq rule.subclass 'acl2::meta))
                                    (pseudo-termp rule.lhs)))
                         (pseudo-term-case rule.lhs :fncall (eq rule.lhs.fn (pseudo-fnsym-fix fn)))))
          (mv (gl-msg "Malformed rewrite rule: ~x0~%" rule)
              nil nil interp-st state))
         ((unless (or (eq rule.equiv 'equal)
                      ;; bozo check refinements
                      (member rule.equiv (interp-st->equiv-contexts interp-st))))
          (mv nil nil nil interp-st state))
         (rule.lhs.args (pseudo-term-call->args rule.lhs))
         ((mv unify-ok bindings) (glcp-unify-term/gobj-list rule.lhs.args args nil))
         ((unless unify-ok) (mv nil nil nil interp-st state))
         ((unless (mbt (pseudo-term-listp rule.hyps)))
          (mv (gl-msg "Malformed rewrite rule: ~x0~%" rule)
              nil nil interp-st state))
         (backchain-limit (interp-st->backchain-limit interp-st))
         ((when (and* rule.hyps (eql 0 backchain-limit)))
          (mv nil nil nil interp-st state))
         (flags (interp-st->flags interp-st))
         (hyps-flags  (!interp-st->intro-bvars
                       t
                       (!interp-flags->intro-bvars
                        nil
                        (!interp-flags->simplify-logic nil flags))))
         (interp-st (interp-st-push-frame bindings interp-st))
         (interp-st (interp-st-set-debug rule interp-st))
         ((interp-st-bind
           (flags hyps-flags flags)
           (contexts '(iff))
           (backchain-limit (1- backchain-limit) backchain-limit))
          ((gl-interp-recursive-call err successp interp-st state)
           (gl-rewrite-relieve-hyps rule.hyps interp-st state)))

         ((unless successp)
          (b* ((interp-st (interp-st-pop-frame interp-st)))
            (mv err nil nil interp-st state)))

         (concl-flags (!interp-st->intro-bvars t flags))
         ((interp-st-bind
           (flags concl-flags flags))
          ((mv err val interp-st state)
           (gl-interp-term-equivs rule.rhs interp-st state)))

         (interp-st (interp-st-pop-frame interp-st)))

      (mv err (not err) val interp-st state)))
          
    
  (define gl-interp-time$ ((timing-arg pseudo-termp)
                           (x pseudo-termp)
                           interp-st
                           state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                   (+ (pseudo-term-binding-count first-arg)
                      (pseudo-term-binding-count last-arg))
                   30)
    :returns (mv err
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((interp-st-bind
           (equiv-contexts nil))
          ((gl-interp-recursive-call err time$-arg interp-st state)
           (gl-interp-term-equivs timing-arg interp-st state)))
         ((when err)
          (mv err nil interp-st state))
         (time$-arg (gl-interp-time$-arg time$-arg x)))
      (time$1 time$-arg
              (gl-interp-term-equivs x interp-st state))))
         
  (define gl-interp-return-last ((return-last-fnname pseudo-termp)
                                 (first-arg pseudo-termp)
                                 (last-arg pseudo-termp)
                                 interp-st state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                   (+ (pseudo-term-binding-count first-arg)
                      (pseudo-term-binding-count last-arg))
                   40)
    :returns (mv err
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((when (equal return-last-fnname ''time$1-raw))
          (gl-interp-time$ first-arg last-arg interp-st state))
         ((when (equal return-last-fnname ''(syntax-bind)))
          (gl-interp-syntax-bind first-arg last-arg interp-st state)))
      ;; Otherwise just evaluate the last-arg.
      (gl-interp-term-equivs last-arg interp-st state)))
                
               

  (define gl-interp-if/or ((test pseudo-termp)
                           (then pseudo-termp)
                           (else pseudo-termp)
                           interp-st
                           state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020
                   (+ (pseudo-term-binding-count test)
                      (pseudo-term-binding-count then)
                      (pseudo-term-binding-count else))
                   60)
    :returns (mv err
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (if (hons-equal test then)
        (gl-interp-or test else interp-st state)
      (gl-interp-if test then else interp-st state)))

  
  (define gl-interp-if ((test pseudo-termp)
                        (then pseudo-termp)
                        (else pseudo-termp)
                        interp-st
                        state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020
                   (+ (pseudo-term-binding-count test)
                      (pseudo-term-binding-count then)
                      (pseudo-term-binding-count else))
                   40)
    :returns (mv err
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    ;; Tricky because we have to keep the test/thenval on the stack while we
    ;; run the then/else branches, because we might simplify the logicman while
    ;; running them.
    (b* (((gl-interp-recursive-call err testbfr interp-st state)
          (gl-interp-test test interp-st state))
         ((when err) (mv err nil interp-st state))
         (interp-st (interp-st-push-bool-scratch testbfr interp-st))
         ((gl-interp-recursive-call err then-unreachable thenval interp-st state)
         ;; pushes val onto scratch if not unreachable
          (gl-maybe-interp testbfr then interp-st state))
         ((when err)
          (b* ((interp-st (interp-st-pop-bool-scratch 1 interp-st)))
            (mv err nil interp-st state)))
         (interp-st (interp-st-push-scratch thenval interp-st))
         ;; note: testbool may have changed if we simplified the logicman
         (testbfr (first (interp-st-bool-scratch interp-st)))
         ((gl-interp-recursive-call err else-unreachable elseval interp-st state)
          ;; pushes val onto scratch if not unreachable
          (gl-maybe-interp (interp-st-bfr-not testbfr interp-st) else interp-st state))
         ((when err)
          (b* ((interp-st (interp-st-pop-scratch 1 interp-st))
               (interp-st (interp-st-pop-bool-scratch 1 interp-st)))
            (mv err nil interp-st state)))
         (thenval (first (interp-st-scratch interp-st)))
         (testbfr (first (interp-st-bool-scratch interp-st)))
         (interp-st (interp-st-pop-scratch 1 interp-st))
         (interp-st (interp-st-pop-bool-scratch 1 interp-st))
         ((when then-unreachable)
          (if else-unreachable
              (mv :unreachable nil interp-st state)
            (mv nil elseval interp-st state)))
         ((when else-unreachable)
          (mv nil thenval interp-st state)))
      (gl-interp-merge-branches testbfr thenval elseval interp-st state)))

  (define gl-interp-or ((test pseudo-termp)
                        (else pseudo-termp)
                        interp-st
                        state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020
                   (+ (pseudo-term-binding-count test)
                      (pseudo-term-binding-count else))
                   40)
    :returns (mv err
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* ((equiv-contexts (interp-st->equiv-contexts interp-st))
         (or-test-equiv-contexts (gl-interp-or-test-equiv-contexts equiv-contexts))
         ((interp-st-let
           (equiv-contexts or-test-equiv-contexts equiv-contexts))
          ((gl-interp-recursive-call err testval interp-st state)
           (gl-interp-term-equivs test interp-st state)))
         ((when err) (mv err nil interp-st state))
         ((mv err testbfr interp-st state)
          (gl-interp-simplify-if-test testval interp-st state))
         ((when err) (mv err nil interp-st state))
         (interp-st (interp-st-push-scratch testval interp-st))
         (interp-st (interp-st-push-bool-scratch testbfr interp-st))
         ((gl-interp-recursive-call err else-unreachable elseval interp-st state)
          ;; pushes val onto scratch if not unreachable
          (gl-maybe-interp (interp-st-bfr-not testbfr interp-st) else interp-st state))
         (testval (first (interp-st-scratch interp-st)))
         (testbfr (first (interp-st-bool-scratch interp-st)))
         (interp-st (interp-st-pop-scratch 1 interp-st))
         (interp-st (interp-st-pop-bool-scratch 1 interp-st))
         ((when err)
          (mv err nil interp-st state))
         ((when else-unreachable)
          (mv nil testval interp-st state)))
      (gl-interp-merge-branches testbfr testval elseval interp-st state)))


  (define gl-maybe-interp ((test interp-st-bfr-p)
                           (x pseudo-termp)
                           interp-st
                           state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   2020
                   (pseudo-term-binding-count x)
                   40)
    :returns (mv err
                 unreachable
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((mv contra checkpoint interp-st)
          (stobj-let ((logicman (interp-st->logicman interp-st))
                      (pathcond (interp-st->pathcond interp-st))
                      (constraint-pathcond (interp-st->constraint interp-st)))
                     (contra checkpoint pathcond constraint-pathcond)
                     ;; this is a bit weak... would be better to check against
                     ;; both constraint and pathcond at once somehow
                     (b* ((bfr-mode  (logicman->mode logicman))
                          (checkpoint (pathcond-checkpoint bfr-mode pathcond))
                          ((mv constraint-implies constraint-pathcond)
                           (logicman-pathcond-implies test constraint-pathcond))
                          ((when constraint-implies)
                           (mv (eql constraint-implies 0) checkpoint pathcond constraint-pathcond))
                          ((mv contra pathcond) (logicman-pathcond-assume test pathcond))
                          ((when contra)
                           (b* ((pathcond (pathcond-rewind checkpoint bfr-mode pathcond)))
                             (mv contra nil pathcond constraint-pathcond))))
                       (mv nil checkpoint pathcond constraint-pathcond))
                     (mv contra checkpoint interp-st)))
         ((when contra)
          (mv nil t nil interp-st state))
         ((mv err ans interp-st state)
          (gl-interp-term-equivs x interp-st state))
         (interp-st (stobj-let ((logicman (interp-st->logicman interp-st))
                                (pathcond (interp-st->pathcond interp-st)))
                               (pathcond)
                               (pathcond-rewind checkpoint (logicman->bfr-mode logicman) pathcond)
                               interp-st))
         ((when (eq err :unreachable))
          (mv nil t nil interp-st state)))
      (mv err nil ans interp-st state)))

    gl-interp-merge-branches
    gl-interp-simplify-if-test)
             
        
         
    
