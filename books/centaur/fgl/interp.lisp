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


(define interp-st-bindings (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-bindings stack)
             bindings))

(define interp-st-stack-len (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (len)
             (stack-len stack)
             len))

(define interp-st-pop-frame (interp-st)
  :enabled t
  :inline t
  :guard (< 1 (interp-st-stack-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-frame stack)
             interp-st))

(define interp-st-push-scratch ((x gl-object-p)
                                interp-st)
  :enabled t
  :inline t
  :guard (< 1 (interp-st-stack-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-push-scratch x stack)
             interp-st))

(define interp-st-scratch-len (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (len)
             (stack-scratchlen stack)
             len))

(define interp-st-pop-scratch ((n natp)
                                interp-st)
  :enabled t
  :inline t
  :guard (<= n (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-scratch n stack)
             interp-st))

(define interp-st-peek-scratch ((n natp)
                                interp-st)
  :enabled t
  :inline t
  :guard (<= n (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (args)
             (stack-peek-scratch n stack)
             args))

(define interp-st-add-bindings ((x gl-object-alist-p)
                                interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-bindings x stack)
             interp-st))

(define interp-st-set-bindings ((x gl-object-alist-p)
                                interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-bindings x stack)
             interp-st))

(define interp-st-push-frame ((bindings gl-object-alist-p)
                              interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((stack (stack-push-frame stack)))
               (stack-set-bindings bindings stack))
             interp-st))

(define interp-st-dup-frame (interp-st)
  :enabled t
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((bindings (stack-bindings stack))
                  (stack (stack-push-frame stack)))
               (stack-set-bindings bindings stack))
             interp-st))




(define interp-st-decrement-reclimit (interp-st)
  :guard (posp (interp-st->reclimit interp-st))
  (update-interp-st->reclimit (1- (interp-st->reclimit interp-st)) interp-st))

(define interp-st-increment-reclimit (interp-st)
  (update-interp-st->reclimit (1+ (lnfix (interp-st->reclimit interp-st))) interp-st))

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
    (b* ((current-equiv-contexts (interp-st->equiv-contexts interp-st))
         (interp-st (interp-st-update-equiv-contexts '(iff) interp-st))
         ((gl-interp-recursive-call err xobj interp-st state)
          (gl-interp-term-equivs x interp-st state))
         (interp-st (interp-st-update-equiv-contexts current-equiv-contexts interp-st))
         ((when err)
          (mv err nil interp-st state)))
      (simplify-if-test xobj interp-st state)))

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
        :var (b* ((bindings (interp-st->bindings interp-st)))
               (glcp-value (cdr (hons-assoc-equal x.name bindings))))
        :lambda
        (b* (((mv x-bindings body) (lambda-nest-to-bindinglist x))
             (interp-st (interp-st-dup-frame interp-st))
             (contexts (interp-st->equiv-contexts interp-st))
             (interp-st (update-interp-st->contexts nil interp-st))
             ((gl-interp-recursive-call err interp-st state)
              ;; replaces the top of stack with the bindings
              (gl-interp-bindinglist bindings interp-st state))
             (interp-st (upate-interp-st->equiv-contexts contexts interp-st))
             ((when err)
              (b* ((interp-st (interp-st-pop-frame interp-st)))
                (mv err nil interp-st state)))
             ((mv err val interp-st state)
              (gl-interp-term-equivs body interp-st state))
             (interp-st (interp-st-pop-frame interp-st)))
          (mv err val interp-st state))
        :fncall 
        (b* (((when (and** (eq x.fn 'if) (eql (len x.args) 3)))
              (gl-interp-if (first x.args)
                            (second x.args)
                            (third x.args)
                            interp-st state))
             ((when (and** (eq x.fn 'return-last) (eql (len x.args) 3)))
              (gl-interp-return-last (first x.args)
                                     (second x.args)
                                     (third x.args)
                                     interp-st state))
             ((gl-interp-recursive-call err interp-st state)
              (gl-interp-arglist x.args interp-st state))
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
         (interp-st (interp-st-add-bindings (pairlis$ x1.formals args) interp-st)))
      (gl-interp-bindinglist (cdr bindings) interp-st state)))
         
  (define gl-interp-fncall ((fn pseudo-fnsym-p)
                            (arity natp)
                            interp-st
                            state)
    :measure (list (nfix (interp-st->reclimit interp-st))
                   0 0 1)
    (b* (((gl-function-mode fn-mode)
          (gl-function-mode-fix!
           (cdr (hons-assoc-equal fn (table-alist 'gl-fn-modes (w state))))))
         (args (interp-st-peek-scratch arity interp-st))
         (interp-st (interp-st-pop-scratch arity interp-st))
         ((mv successp ans)
          (fncall-try-concrete-eval fn args fn-mode.dont-concrete-exec state))
         ((when successp)
          (mv nil ans interp-st state))
         ((gl-interp-recursive-call err successp ans interp-st state)
          (gl-rewrite-fncall fn args fn-mode.dont-rewrite interp-st state))
         ((when err)
          (mv err nil interp-st state))
         ((when successp)
          (mv nil ans interp-st state))
         ((mv successp ans interp-st state)
          (gl-primitive-fncall fn args fn-mode.dont-primitive-exec interp-st state))
         ((when successp)
          (mv nil ans interp-st state))
         ((mv err successp ans interp-st state)
          (gl-interp-fn-definition fn args fn-mode.dont-expand-def interp-st state))
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
    :measure (list (nfix (interp-st->reclimit interp-st)) 0 0 0)
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
         ((when (zp (interp-st->reclimit interp-st)))
          (mv (gl-msg "The recursion limit ran out.")
              nil nil interp-st state))
         (interp-st (interp-st-push-frame interp-st))
         (interp-st (interp-st-set-bindings (pairlis$ formals args) interp-st))
         (interp-st (interp-st-decrement-reclimit interp-st))
         ((mv err ans interp-st state)
          (gl-interp-term-equivs body interp-st state))
         (interp-st (interp-st-pop-frame interp-st))
         (interp-st (interp-st-increment-reclimit interp-st)))
      (mv err ans interp-st state)))


  (define gl-rewrite-fncall ((fn pseudo-fnsym-p)
                             (args gl-objectlist-p)
                             (dont)
                             interp-st
                             state)
    :measure (list (nfix (interp-st->reclimit interp-st)) 0 0 0)
    :returns (mv err successp
                 (ans gl-object-p)
                 new-interp-st
                 new-state)
    (b* (((when dont)
          (mv nil nil nil interp-st state))
         (backchain-limit (interp-st->backchain-limit interp-st))
         ((when (eql 0 backchain-limit))
          (mv nil nil nil interp-st state))
         (interp-st (update-interp-st->backchain-limit (1- backchain-limit) interp-st))
         (rules (fn-rewrite-rules fn (glcp-config->rewrite-rule-table
                                      (interp-st->config interp-st))
                                  (w state)))
         ;; Pushes a stack frame if successful!
         ((gl-interp-recursive-call err successp rhs interp-st state)
          (gl-rewrite-fncall-rules rules fn args interp-st state))



         

              ((when (zp (interp-st->reclimit interp-st)))
          (glcp-interp-error (gl-msg "The recursion limit ran out.")))
         (interp-st (interp-st-decrement-reclimit interp-st))
         
         
  gl-interp-if
  gl-interp-return-last
  gl-rewrite-fncall)
             
        
         
    
