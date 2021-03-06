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

(include-book "bfr-arithmetic")
(include-book "bvar-db-equivs")
(include-book "unify-defs")
(include-book "centaur/meta/bindinglist" :dir :system)
(include-book "syntax-bind")
; (include-book "rewrite-tables")
(include-book "system/f-put-global" :dir :system)
(include-book "std/util/defret-mutual-generate" :dir :system)
(include-book "unify-thms")
(include-book "tools/some-events" :dir :system)
(include-book "primitives-stub")
(include-book "sat-stub")
(include-book "trace")
(include-book "fancy-ev")
(include-book "binder-rules") ;; includes regular rules too
(include-book "congruence-rules")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/meta/resolve-flag-cp" :dir :system))
(local (include-book "centaur/meta/urewrite" :dir :system))
(local (include-book "centaur/meta/let-abs" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (e/d (acl2::kwote-lst-redef)
                       (kwote-lst))))


;; NOTE: All these rules should be superfluous, but they might significantly speed up proofs.
(local (defthm interp-st-bfrs-ok-of-update-reclimit
         (implies (interp-st-bfrs-ok interp-st)
                  (interp-st-bfrs-ok (update-interp-st->reclimit reclimit interp-st)))))

(local (defthm interp-st-bfrs-ok-of-update-equiv-contexts
         (implies (interp-st-bfrs-ok interp-st)
                  (interp-st-bfrs-ok (update-interp-st->equiv-contexts equiv-contexts interp-st)))))

(local (defthm interp-st->logicman-of-update-reclimit
         (equal (interp-st->logicman (update-interp-st->reclimit reclimit interp-st))
                (interp-st->logicman interp-st))))

(local (defthm interp-st->logicman-of-update-equiv-contexts
         (equal (interp-st->logicman (update-interp-st->equiv-contexts equiv-contexts interp-st))
                (interp-st->logicman interp-st))))

(local (defthm interp-st->logicman-of-update-stack
         (equal (interp-st->logicman (update-interp-st->stack equiv-contexts interp-st))
                (interp-st->logicman interp-st))))

(local (defthm interp-st->logicman-of-update-errmsg
         (equal (interp-st->logicman (update-interp-st->errmsg equiv-contexts interp-st))
                (interp-st->logicman interp-st))))


(local (in-theory (disable w)))



(define interp-st-cancel-error ((msg symbolp) interp-st)
  :returns new-interp-st
  :hooks nil
  (if (eq (interp-st->errmsg interp-st) msg)
      (update-interp-st->errmsg nil interp-st)
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (not (equal (interp-st->errmsg interp-st) msg))
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret <fn>-something-different
    (implies (and msg2 (not (equal msg2 msg)))
             (equal (equal (interp-st->errmsg new-interp-st) msg2)
                    (equal (interp-st->errmsg interp-st) msg2)))))

;; (define fgl-interp-error (msg &key (interp-st 'interp-st)
;;                                (state 'state))
;;   :returns (mv errmsg
;;                result
;;                new-interp-st
;;                new-state)
;;   (mv msg nil interp-st state))

;; (defmacro fgl-value (obj)
;;   `(mv nil ,obj interp-st state))


;; should we look for equivalence assumptions for this object?
(define fgl-term-obj-p ((x fgl-object-p))
  (declare (xargs :guard t))
  (fgl-object-case x
    :g-ite t
    :g-var t
    :g-apply t
    :otherwise nil))

(define fgl-function-mode-fix! (x)
  :guard-hints(("Goal" :in-theory (enable fgl-function-mode-fix)))
  :enabled t
  (mbe :logic (fgl-function-mode-fix x)
       :exec (loghead 6 (ifix x))))

(define g-concretelist-p ((x fgl-objectlist-p))
  (if (atom x)
      t
    (and (fgl-object-case (car x) :g-concrete)
         (g-concretelist-p (Cdr x)))))

(define g-concretelist-vals ((x fgl-objectlist-p))
  :guard (g-concretelist-p x)
  :guard-hints (("goal" :in-theory (enable g-concretelist-p)))
  (if (atom x)
      nil
    (cons (g-concrete->val (car x))
          (g-concretelist-vals (cdr x)))))




(define fncall-try-concrete-eval ((fn pseudo-fnsym-p)
                                  (args fgl-objectlist-p)
                                  (dont-concrete-exec)
                                  state)
  :returns (mv ok (ans fgl-object-p))
  (b* (((when (or dont-concrete-exec
                  (not (g-concretelist-p args))))
        (mv nil nil))
       ((mv err ans)
        (acl2::magic-ev-fncall-logic (pseudo-fnsym-fix fn) (g-concretelist-vals args) state)))
    (mv (not err) (g-concrete ans)))
  ///
  (defret fgl-object-bfrlist-of-<fn>
    (equal (fgl-object-bfrlist ans) nil))

  (local (defthm fgl-objectlist-eval-when-concretelist-p
           (implies (g-concretelist-p x)
                    (equal (fgl-objectlist-eval x env)
                           (g-concretelist-vals x)))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval fgl-object-eval g-concretelist-p
                                             g-concretelist-vals)))))

  (defret eval-of-<fn>
    (implies (and ok
                  (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state)))
             (equal (fgl-object-eval ans env)
                    (fgl-ev (cons (pseudo-fnsym-fix fn) (kwote-lst (fgl-objectlist-eval args env)))
                            nil)))))


(define interp-st-restore-reclimit ((reclimit natp)
                                    interp-st)
  :guard (acl2::nat-equiv reclimit (interp-st->reclimit interp-st))
  :inline t
  :enabled t
  (mbe :logic (update-interp-st->reclimit (lnfix reclimit) interp-st)
       :exec interp-st))

(def-b*-binder fgl-interp-recursive-call
  :body
  `(b* ((interp-recursive-call-reclimit (lnfix (interp-st->reclimit interp-st)))
        ((mv ,@args interp-st state) . ,forms)
        (interp-st (interp-st-restore-reclimit interp-recursive-call-reclimit interp-st)))
     ,rest-expr))


(define fgl-interp-time$-arg ((arg fgl-object-p) (x pseudo-termp))
  (b* ((arg (fgl-object-case arg :g-concrete (and (true-listp arg.val) arg.val) :otherwise nil))
       (term-descrip (pseudo-term-case x :fncall x.fn :otherwise (pseudo-term-fix x))))
    (if arg
        (b* ((msg (nth 3 arg)))
          (if msg
              arg
            (append (take 3 arg)
                    (list "fgl-interp ~x0: ~st real, ~sc cpu, ~sa bytes~%"
                          (list term-descrip)))))
      (list 0 nil nil "fgl-interp ~x0: ~st real, ~sc cpu, ~sa bytes~%"
            (list term-descrip)))))

(local (defthm assoc-when-key
         (implies k
                  (equal (assoc k a)
                         (hons-assoc-equal k a)))))

(define fgl-interp-match-synp ((x pseudo-termp))
  :returns (mv (synp-type symbolp) ;; nil if bad
               (untrans-form)
               (trans-term pseudo-termp)
               (vars))
  (b* (((unless (pseudo-term-case x :fncall))
        (mv nil nil nil nil))
       ((pseudo-term-fncall x))
       ((unless (and (eq x.fn 'synp)
                     (eql (len x.args) 3)))
        (mv nil nil nil nil))
       ((list vars untrans-form trans-form) x.args)
       ((unless (and (pseudo-term-case vars :quote)
                     (pseudo-term-case untrans-form :quote)
                     (pseudo-term-case trans-form :quote)))
        (mv nil nil nil nil))
       (vars (acl2::pseudo-term-quote->val vars))
       (trans-form (acl2::pseudo-term-quote->val trans-form))
       (untrans-form (acl2::pseudo-term-quote->val untrans-form))
       ((unless (and (consp untrans-form)
                     (symbolp (car untrans-form))
                     (pseudo-termp trans-form)))
        (mv nil nil nil nil)))
    (mv (car untrans-form)
        untrans-form
        trans-form
        vars))
  ///
  (defret fgl-interp-match-synp-implies-eval
    (implies synp-type
             (equal (fgl-ev x a) t))))



(defmacro fgl-interp-value (&rest args)
  `(mv ,@args interp-st state))

(acl2::def-b*-binder fgl-interp-value
  :body `(b* (((mv ,@args interp-st state) . ,forms)) ,rest-expr))

(define fgl-interp-syntax-interp ((synp-term pseudo-termp)
                                 (untrans pseudo-termp)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
  :returns (mv (ans fgl-object-p)
               new-interp-st
               new-state)
  :prepwork ((local (defthm symbol-alistp-when-fgl-object-bindings-p
                      (implies (fgl-object-bindings-p x)
                               (symbol-alistp x))
                      :hints(("Goal" :in-theory (enable fgl-object-bindings-p))))))
  (b* (((unless (and (pseudo-term-case untrans :quote)))
        ;; We could go ahead and simulate x anyway but this does seem like an error.
        (fgl-interp-error :msg (fgl-msg "Bad syntax-interp form: args ~x0."
                                      (list (pseudo-term-fix synp-term)
                                            (pseudo-term-fix untrans)))))
       ((unless (member-eq 'unequiv (interp-st->equiv-contexts interp-st)))
        (fgl-interp-error :msg (fgl-msg "Syntax-interp called not in an unequiv context: args ~x0."
                                      (list (pseudo-term-fix synp-term)
                                            (pseudo-term-fix untrans)))))
       (bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st)))
       ((mv err val interp-st state) (fancy-ev synp-term bindings 100 interp-st state t t))
       ((when err)
        (fgl-interp-error
         :msg (fgl-msg "Syntax-interp error evaluating ~x0: ~@1"
                      (pseudo-term-quote->val untrans)
                      (if (or (consp err) (stringp err)) err "(no message)"))))
       ((unless (fgl-bfr-object-p val (interp-st-bfr-state)))
        (fgl-interp-error
         :msg (fgl-msg "Syntax-bind error: ~x0 evaluted to an illformed symbolic object, saved as debug object."
                      (pseudo-term-quote->val untrans))
         :debug-obj val)))
    (fgl-interp-value val))
  ///
  (local (defthm bfrlist-of-interp-st-add-binding
           (implies (and (not (member v (major-stack-bfrlist stack)))
                         (not (member v (fgl-object-bfrlist val))))
                    (not (member v (major-stack-bfrlist (stack$a-add-binding var val stack)))))
           :hints (("goal" :expand ((major-stack-bfrlist stack))
                    :in-theory (enable stack$a-add-binding major-frame-bfrlist
                                       major-stack-bfrlist)))))

  (local (in-theory (disable stack$a-add-binding)))
  (local (in-theory (enable bfr-listp-when-not-member-witness)))

  (local (Defthm fgl-bfr-object-p-is-fgl-object-p-and-bfr-listp
           (equal (fgl-bfr-object-p x)
                  (and (fgl-object-p x)
                       (bfr-listp (fgl-object-bfrlist x))))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (and (interp-st-bfrs-ok new-interp-st)
                  (implies (equal logicman (interp-st->logicman interp-st))
                           (lbfr-listp (fgl-object-bfrlist ans) logicman)))))

  (local (acl2::use-trivial-ancestors-check))

  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db :equiv-contexts :reclimit))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret multivalues-of-<fn>
    (equal (list . <values>) <call>))

  (defret <fn>-preserves-errmsg
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defret ans-of-<fn>
    (implies (and (not (interp-st->errmsg new-interp-st))
                  (equal contexts (interp-st->equiv-contexts interp-st)))
             (equal (fgl-ev-context-fix contexts
                                        (fgl-object-eval ans env logicman))
                    (fgl-ev-context-fix (interp-st->equiv-contexts interp-st) nil)))))


(define fgl-interp-or-test-equiv-contexts ((contexts equiv-contextsp))
  :returns (new-contexts equiv-contextsp)
  (cond ((member-eq 'unequiv (equiv-contexts-fix contexts)) '(unequiv))
        ((member-eq 'iff (equiv-contexts-fix contexts)) '(iff))))

(define fgl-interp-or-test-already-rewrittenp ((contexts equiv-contextsp))
  (or (member-eq 'unequiv (equiv-contexts-fix contexts))
      (member-eq 'iff (equiv-contexts-fix contexts))))

;; (define interp-st-checkpoint-p (chp interp-st)
;;   :enabled t
;;   (stobj-let ((pathcond (interp-st->pathcond interp-st))
;;               (logicman (interp-st->logicman interp-st)))
;;              (ok)
;;              (pathcond-checkpoint-p chp (logicman->mode logicman) pathcond)
;;              ok))

(define interp-st-pathcond-assume ((test interp-st-bfr-p)
                                   interp-st)

  :returns (mv contra
               (new-interp-st))
  :guard-hints (("goal" :in-theory (enable pathcond-rewind-ok)))
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st))
              (constraint-pathcond (interp-st->constraint interp-st)))
             (contra pathcond constraint-pathcond)
             ;; this is a bit weak... would be better to check against
             ;; both constraint and pathcond at once somehow
             (b* ((constraint-pathcond (pathcond-fix constraint-pathcond))
                  ((unless test)
                   (mv t pathcond constraint-pathcond))
                  ;; ((mv constraint-implies constraint-pathcond)
                  ;;  (logicman-pathcond-implies test constraint-pathcond))
                  ;; ((when (eql constraint-implies 0))
                  ;;  (mv t pathcond constraint-pathcond))
                  ((mv contra constraint-pathcond)
                   (logicman-pathcond-assume test constraint-pathcond))
                  ((when contra)
                   (mv t pathcond constraint-pathcond))
                  (constraint-pathcond (pathcond-rewind (logicman->mode logicman) constraint-pathcond))
                  ((mv contra pathcond) (logicman-pathcond-assume test pathcond)))
               (mv contra pathcond constraint-pathcond))
             (mv contra interp-st))
  ///
  (defret interp-st-get-of-interp-st-pathcond-assume
    (implies (and (not (equal (interp-st-field-fix key) :pathcond))
                  (not (equal (interp-st-field-fix key) :constraint)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret interp-st->constraint-of-interp-st-pathcond-assume
    (equal (interp-st->constraint new-interp-st)
           (pathcond-fix (interp-st->constraint interp-st))))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfr-p test)
                  (interp-st-bfrs-ok interp-st))
             (interp-st-bfrs-ok new-interp-st)))

  (defret pathcond-rewind-of-<fn>
    (implies (and (not contra)
                  (equal mode (logicman->mode (interp-st->logicman interp-st))))
             (equal (pathcond-rewind mode (interp-st->pathcond new-interp-st))
                    (pathcond-fix (interp-st->pathcond interp-st)))))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
          (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-pathcond-when-contra
    (implies contra
             (pathcond-equiv (interp-st->pathcond new-interp-st)
                             (interp-st->pathcond interp-st))))

  (defret logicman-pathcond-eval-of-<fn>
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (bfr-eval test env (interp-st->logicman interp-st))
                  (equal logicman (interp-st->logicman new-interp-st)))
             (logicman-pathcond-eval env (interp-st->pathcond new-interp-st) logicman)))

  (defret interp-st-pathcond-assume-not-contradictionp
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (bfr-eval test env (interp-st->logicman interp-st)))
             (not contra))))



(define interp-st-pathcond-rewind (interp-st)
  :guard (stobj-let ((pathcond (interp-st->pathcond interp-st))
                     (logicman (interp-st->logicman interp-st)))
                    (ok)
                    (pathcond-rewind-ok (lbfr-mode) pathcond)
                    ok)
  :returns new-interp-st
  :enabled t
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st)))
             (pathcond)
             (pathcond-rewind (logicman->mode logicman) pathcond)
             interp-st))

(define fgl-apply-match-not ((x fgl-object-p))
  :guard (fgl-object-case x :g-apply)
  :returns (mv ok
               (negated-arg fgl-object-p))
  (b* (((unless (mbt (fgl-object-case x :g-apply))) (mv nil nil))
       ((g-apply x))
       (fn x.fn)
       (args x.args)
       ((when (eq fn 'not))
        (cond ((eql (len args) 1)
               (mv t (fgl-object-fix (car args))))
              (t (mv nil nil))))
       ((when (eq fn 'equal))
        (b* (((unless (eql (len args) 2))
              (mv nil nil))
             ((list arg1 arg2) args)
             ((when (fgl-object-case arg1
                      :g-concrete (eq arg1.val nil)
                      :otherwise nil))
              (mv t (fgl-object-fix arg2)))
             ((when (fgl-object-case arg2
                      :g-concrete (eq arg2.val nil)
                      :otherwise nil))
              (mv t (fgl-object-fix arg1))))
          (mv nil nil))))
    (mv nil nil))
  ///


  (defret fgl-apply-match-not-correct
    (implies ok
             (iff (fgl-object-eval negated-arg env logicman)
                  (not (fgl-object-eval x env logicman))))
    :hints(("Goal" :expand ((fgl-objectlist-eval (g-apply->args x) env)
                            (fgl-objectlist-eval (cdr (g-apply->args x)) env)
                            (fgl-objectlist-eval (cddr (g-apply->args x)) env))
            :in-theory (enable fgl-apply))))

  (defret fgl-object-count-of-g-apply-match-not
    (implies ok
             (< (fgl-object-count negated-arg) (fgl-object-count x)))
    :hints(("Goal" :expand ((fgl-object-count x)
                            (fgl-objectlist-count (g-apply->args x))
                            (fgl-objectlist-count (cdr (g-apply->args x)))
                            (fgl-objectlist-count (cddr (g-apply->args x))))))
    :rule-classes :linear)

  (defret bfrlist-of-fgl-apply-match-not
    (implies (not (member v (fgl-object-bfrlist x)))
             (not (member v (fgl-object-bfrlist negated-arg))))))


(local
 (defthm pseudo-var-list-p-of-append
   (implies (and (pseudo-var-list-p x)
                 (pseudo-var-list-p y))
            (pseudo-var-list-p (append x y)))))

(local (in-theory (disable pseudo-termp acl2::magic-ev)))

(define fgl-rewrite-relieve-hyp-synp ((synp-type symbolp)
                                     (form pseudo-termp)
                                     (vars)
                                     (untrans-form)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
  :returns (mv successp
               new-interp-st
               new-state)
  :prepwork ((local (defthm alist-keys-of-fgl-object-bindings
                      (implies (fgl-object-bindings-p x)
                               (and (pseudo-var-list-p (alist-keys x))
                                    (symbol-listp (alist-keys x))))
                      :hints(("Goal" :in-theory (enable alist-keys)))))
             (local (defthm symbol-alistp-when-fgl-object-bindings-p
                      (implies (fgl-object-bindings-p x)
                               (symbol-alistp x))))

             (local (Defthm fgl-bfr-object-bindings-p-is-fgl-object-bindings-p-and-bfr-listp
                      (equal (fgl-bfr-object-bindings-p x)
                             (and (fgl-object-bindings-p x)
                                  (bfr-listp (fgl-object-bindings-bfrlist x))))
                      :hints(("Goal" :in-theory (enable fgl-bfr-object-bindings-p-implies-fgl-object-bindings-p)))))

             (local (defthm symbol-listp-when-pseudo-var-list-p
                      (implies (pseudo-var-list-p x)
                               (symbol-listp x)))))
  :hooks ((:fix :omit (synp-type)))
  (b* ((bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st)))
       (form (pseudo-term-fix form))
       ((mv err val interp-st state) (fancy-ev form bindings 100 interp-st state t t))
       ((when err)
        (fgl-interp-error
         :msg (fgl-msg "Synp error evaluating ~x0 (translated: ~x1): ~x2"
                      untrans-form form (if (or (consp err) (stringp err)) err "(no message)"))))
       ((when (eq synp-type 'syntaxp))
        (fgl-interp-value val))
       ;; bind-free...
       ((unless val)
        ;; No error -- bind-free evaluated to NIL which means just don't do the rewrite.
        (fgl-interp-value nil))
       ((unless (fgl-bfr-object-bindings-p val (interp-st-bfr-state)))
        (fgl-interp-error
         :msg (fgl-msg "Bind-free error: ~x0 evaluated to a non-FGL object alist: ~x1" untrans-form val)))
       (newly-bound-vars (alist-keys val))
       ((when (and (symbol-listp vars)
                   (not (subsetp-eq vars newly-bound-vars))))
        (fgl-interp-error
         :msg (fgl-msg "Bind-free error: ~x0 evaluated to an alist not ~
                     containing the required vars ~x1: ~x2" untrans-form val vars)))
       ;; Consider allowing already-bound variables to be bound in the new
       ;; bindings, and just omitting them from the final bindings.  Might be
       ;; convenient in case we want to bind a variable in different places for
       ;; different cases.
       ((when (intersectp-eq (alist-keys bindings) newly-bound-vars))
        (fgl-interp-error
         :msg (fgl-msg "Bind-free error: ~x0 evaluated to an alist containing already-bound vars: ~x1" untrans-form val)))
       ((unless (no-duplicatesp-eq newly-bound-vars))
        (fgl-interp-error
         :msg (fgl-msg "Bind-free error: ~x0 evaluated to an alist containing duplicate vars: ~x1" untrans-form val)))

       (interp-st (interp-st-set-bindings (append val (interp-st-bindings interp-st)) interp-st)))
    (fgl-interp-value t))
  ///
  (local
   (defthm major-stack-bfrlist-of-stack$a-set-bindings
     (implies (and (not (member v (major-stack-bfrlist stack)))
                   (not (member v (fgl-object-bindings-bfrlist bindings))))
              (not (member v (major-stack-bfrlist (stack$a-set-bindings bindings stack)))))
     :hints(("Goal" :in-theory (enable stack$a-set-bindings
                                       major-stack-bfrlist
                                       major-frame-bfrlist
                                       minor-frame-bfrlist
                                       minor-stack-bfrlist)
             :do-not-induct t))))

  (local
   (defthm fgl-object-bindings-bfrlist-of-stack$a-bindings-bindings
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (fgl-object-bindings-bfrlist (stack$a-bindings stack)))))
     :hints(("Goal" :in-theory (enable stack$a-bindings
                                       major-stack-bfrlist
                                       major-frame-bfrlist)
             :do-not-induct t))))

  (local (in-theory (disable stack$a-set-bindings
                             stack$a-bindings
                             stack$a-minor-bindings)))

  (local (in-theory (enable bfr-listp-when-not-member-witness)))
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st)))

  (defret interp-st-get-of-<fn>
    (implies (member (interp-st-field-fix key)
                     '(:logicman :bvar-db :pathcond :constraint :constraint-db :equiv-contexts :reclimit))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret multivalues-of-<fn>
    (equal (list . <values>)
           <call>))

  (defret <fn>-preserves-errmsg
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (local (acl2::use-trivial-ancestors-check))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



;; Used in merge-branches to recognize a branch on which we can unify some
;; function.  BOZO We might want to try more than one function for some objects
;; -- e.g. for :g-integer we could do both int and intcons, for concrete values
;; that are conses we could do both concrete and bool, etc.  Ideally we'd try
;; all the functions that the argument could unify with.
(define fgl-fncall-object->fn ((x fgl-object-p))
  :returns (fn pseudo-fnsym-p) ;; nil if didn't match
  (fgl-object-case x
    :g-boolean 'bool
    :g-integer 'int
    :g-concrete 'concrete
    :g-apply x.fn
    :g-cons 'cons
    :g-ite 'if
    :otherwise nil))


(defthm fgl-ev-list-of-kwote-lst
  (equal (fgl-ev-list (kwote-lst x) a)
         (true-list-fix x))
  :hints (("goal" :induct (len x))))

(defthm not-quote-when-pseudo-fnsym-p
  (implies (pseudo-fnsym-p x)
           (not (equal x 'quote))))

(define fgl-object-recognize-merge-fncall ((x fgl-object-p))
  ;; Note: This is used when we want to merge two calls of the same function,
  ;; e.g.  (if test (foo x y) (foo w z)).  We don't want to match a g-boolean
  ;; to (bool x), for example, because that would lead to an infinite loop where we
  ;; match (if test (g-boolean b) (g-boolean c)) as
  ;; (if test (bool (g-boolean b)) (bool (g-boolean c)))
  ;; then merge the args, i.e. (list (g-boolean b)) (list (g-boolean c))
  ;; in which when we merge the first arg we get back to
  ;; (if test (g-boolean b) (g-boolean c)) and get stuck in an infinite loop.
  :returns (mv (fn pseudo-fnsym-p :rule-classes (:rewrite (:type-prescription :typed-term fn)))
               (args fgl-objectlist-p))
  (fgl-object-case x
    ;; :g-boolean (mv 'bool (list (fgl-object-fix x)))
    ;; :g-integer (mv 'int (list (fgl-object-fix x)))
    ;; :g-concrete (mv 'concrete (list (fgl-object-fix x)))
    :g-apply (mv x.fn x.args)
    :g-cons (mv 'cons (list x.car x.cdr))
    :g-concrete (if (consp x.val)
                    (mv 'cons (list (g-concrete (car x.val))
                                    (g-concrete (cdr x.val))))
                  (mv nil nil))
    :otherwise (mv nil nil))
  ///

  (defret eval-when-fgl-object-recognize-merge-fncall2
    (implies (and fn
                  (equal fn1 fn))
             (equal (fgl-ev (cons fn1
                                         (kwote-lst (fgl-objectlist-eval args env)))
                                   a)
                    (fgl-object-eval x env)))
    :hints(("Goal" :in-theory (enable fgl-apply fgl-objectlist-eval
                                      fgl-ev-of-fncall-args))))

  (defret bfr-listp-fgl-objectlist-bfrlist-of-<fn>
    (implies (bfr-listp (fgl-object-bfrlist x))
             (bfr-listp (fgl-objectlist-bfrlist args)))
    :hints (("goal" :Expand ((fgl-object-bfrlist x))))))


(defthm logicman-get-of-bfr-ite-bss-fn
  (implies (and (not (equal (logicman-field-fix key) :aignet))
                (not (equal (logicman-field-fix key) :strash)))
           (equal (logicman-get key (mv-nth 1 (bfr-ite-bss-fn c v1 v0 logicman)))
                  (logicman-get key logicman)))
  :hints(("Goal" :in-theory (enable bfr-ite-bss-fn
                                    bfr-ite-bss-fn-aux))))

(define fgl-object-basic-merge ((test lbfr-p)
                               (then fgl-object-p)
                               (else fgl-object-p)
                               (make-ites-p)
                               &optional
                               (logicman 'logicman))
  :measure (acl2::two-nats-measure (+ (fgl-object-count then)
                                      (fgl-object-count else))
                                   (+ (acl2-count (g-concrete->val then))
                                      (acl2-count (g-concrete->val else))))
  :prepwork ((local (include-book "primitive-lemmas"))
             (local (defthm-fgl-bfr-object-fix-flag
                      (defthm fgl-object-count-of-fgl-bfr-object-fix
                        (equal (fgl-object-count (fgl-bfr-object-fix x))
                               (fgl-object-count x))
                        :hints ('(:in-theory (enable fgl-object-count)
                                  :expand ((fgl-bfr-object-fix x))))
                        :flag fgl-bfr-object-fix)
                      (defthm fgl-objectlist-count-of-fgl-bfr-objectlist-fix
                        (equal (fgl-objectlist-count (fgl-bfr-objectlist-fix x))
                               (fgl-objectlist-count x))
                        :hints ('(:in-theory (enable fgl-objectlist-count)
                                  :expand ((fgl-bfr-objectlist-fix x))))
                        :flag fgl-bfr-objectlist-fix)
                      (defthm fgl-object-alist-count-of-fgl-bfr-object-alist-fix
                        (equal (fgl-object-alist-count (fgl-bfr-object-alist-fix x))
                               (fgl-object-alist-count x))
                        :hints ('(:in-theory (enable fgl-object-alist-count)
                                  :expand ((fgl-bfr-object-alist-fix x)
                                           (fgl-object-alist-count x)
                                           (fgl-object-alist-fix x))))
                        :flag fgl-bfr-object-alist-fix)))

             (local (defthm g-concrete->val-of-fgl-bfr-object-fix
                      (implies (fgl-object-case x :g-concrete)
                               (equal (g-concrete->val (fgl-bfr-object-fix x))
                                      (g-concrete->val x)))
                      :hints(("Goal" :in-theory (enable fgl-bfr-object-fix)))))

             (local (defthm fgl-object-kind-of-fgl-bfr-object-fix
                      (equal (fgl-object-kind (fgl-bfr-object-fix x))
                             (fgl-object-kind x))
                      :hints(("Goal" :expand  ((fgl-bfr-object-fix x))))))

             (local (defthm fgl-object-count-of-gobj-syntactic-list->car
                      (implies (gobj-syntactic-consp x)
                               (<= (fgl-object-count (gobj-syntactic-list->car x))
                                   (fgl-object-count x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-list->car gobj-syntactic-consp fgl-object-count)))
                      :rule-classes :linear))
             (local (defthm fgl-object-count-of-gobj-syntactic-list->cdr
                      (implies (gobj-syntactic-consp x)
                               (<= (fgl-object-count (gobj-syntactic-list->cdr x))
                                   (fgl-object-count x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-list->cdr gobj-syntactic-consp fgl-object-count)))
                      :rule-classes :linear))

             (local (defthm gobj-syntactic-consp-of-fgl-bfr-object-fix
                      (equal (gobj-syntactic-consp (fgl-bfr-object-fix x))
                             (gobj-syntactic-consp x))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-consp)))))

             (local (defthm gobj-syntactic-booleanp-of-fgl-bfr-object-fix
                      (equal (gobj-syntactic-booleanp (fgl-bfr-object-fix x))
                             (gobj-syntactic-booleanp x))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-booleanp)))))

             (local (defthm gobj-syntactic-integerp-of-fgl-bfr-object-fix
                      (equal (gobj-syntactic-integerp (fgl-bfr-object-fix x))
                             (gobj-syntactic-integerp x))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-integerp)))))

             (local (defthm acl2-count-of-gobj-syntactic-list->car
                      (implies (and (gobj-syntactic-consp x)
                                    (equal (fgl-object-count (gobj-syntactic-list->car x))
                                           (fgl-object-count x)))
                               (< (acl2-count (g-concrete->val (fgl-bfr-object-fix (gobj-syntactic-list->car x))))
                                  (acl2-count (g-concrete->val x))))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-list->car gobj-syntactic-consp fgl-object-count)))
                      :rule-classes :linear))
             (local (defthm acl2-count-of-gobj-syntactic-list->cdr
                      (implies (and (gobj-syntactic-consp x)
                                    (equal (fgl-object-count (gobj-syntactic-list->cdr x))
                                           (fgl-object-count x)))
                               (< (acl2-count (g-concrete->val (fgl-bfr-object-fix (gobj-syntactic-list->cdr x))))
                                  (acl2-count (g-concrete->val x))))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-list->cdr gobj-syntactic-consp fgl-object-count)))
                      :rule-classes :linear))

             (local (defthm gobj-syntactic-list->car-of-fgl-bfr-object-fix
                      (equal (gobj-syntactic-list->car (fgl-bfr-object-fix x))
                             (fgl-bfr-object-fix (gobj-syntactic-list->car x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-list->car fgl-bfr-object-fix)
                              :expand ((fgl-bfr-object-fix x))))))

             (local (defthm gobj-syntactic-list->cdr-of-fgl-bfr-object-fix
                      (equal (gobj-syntactic-list->cdr (fgl-bfr-object-fix x))
                             (fgl-bfr-object-fix (gobj-syntactic-list->cdr x)))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-list->cdr fgl-bfr-object-fix)
                              :expand ((fgl-bfr-object-fix x))))))

             (local (defthm gobj-syntactic-integer->bits-of-fgl-bfr-object-fix
                      (equal (gobj-syntactic-integer->bits (fgl-bfr-object-fix x))
                             (true-list-fix (bfr-list-fix (gobj-syntactic-integer->bits x))))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-integer->bits fgl-bfr-object-fix)
                              :expand ((fgl-bfr-object-fix x))))))

             (local (defthm bfr-p-when-booleanp
                      (implies (booleanp x)
                               (bfr-p x))
                      :hints(("Goal" :in-theory (enable booleanp)))))

             (local (defthm gobj-syntactic-boolean->bool-of-fgl-bfr-object-fix
                      (implies (gobj-syntactic-booleanp x)
                               (equal (gobj-syntactic-boolean->bool (fgl-bfr-object-fix x))
                                      (bfr-fix (gobj-syntactic-boolean->bool x))))
                      :hints(("Goal" :in-theory (enable gobj-syntactic-boolean->bool
                                                        gobj-syntactic-booleanp
                                                        fgl-bfr-object-fix)
                              :expand ((fgl-bfr-object-fix x))))))

             (local (defthm equal-of-fgl-object-eval-when-equal-of-fgl-bfr-object-fix
                      (let ((bfrstate (logicman->bfrstate)))
                        (implies (equal (fgl-bfr-object-fix x) (fgl-bfr-object-fix y))
                                 (equal (equal (fgl-object-eval x env)
                                               (fgl-object-eval y env))
                                        t)))
                      :hints (("goal" :use ((:instance fgl-object-eval-of-fgl-bfr-object-fix
                                             (x x))
                                            (:instance fgl-object-eval-of-fgl-bfr-object-fix
                                             (x y)))
                               :in-theory (disable fgl-object-eval-of-fgl-bfr-object-fix))))))
  :verify-guards nil
  :returns (mv (okp)
               (obj fgl-object-p)
               new-logicman)
  :guard-hints (("goal" :in-theory (enable bfr-ite-bss-fn)))
  :guard (and (fgl-bfr-object-p then (logicman->bfrstate))
              (fgl-bfr-object-p else (logicman->bfrstate)))
  (b* ((bfrstate (logicman->bfrstate))
       (then (fgl-bfr-object-fix then))
       (else (fgl-bfr-object-fix else))
       ((when (equal (fgl-object-fix then)
                     (fgl-object-fix else)))
        (mv t (fgl-bfr-object-fix then) logicman))
       ((when (and (gobj-syntactic-booleanp then)
                   (gobj-syntactic-booleanp else)))
        (b* (((mv bfr logicman)
              (bfr-ite (bfr-fix test)
                       (gobj-syntactic-boolean->bool then)
                       (gobj-syntactic-boolean->bool else)
                       logicman)))
          (mv t (mk-g-boolean bfr) logicman)))
       ((when (and (gobj-syntactic-integerp then)
                   (gobj-syntactic-integerp else)))
        (b* (((mv bfr logicman)
              (bfr-ite-bss-fn (bfr-fix test)
                            (gobj-syntactic-integer->bits then)
                            (gobj-syntactic-integer->bits else)
                            logicman)))
          (mv t (mk-g-integer bfr) logicman)))
       ((when (and (gobj-syntactic-consp then)
                   (gobj-syntactic-consp else)))
        (b* ((test (bfr-fix test))
             ((mv car-ok car logicman)
              (fgl-object-basic-merge test
                                     (gobj-syntactic-list->car then)
                                     (gobj-syntactic-list->car else)
                                     make-ites-p
                                     logicman))
             ((unless car-ok)
              (mv nil nil logicman))
             ((mv cdr-ok cdr logicman)
              (fgl-object-basic-merge test
                                     (gobj-syntactic-list->cdr then)
                                     (gobj-syntactic-list->cdr else)
                                     make-ites-p
                                     logicman))
             ((unless cdr-ok)
              (mv nil nil logicman)))
          (mv t (mk-g-cons car cdr) logicman))))
    (mv make-ites-p
        (if make-ites-p (g-ite (mk-g-boolean (bfr-fix test)) then else) nil)
        logicman))
  ///
  (local (in-theory (disable bfr-listp-when-not-member-witness
                             fgl-bfr-object-fix-when-fgl-bfr-object-p
                             (:d fgl-object-basic-merge))))
  ;; (defret fgl-bfr-object-p-of-<fn>
  ;;   (fgl-bfr-object-p obj (logicman->bfrstate new-logicman)))

  (fty::deffixequiv fgl-object-basic-merge
    :hints (("goal" :induct t)
            '(:expand ((:free (test else) (fgl-object-basic-merge test then else make-ites-p))
                       (:free (test then) (fgl-object-basic-merge test then else make-ites-p))))))


  (local (defthm bfr-listp-fgl-object-bfrlist-of-fgl-bfr-object-fix
           (bfr-listp (fgl-object-bfrlist (fgl-bfr-object-fix x)))
           :hints (("goal" :use ((:instance return-type-of-fgl-bfr-object-fix.new-x))
                    :in-theory (disable return-type-of-fgl-bfr-object-fix.new-x)))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints (("goal" :expand (<call>) :induct <call>)))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (bfr-nvars logicman))
    :hints (("goal" :expand (<call>) :induct <call>)))

  (defret bfr-listp-of-fgl-object-basic-merge
    ;; (implies (and (lbfr-p test)
    ;;               (lbfr-listp (fgl-object-bfrlist thenval))
    ;;               (lbfr-listp (fgl-object-bfrlist elseval)))
    (bfr-listp (fgl-object-bfrlist obj) (logicman->bfrstate new-logicman))
    :hints (("goal" :expand (<call>) :induct <call>)
            (and stable-under-simplificationp
                 '(:in-theory (enable bfr-listp-when-not-member-witness)))))

  (verify-guards fgl-object-basic-merge-fn
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable bfr-listp-when-not-member-witness)))))

  (defret eval-of-fgl-object-basic-merge
    (implies okp
             (equal (fgl-object-eval obj env new-logicman)
                    (if (gobj-bfr-eval test env)
                        (fgl-object-eval then env logicman)
                      (fgl-object-eval else env logicman))))
    :hints(("Goal" :expand (<call>) :induct <call>
            :in-theory (enable gobj-bfr-eval ;; gobj-bfr-list-eval-is-bfr-list-eval
                               fgl-object-eval-when-gobj-syntactic-consp))))

  (local (defthm fgl-bfr-objectlist-of-fgl-bfr-object-fix
           (bfr-listp (fgl-object-bfrlist (fgl-bfr-object-fix x bfrstate)) bfrstate)
           :hints (("goal" :use ((:instance fgl-bfr-object-p-when-fgl-object-p
                                  (x (fgl-bfr-object-fix x bfrstate))))))))

  (deffixequiv fgl-object-basic-merge
    :hints (("goal" :induct (fgl-object-basic-merge test then else logicman)
             :expand ((:free (then) (fgl-object-basic-merge test then else logicman))
                      (:free (else) (fgl-object-basic-merge test then else logicman))))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :aignet))
                  (not (equal (logicman-field-fix key) :strash)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman)))
    :hints(("Goal" :expand (<call>) :induct <call>))))

(define interp-st-fgl-object-basic-merge ((test interp-st-bfr-p)
                                         (then fgl-object-p)
                                         (else fgl-object-p)
                                         interp-st
                                         state)
  :returns (mv (obj fgl-object-p)
               new-interp-st
               new-state)

  :guard (and (interp-st-bfr-listp (fgl-object-bfrlist then) interp-st)
              (interp-st-bfr-listp (fgl-object-bfrlist else) interp-st))
  (b* ((make-ites (interp-flags->make-ites (interp-st->flags interp-st))))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (okp obj logicman)
               (fgl-object-basic-merge test then else make-ites logicman)
               (b* (((unless okp)
                     (fgl-interp-error :msg "If-then-else failed to merge -- see debug obj"
                                      :debug-obj (list :test test
                                                       :then (fgl-object-fix then)
                                                       :else (fgl-object-fix else)))))
                 (mv obj interp-st state))))
  ///


  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st)))

  (defret bfr-object-p-of-<fn>
    (lbfr-listp (fgl-object-bfrlist obj) (interp-st->logicman new-interp-st)))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p (interp-st->logicman new-interp-st) (interp-st->logicman interp-st)))

  (defret eval-of-interp-st-fgl-object-basic-merge
    (implies (not (interp-st->errmsg new-interp-st))
             (equal (fgl-object-eval obj env (interp-st->logicman new-interp-st))
                    (if (gobj-bfr-eval test env (interp-st->logicman interp-st))
                        (fgl-object-eval then env (interp-st->logicman interp-st))
                      (fgl-object-eval else env (interp-st->logicman interp-st))))))

  (defret interp-st-get-of-<fn>
    (implies (and (equal key1 (interp-st-field-fix key))
                  (not (equal key1 :logicman))
                  (not (equal key1 :errmsg))
                  (not (equal key1 :debug-info))
                  (not (equal key1 :debug-stack)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-return-values-correct
    (equal (list . <values>)
           <call>))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (local (acl2::use-trivial-ancestors-check))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))






(define fgl-interp-finish-simplify-if-test-ite ((test-bfr interp-st-bfr-p)
                                               (then-bfr interp-st-bfr-p)
                                               (else-bfr interp-st-bfr-p)
                                               (then-unreachable)
                                               (else-unreachable)
                                               interp-st
                                               state)
  :returns (mv (ite (interp-st-bfr-p ite new-interp-st))
               new-interp-st
               new-state)
  (b* (((when then-unreachable)
        (if else-unreachable
            (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
              (mv nil interp-st state))
          (mv (interp-st-bfr-fix else-bfr) interp-st state)))
       ((when else-unreachable)
        (mv (interp-st-bfr-fix then-bfr) interp-st state)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ite logicman)
               (bfr-ite test-bfr then-bfr else-bfr)
               (mv ite interp-st state)))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st)))

  (defret lbfr-p-of-<fn>
    (lbfr-p ite (interp-st->logicman new-interp-st)))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :errmsg)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret <fn>-preserves-errmsg
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret <fn>-correct
    (implies (and (implies then-unreachable
                           (not (gobj-bfr-eval test-bfr env (interp-st->logicman interp-st))))
                  (implies else-unreachable
                           (gobj-bfr-eval test-bfr env (interp-st->logicman interp-st))))
             (equal (gobj-bfr-eval ite env (interp-st->logicman new-interp-st))
                    (if* (gobj-bfr-eval test-bfr env (interp-st->logicman interp-st))
                         (gobj-bfr-eval then-bfr env (interp-st->logicman interp-st))
                         (gobj-bfr-eval else-bfr env (interp-st->logicman interp-st)))))
    :hints(("Goal" :in-theory (enable gobj-bfr-eval))))

  (defret <fn>-return-values-correct
    (equal (list . <values>)
           <call>))

  (defret <fn>-unreachable-when-then
    (implies (not then-unreachable)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret <fn>-unreachable-when-else
    (implies (not else-unreachable)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))








(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local
 (defthm pseudo-term-bindinglist-count-when-consp
   (implies (consp x)
            (< (+ (pseudo-term-binding-count (car x))
                  (pseudo-term-list-binding-count (cdr x)))
               (pseudo-term-list-binding-count x)))
    :rule-classes :linear))

(local (defthm len-of-cons
         (equal (len (cons a b))
                (+ 1 (len b)))))

(local (defthm and*-hyp
         (implies (acl2::rewriting-negative-literal `(acl2::binary-and* ,a ,b))
                  (iff (and* a b) (and a b)))))

(local (defun len-is (x n)
         (if (zp n)
             (and (eql n 0) (atom x))
           (and (consp x)
                (len-is (cdr x) (1- n))))))

(local (defthm open-len-is
         (implies (syntaxp (quotep n))
                  (equal (len-is x n)
                         (if (zp n)
                             (and (eql n 0) (atom x))
                           (and (consp x)
                                (len-is (cdr x) (1- n))))))))


(local (defthm equal-len-hyp
         (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
                                    (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
                                (quotep n)))
                  (equal (equal (len x) n)
                         (len-is x n)))))

(local (defthm fgl-object-count-of-car-weak
         (<= (fgl-object-count (car x)) (fgl-objectlist-count x))
         :hints (("goal" :cases ((consp x))))
         :rule-classes :linear))

(local (defthm fgl-objectlist-count-of-cdr-weak
         (<= (fgl-objectlist-count (cdr x)) (fgl-objectlist-count x))
         :hints (("goal" :cases ((consp x))))
         :rule-classes :linear))

(local (defthm mv-nth-of-cons
         (equal (mv-nth n (cons a b))
                (if (zp n) a (mv-nth (1- n) b)))
         :hints(("Goal" :in-theory (enable mv-nth)))))


(local (defthm len-cdr-less-when-consp
         (implies (consp x)
                  (< (len (cdr x)) (len x)))
         :rule-classes :linear))

(local (defthm stack$a-open-nth-scratch
         (implies (and (syntaxp (quotep n))
                       (< (nfix n) (stack$a-scratch-len stack)))
                  (equal (stack$a-nth-scratch n stack)
                         (if (zp n)
                             (stack$a-top-scratch stack)
                           (stack$a-nth-scratch (1- n)
                                                (stack$a-pop-scratch stack)))))
         :hints(("Goal" :in-theory (e/d (stack$a-top-scratch stack$a-pop-scratch stack$a-nth-scratch
                                           stack$a-scratch-len len)
                                        ())
                 :expand ((major-stack-nth-scratch n stack)
                          (minor-stack-nth-scratch n (major-frame->minor-stack (car stack)))
                          (:free (stack) (major-stack-nth-scratch (+ -1 n) stack))
                          (:free (stack) (minor-stack-nth-scratch (+ -1 n) stack))
                          (major-stack-nth-scratch 0 stack)
                          (minor-stack-nth-scratch 0 (major-frame->minor-stack (car stack)))
                          (minor-stack-scratch-len (major-frame->minor-stack (car stack)))
                          (:free (a b) (minor-stack-scratch-len (cons a b))))))))



(local (in-theory (disable (tau-system) len default-car default-cdr
                           pseudo-termp
                           pseudo-term-listp
                           fgetprop
                           not
                           acl2::nfix-when-not-natp
                           equal-of-booleans-rewrite
                           mv-nth-cons-meta
                           take
                           acl2::take-of-too-many
                           acl2::take-of-len-free
                           acl2::take-when-atom
                           acl2::lower-bound-of-len-when-sublistp
                           append)))


(define fgl-interp-check-reclimit (interp-st)
  :inline t
  (or (zp (interp-st->reclimit interp-st))
      (interp-st->errmsg interp-st))
  ///
  (defthm not-check-reclimit-implies-posp-reclimit
    (implies (not (fgl-interp-check-reclimit interp-st))
             (posp (interp-st->reclimit interp-st)))
    :rule-classes :forward-chaining)

  (def-updater-independence-thm fgl-interp-check-reclimit-of-update
    (implies (and (equal (interp-st->reclimit new) (interp-st->reclimit old))
                  (equal (interp-st->errmsg new) (interp-st->errmsg old)))
             (equal (fgl-interp-check-reclimit new) (fgl-interp-check-reclimit old)))))

(define fgl-interp-test-equiv-contexts ((contexts equiv-contextsp))
  :returns (new-contexts equiv-contextsp)
  (if (member-eq 'unequiv (equiv-contexts-fix contexts))
      '(unequiv)
    '(iff)))

(define fgl-interp-lambda-arglist-equiv-contexts ((contexts equiv-contextsp))
  :returns (new-contexts equiv-contextsp)
  (and (member-eq 'unequiv (equiv-contexts-fix contexts))
       '(unequiv)))


;; ;; BOZO change this to derive argcontexts based on congruence rules!
;; (define fgl-interp-arglist-equiv-contexts ((contexts equiv-contextsp)
;;                                            (fn pseudo-fnsym-p)
;;                                            (arity natp))
;;   :returns (new-contexts equiv-argcontexts-p)
;;   :ignore-ok t :irrelevant-formals-ok t
;;   (and (member-eq 'unequiv (equiv-contexts-fix contexts))
;;        t)
;;   ///
;;   (local (defthm nth-equiv-when-equal-length
;;            (implies (equal (len x) (len y))
;;                     (equal (acl2::nth-equiv x y)
;;                            (acl2::list-equiv x y)))
;;            :hints(("Goal" :in-theory (enable acl2::list-equiv acl2::nth-equiv-recursive true-list-fix
;;                                              acl2::nth-equiv-ind len)
;;                    :induct (acl2::nth-equiv x y)))))

;;   (local (fty::deffixcong acl2::list-equiv equal (kwote-lst x) x
;;            :hints(("Goal" :in-theory (enable true-list-fix)))))

;;   (defret <fn>-correct
;;     (fgl-ev-argcontext-congruence-correct-p contexts fn new-contexts arity)
;;     :hints(("Goal" :in-theory (enable fgl-ev-argcontext-congruence-correct-p)))))


(define fgl-interp-equiv-refinementp ((equiv pseudo-fnsym-p)
                                     (contexts equiv-contextsp))
  :hooks ((:fix :args (contexts)))
  (b* (;; (equiv (pseudo-fnsym-fix equiv))  BOZO we don't fix this because it messes up some stuff
       (contexts (equiv-contexts-fix contexts)))
    (or (eq equiv 'equal)
        (member-eq equiv contexts)
        (member-eq 'unequiv contexts))))

(defun fgl-interp-fncall-special-case-fn (cases)
  (b* (((when (atom cases))
        '((otherwise (fgl-interp-value nil nil))))
       ((list (list fn arity) term) (car cases)))
    (cons `(,fn
            (if (eql (len args) ,arity)
                (b* (((fgl-interp-value ans) ,term))
                  (fgl-interp-value t ans))
              (fgl-interp-error :msg (fgl-msg "Bad arity in special fncall: ~x0"
                                             (cons (pseudo-fnsym-fix fn) (pseudo-term-list-fix args)))
                               :nvals 2)))
          (fgl-interp-fncall-special-case-fn (cdr cases)))))

(defmacro fgl-interp-fncall-special-case (fn &rest cases)
  `(case ,fn
     . ,(fgl-interp-fncall-special-case-fn cases)))


(define equiv-contexts-coarsening-p ((x equiv-contextsp)
                                     (y equiv-contextsp))
  :returns (coarseningp)
  (b* ((x (equiv-contexts-fix x))
       (y (equiv-contexts-fix y))
       ((when (eq y nil)) t) ;; y is the finest equiv context
       ((when (member 'unequiv x)) t) ;; x is the coarsest equiv context
       ((when (equal x y)) t))
    nil)
  ///
  ;; (local (in-theory (disable equiv-contexts-fix-under-iff)))
  (local (defthm not-equiv-contexts-fix
           (implies (not (consp y))
                    (cmr::equiv-contexts-equiv y nil))
           :rule-classes :forward-chaining))

  (defthm fgl-ev-context-equiv-when-coarsening-p
    (implies (and (equiv-contexts-coarsening-p x y)
                  (equal (fgl-ev-context-fix y a)
                         (fgl-ev-context-fix y b)))
             (equal (equal (fgl-ev-context-fix x a)
                           (fgl-ev-context-fix x b))
                    t))))

(set-state-ok t)


;; bozo move to own book
(define easy-arity ((fn (or (and (consp fn)
                                 (consp (cdr fn))
                                 (true-listp (cadr fn)))
                            (symbolp fn)))
                    (w plist-worldp))
  :returns (nargs (equal nargs (arity fn w))
                  :hints(("Goal" :in-theory (enable arity length))))
  (cond ((acl2::flambdap fn) (length (acl2::lambda-formals fn)))
        (t (let ((temp (getpropc fn 'formals t w)))
             (cond ((eq temp t) nil)
                   (t (if (stringp temp) (length temp) (len temp))))))))

(defines easy-termp
  (define easy-termp (x (w plist-worldp))
    :no-function t
    :verify-guards nil
    :returns (ans (equal ans (termp x w))
                  :hints ('(:expand ((termp x w)))))
    :prepwork ((local (in-theory (disable termp term-listp
                                          acl2::legal-variablep
                                          acl2::arglistp1
                                          acl2::all-vars1
                                          acl2-count
                                          true-listp))))
    (cond ((acl2::variablep x) (acl2::legal-variablep x))
          ((acl2::fquotep x)
           (and (consp (cdr x)) (null (cddr x))))
          ((symbolp (car x))
           (let ((arity (easy-arity (car x) w)))
             (and arity
                  (easy-term-listp (cdr x) w)
                  (eql (length (cdr x)) arity))))
          ((and (consp (car x))
                (true-listp (car x))
                (eq (caar x) 'lambda)
                (eql 3 (length (car x)))
                (acl2::arglistp (cadr (car x)))
                (easy-termp (caddr (car x)) w)
                (null (set-difference-eq (all-vars (caddr (car x)))
                                         (cadr (car x))))
                (easy-term-listp (cdr x) w)
                (eql (length (cadr (car x)))
                     (length (cdr x))))
           t)
          (t nil)))
  (define easy-term-listp (x (w plist-worldp))
    :no-function t
    :returns (ans (equal ans (term-listp x w))
                  :hints ('(:expand ((term-listp x w)))))
    (cond ((atom x) (equal x nil))
          ((easy-termp (car x) w)
           (easy-term-listp (cdr x) w))
          (t nil)))
  ///
  (local (defthm symbolp-when-legal-variablep
           (implies (acl2::legal-variablep x)
                    (symbolp x))
           :hints(("Goal" :in-theory (enable acl2::legal-variablep)))))
  (local (defthm symbol-listp-when-arglistp1
           (implies (acl2::arglistp1 x)
                    (symbol-listp x))
           :hints(("Goal" :in-theory (enable acl2::arglistp1)))))
  (local (defthm true-listp-when-arglistp1
           (implies (acl2::arglistp1 x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable acl2::arglistp1)))))

  #!acl2
  (local (flag::make-flag all-vars1-flag all-vars1))
  #!acl2
  (local (defthm-all-vars1-flag
           (defthm true-listp-of-all-vars1
             (implies (true-listp ans)
                      (true-listp (all-vars1 term ans)))
             :hints ('(:expand ((all-vars1 term ans))))
             :flag all-vars1)
           (defthm true-listp-of-all-vars1-lst
             (implies (true-listp ans)
                      (true-listp (all-vars1-lst lst ans)))
             :hints ('(:expand ((all-vars1-lst lst ans))))
             :flag all-vars1-lst)))

  (defthm-easy-termp-flag
    (defthm termp-implies-pseudo-termp
      (implies (termp x w)
               (pseudo-termp x))
      :hints ('(:expand ((termp x w)
                         (pseudo-termp x))))
      :flag easy-termp)
    (defthm term-listp-implies-pseudo-term-listp
      (implies (term-listp x w)
               (pseudo-term-listp x))
      :hints ('(:expand ((term-listp x w)
                         (pseudo-term-listp x))))
      :flag easy-term-listp))



  (verify-guards easy-termp))


(define fgl-objectlist-find-ite ((x fgl-objectlist-p))
  :returns (ite fgl-object-p)
  (if (atom x)
      nil
    (if (fgl-object-case (car x) :g-ite)
        (fgl-object-fix (car x))
      (fgl-objectlist-find-ite (cdr x))))
  ///
  (defret fgl-object-kind-of-<fn>
    (iff (equal (fgl-object-kind ite) :g-ite)
         ite))

  (defret bfr-listp-of-fgl-objectlist-find-ite
    (implies (bfr-listp (fgl-objectlist-bfrlist x))
             (bfr-listp (fgl-object-bfrlist ite)))))

(define fgl-objectlist-split ((test fgl-object-p)
                             (x fgl-objectlist-p))
  :returns (mv (then fgl-objectlist-p)
               (else fgl-objectlist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv rest-then rest-else) (fgl-objectlist-split test (cdr x)))
       (x1 (fgl-object-fix (car x)))
       ((when (and (fgl-object-case x1 :g-ite)
                   (equal (g-ite->test x1) (fgl-object-fix test))))
        (mv (cons (g-ite->then x1) rest-then)
            (cons (g-ite->else x1) rest-else))))
    (mv (cons x1 rest-then)
        (cons x1 rest-else)))
  ///
  (local (defthm fgl-objectlist-eval-of-atom
           (implies (not (Consp x))
                    (equal (fgl-objectlist-eval x env logicman) nil))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (defret fgl-objectlist-split-correct-true
    (implies (fgl-object-eval test env)
             (equal (fgl-objectlist-eval then env)
                    (fgl-objectlist-eval x env))))

  (defret fgl-objectlist-split-correct-false
    (implies (not (fgl-object-eval test env))
             (equal (fgl-objectlist-eval else env)
                    (fgl-objectlist-eval x env))))

  (defret fgl-objectlist-count-of-fgl-objectlist-split-weak
    (and (<= (fgl-objectlist-count then) (fgl-objectlist-count x))
         (<= (fgl-objectlist-count else) (fgl-objectlist-count x)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-count)))
    :rule-classes :linear)

  (defret fgl-objectlist-count-of-fgl-objectlist-split-strong
    :pre-bind ((ite (fgl-objectlist-find-ite x))
               (test (g-ite->test ite)))
    (implies ite
             (and (< (fgl-objectlist-count then) (fgl-objectlist-count x))
                  (< (fgl-objectlist-count else) (fgl-objectlist-count x))))
    :hints(("Goal" :in-theory (enable fgl-objectlist-find-ite
                                      fgl-objectlist-count)))
    :rule-classes :linear)

  (defret bfr-listp-of-fgl-objectlist-split
    (implies (bfr-listp (fgl-objectlist-bfrlist x))
             (and (bfr-listp (fgl-objectlist-bfrlist then))
                  (bfr-listp (fgl-objectlist-bfrlist else))))
    :hints(("Goal" :in-theory (enable bfr-listp-when-not-member-witness)))))


(define fgl-good-fgl-rule-p ((x fgl-rule-p))
  (fgl-ev-theoremp (fgl-rule-term x)))



(define fgl-good-fgl-rules-p ((x fgl-rulelist-p))
  (if (atom x)
      t
    (and (fgl-good-fgl-rule-p (car x))
         (fgl-good-fgl-rules-p (cdr x))))
  ///
  (local
   (defthmd fgl-ev-when-theoremp
     (implies (fgl-ev-theoremp x)
              (fgl-ev x a))
     :hints (("goal" :use fgl-ev-falsify))))

  (defthm fgl-good-fgl-rules-p-implies-conjoin-fgl-rulelist-terms
    (implies (fgl-good-fgl-rules-p x)
             (fgl-ev (conjoin (fgl-rulelist-terms x)) env))
    :hints(("Goal" :in-theory (enable fgl-rulelist-terms
                                      fgl-good-fgl-rule-p
                                      fgl-ev-when-theoremp))))

  (defthm fgl-good-fgl-rules-p-when-theoremp-conjoin
    (implies (fgl-ev-theoremp (conjoin (fgl-rulelist-terms x)))
             (fgl-good-fgl-rules-p x))
    :hints(("Goal" :in-theory (enable fgl-rulelist-terms
                                      fgl-good-fgl-rule-p
                                      fgl-ev-when-theoremp))))

  (defthm fgl-good-fgl-rules-p-of-append
    (implies (and (fgl-good-fgl-rules-p x)
                  (fgl-good-fgl-rules-p y))
             (fgl-good-fgl-rules-p (append x y)))))

(define interp-st-function-rules ((fn pseudo-fnsym-p) interp-st state)
  :returns (mv (rules fgl-rulelist-p) new-interp-st)
  (b* (((mv err rules) (fgl-function-rules fn (w state)))
       ((when err)
        (if (interp-st->errmsg interp-st)
            (mv rules interp-st)
          (b* ((interp-st (update-interp-st->errmsg err interp-st)))
            (mv rules interp-st)))))
    (mv rules interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (local (defret rules-ev-good-fgl-rules-p-of-<fn>
           (implies (and (rules-ev-meta-extract-global-facts :state st)
                         (equal (w st) (w state)))
                    (rules-ev-good-fgl-rules-p rules))))


  (local
   (defthmd fgl-ev-when-theoremp
     (implies (fgl-ev-theoremp x)
              (fgl-ev x a))
     :hints (("goal" :use fgl-ev-falsify))))

  (defret fgl-good-fgl-rules-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state)))
             (fgl-good-fgl-rules-p rules))
    :hints (("goal" :use ((:functional-instance rules-ev-good-fgl-rules-p-of-<fn>
                           (rules-ev fgl-ev)
                           (rules-ev-list fgl-ev-list)
                           (rules-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
                           (rules-ev-good-fgl-rules-p fgl-good-fgl-rules-p)
                           (rules-ev-good-fgl-rule-p fgl-good-fgl-rule-p)
                           (rules-ev-falsify fgl-ev-falsify)))
             :in-theory (enable fgl-good-fgl-rules-p
                                fgl-ev-when-theoremp
                                fgl-ev-of-nonsymbol-atom
                                fgl-ev-of-bad-fncall
                                fgl-ev-of-fncall-args))
            (and stable-under-simplificationp
                 (case-match clause
                   ((('equal (fn . &) &))
                    (and (symbolp fn)
                         `(:in-theory (enable ,fn))))
                   (& '(:use fgl-ev-meta-extract-global-badguy)))))))


(define interp-st-branch-merge-rules ((fn pseudo-fnsym-p) interp-st state)
  :returns (mv (rules fgl-rulelist-p) new-interp-st)
  (b* (((mv err rules) (fgl-branch-merge-rules fn (w state)))
       ((when err)
        (if (interp-st->errmsg interp-st)
            (mv rules interp-st)
          (b* ((interp-st (update-interp-st->errmsg err interp-st)))
            (mv rules interp-st)))))
    (mv rules interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (local (defret rules-ev-good-fgl-rules-p-of-<fn>
           (implies (and (rules-ev-meta-extract-global-facts :state st)
                         (equal (w st) (w state)))
                    (rules-ev-good-fgl-rules-p rules))))


  (local
   (defthmd fgl-ev-when-theoremp
     (implies (fgl-ev-theoremp x)
              (fgl-ev x a))
     :hints (("goal" :use fgl-ev-falsify))))

  (defret fgl-good-fgl-rules-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state)))
             (fgl-good-fgl-rules-p rules))
    :hints (("goal" :use ((:functional-instance rules-ev-good-fgl-rules-p-of-<fn>
                           (rules-ev fgl-ev)
                           (rules-ev-list fgl-ev-list)
                           (rules-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
                           (rules-ev-good-fgl-rules-p fgl-good-fgl-rules-p)
                           (rules-ev-good-fgl-rule-p fgl-good-fgl-rule-p)
                           (rules-ev-falsify fgl-ev-falsify)))
             :in-theory (enable fgl-good-fgl-rules-p
                                fgl-ev-when-theoremp
                                fgl-ev-of-nonsymbol-atom
                                fgl-ev-of-bad-fncall
                                fgl-ev-of-fncall-args))
            (and stable-under-simplificationp
                 (case-match clause
                   ((('equal (fn . &) &))
                    (and (symbolp fn)
                         `(:in-theory (enable ,fn))))
                   (& '(:use fgl-ev-meta-extract-global-badguy)))))))


(define interp-st-if-rules ((thenfn pseudo-fnsym-p) (elsefn pseudo-fnsym-p) interp-st state)
  :returns (mv (then-rules fgl-rulelist-p)
               (else-rules fgl-rulelist-p)
               (if-rules fgl-rulelist-p)
               new-interp-st)
  (b* (((mv then-rules interp-st) (if (pseudo-fnsym-fix thenfn)
                                      (interp-st-branch-merge-rules thenfn interp-st state)
                                    (mv nil interp-st)))
       ((mv else-rules interp-st) (if (pseudo-fnsym-fix elsefn)
                                      (interp-st-branch-merge-rules elsefn interp-st state)
                                    (mv nil interp-st)))
       ((mv if-rules interp-st) (interp-st-function-rules 'if interp-st state)))
    (mv then-rules else-rules if-rules interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (defret fgl-good-fgl-rules-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state)))
             (and (fgl-good-fgl-rules-p then-rules)
                  (fgl-good-fgl-rules-p else-rules)
                  (fgl-good-fgl-rules-p if-rules)))))


(define fgl-good-fgl-binder-rule-p ((x fgl-binder-rule-p))
  (and (fgl-ev-theoremp (fgl-binder-rule-term x))
       (fgl-ev-theoremp (fgl-binder-rule-equiv-term x)))
  ///
  (local (defthm fgl-ev-when-theoremp
           (implies (fgl-ev-theoremp x)
                    (fgl-ev x a))
           :hints (("Goal" :use fgl-ev-falsify))))

  (defthm binder-rule-term-when-fgl-good-fgl-binder-rule-p
    (implies (fgl-good-fgl-binder-rule-p x)
             (fgl-ev (fgl-binder-rule-term x) a)))

  (defthm binder-rule-equiv-term-when-fgl-good-fgl-binder-rule-p
    (implies (fgl-good-fgl-binder-rule-p x)
             (fgl-ev (fgl-binder-rule-equiv-term x) a))))

(define fgl-good-fgl-binder-rules-p ((x fgl-binder-rulelist-p))
  (if (atom x)
      t
    (and (fgl-good-fgl-binder-rule-p (car x))
         (fgl-good-fgl-binder-rules-p (cdr x))))
  ///
  (local
   (defthmd fgl-ev-when-theoremp
     (implies (fgl-ev-theoremp x)
              (fgl-ev x a))
     :hints (("goal" :use fgl-ev-falsify))))

  (defthm fgl-good-fgl-binder-rules-p-of-append
    (implies (and (fgl-good-fgl-binder-rules-p x)
                  (fgl-good-fgl-binder-rules-p y))
             (fgl-good-fgl-binder-rules-p (append x y)))))

(define interp-st-function-binder-rules ((fn pseudo-fnsym-p) interp-st state)
  :returns (mv (rules fgl-binder-rulelist-p) new-interp-st)
  (b* (((mv err rules) (fgl-function-binder-rules fn (w state)))
       ((when err)
        (if (interp-st->errmsg interp-st)
            (mv rules interp-st)
          (b* ((interp-st (update-interp-st->errmsg err interp-st)))
            (mv rules interp-st)))))
    (mv rules interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (local (defret rules-ev-good-fgl-binder-rules-p-of-<fn>
           (implies (and (rules-ev-meta-extract-global-facts :state st)
                         (equal (w st) (w state)))
                    (rules-ev-good-fgl-binder-rules-p rules))))


  (local
   (defthmd fgl-ev-when-theoremp
     (implies (fgl-ev-theoremp x)
              (fgl-ev x a))
     :hints (("goal" :use fgl-ev-falsify))))

  (defret fgl-good-fgl-binder-rules-p-of-<fn>
    (implies (and (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state)))
             (fgl-good-fgl-binder-rules-p rules))
    :hints (("goal" :use ((:functional-instance rules-ev-good-fgl-binder-rules-p-of-<fn>
                           (rules-ev fgl-ev)
                           (rules-ev-list fgl-ev-list)
                           (rules-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
                           (rules-ev-good-fgl-binder-rules-p fgl-good-fgl-binder-rules-p)
                           (rules-ev-good-fgl-binder-rule-p fgl-good-fgl-binder-rule-p)
                           (rules-ev-falsify fgl-ev-falsify)))
             :in-theory (enable fgl-good-fgl-binder-rules-p
                                fgl-good-fgl-binder-rule-p
                                fgl-ev-when-theoremp
                                fgl-ev-of-nonsymbol-atom
                                fgl-ev-of-bad-fncall
                                fgl-ev-of-fncall-args))
            (and stable-under-simplificationp
                 (case-match clause
                   ((('equal (fn . &) &))
                    (and (symbolp fn)
                         `(:in-theory (enable ,fn))))
                   (& '(:use fgl-ev-meta-extract-global-badguy)))))))



(local
 (defsection bfr-listp-lemmas

   (defthm major-stack-bfrlist-of-atom
      (implies (atom x)
               (equal (major-stack-bfrlist x) nil))
      :hints(("Goal" :in-theory (enable major-stack-bfrlist
                                        default-car)))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm major-stack-bfrlist-of-stack$a-push-scratch
      (set-equiv (major-stack-bfrlist (stack$a-push-scratch obj stack))
                 (append (scratchobj->bfrlist obj)
                         (major-stack-bfrlist stack)))
      :hints(("Goal" :in-theory (enable ;; major-stack-bfrlist
                                 major-frame-bfrlist
                                 ;; minor-stack-bfrlist
                                 minor-frame-bfrlist
                                 stack$a-push-scratch
                                 ;; acl2::set-unequal-witness-rw
                                 )
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))

   (defthm scratchlist-bfrlist-of-update-nth
      (implies (and (not (member v (scratchobj->bfrlist obj)))
                    (not (member v (scratchlist-bfrlist x))))
               (not (member v (scratchlist-bfrlist (update-nth n obj x)))))
      :hints(("Goal" :in-theory (enable update-nth))))

   (defthm bfrlist-of-stack$a-update-scratch
      (implies (and (not (member v (scratchobj->bfrlist obj)))
                    (not (member v (major-stack-bfrlist stack))))
               (not (member v (major-stack-bfrlist (stack$a-update-scratch n obj stack)))))
      :hints(("Goal" :in-theory (enable ;; major-stack-bfrlist
                                 major-frame-bfrlist
                                 ;; minor-stack-bfrlist
                                 minor-frame-bfrlist
                                 stack$a-update-scratch
                                 ;; acl2::set-unequal-witness-rw
                                 )
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))


   (defthm fgl-objectlist-bfrlist-of-append
            (equal (fgl-objectlist-bfrlist (append x y))
                   (append (fgl-objectlist-bfrlist x)
                           (fgl-objectlist-bfrlist y)))
            :hints(("Goal" :in-theory (enable fgl-objectlist-bfrlist append))))

   (defthm member-nthcdr
            (implies (not (member v x))
                     (not (member v (nthcdr n x)))))



   (defthm member-fgl-objectlist-bfrlist-of-nthcdr
            (implies (not (member v (fgl-objectlist-bfrlist x)))
                     (not (member v (fgl-objectlist-bfrlist (nthcdr n x)))))
            :hints(("Goal" :in-theory (enable nthcdr))))

   (defthm major-stack-bfrlist-of-stack$a-pop-scratch
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (major-stack-bfrlist (stack$a-pop-scratch stack)))))
      :hints(("Goal" :in-theory (enable stack$a-pop-scratch
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist)
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-set-bindings
      (implies (and (not (member v (major-stack-bfrlist stack)))
                    (not (member v (fgl-object-bindings-bfrlist bindings))))
               (not (member v (major-stack-bfrlist (stack$a-set-bindings bindings stack)))))
      :hints(("Goal" :in-theory (enable stack$a-set-bindings
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist)
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-set-minor-bindings
      (implies (and (not (member v (major-stack-bfrlist stack)))
                    (not (member v (fgl-object-bindings-bfrlist bindings))))
               (not (member v (major-stack-bfrlist (stack$a-set-minor-bindings bindings stack)))))
      :hints(("Goal" :in-theory (enable stack$a-set-minor-bindings
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist)
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-add-minor-bindings
      (set-equiv (major-stack-bfrlist (stack$a-add-minor-bindings bindings stack))
                 (append (fgl-object-bindings-bfrlist bindings)
                         (major-stack-bfrlist stack)))
      :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist)
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-push-frame
      (equal (major-stack-bfrlist (stack$a-push-frame stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-push-frame
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist)
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-push-minor-frame
      (equal (major-stack-bfrlist (stack$a-push-minor-frame stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-push-minor-frame
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist)
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-pop-frame
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (major-stack-bfrlist (stack$a-pop-frame stack)))))
      :hints(("Goal" :in-theory (enable stack$a-pop-frame
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist
                                        default-car)
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-pop-minor-frame
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (major-stack-bfrlist (stack$a-pop-minor-frame stack)))))
      :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist
                                        minor-stack-bfrlist
                                        default-car)
              :do-not-induct t)))

   (defthm fgl-object-bindings-bfrlist-of-stack$a-bindings
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (fgl-object-bindings-bfrlist (stack$a-bindings stack)))))
      :hints(("Goal" :in-theory (enable stack$a-bindings
                                        major-frame-bfrlist)
              :expand ((major-stack-bfrlist stack))
              :do-not-induct t)))

   (defthm fgl-object-bindings-bfrlist-of-stack$a-minor-bindings
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (fgl-object-bindings-bfrlist (stack$a-minor-bindings stack)))))
      :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-stack-bfrlist
                                        minor-frame-bfrlist)
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))


   (defthm scratchobj->bfrlist-of-stack$a-top-scratch
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (scratchobj->bfrlist (stack$a-top-scratch stack)))))
      :hints(("Goal" :in-theory (enable stack$a-top-scratch
                                        major-frame-bfrlist
                                        minor-frame-bfrlist)
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))

   (defthm scratchobj-bfrlist-of-minor-stack-nth-scratch
     (implies (not (member v (minor-stack-bfrlist stack)))
              (not (member v (scratchobj->bfrlist (minor-stack-nth-scratch n stack)))))
     :hints(("Goal" :in-theory (enable minor-stack-nth-scratch
                                       minor-stack-bfrlist
                                       minor-frame-bfrlist))))

   (defthm scratchobj-bfrlist-of-major-stack-nth-scratch
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (scratchobj->bfrlist (major-stack-nth-scratch n stack)))))
     :hints(("Goal" :in-theory (enable major-stack-nth-scratch
                                       major-stack-bfrlist
                                       major-frame-bfrlist))))

   (defthm scratchobj->bfrlist-of-stack$a-nth-scratch
      (implies (not (member v (major-stack-bfrlist stack)))
               (not (member v (scratchobj->bfrlist (stack$a-nth-scratch n stack)))))
      :hints(("Goal" :in-theory (enable stack$a-nth-scratch
                                        major-frame-bfrlist
                                        minor-frame-bfrlist)
              :expand ((major-stack-bfrlist stack)
                       (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))



   (defthm major-stack-bfrlist-of-stack$a-set-rule
      (equal (major-stack-bfrlist (stack$a-set-rule obj stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-set-rule
                                        major-stack-bfrlist
                                        major-frame-bfrlist))))

   (defthm major-stack-bfrlist-of-stack$a-set-phase
      (equal (major-stack-bfrlist (stack$a-set-phase obj stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-set-phase
                                        major-stack-bfrlist
                                        major-frame-bfrlist))))

   (defthm major-stack-bfrlist-of-stack$a-set-term
      (equal (major-stack-bfrlist (stack$a-set-term obj stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-set-term
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist)
              :expand ((minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-set-term-index
      (equal (major-stack-bfrlist (stack$a-set-term-index obj stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-set-term-index
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist)
              :expand ((minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t)))

   (defthm major-stack-bfrlist-of-stack$a-add-binding
      (implies (and (not (member v (major-stack-bfrlist stack)))
                    (not (member v (fgl-object-bfrlist obj))))
               (not (member v (major-stack-bfrlist (stack$a-add-binding var obj stack)))))
      :hints(("Goal" :in-theory (enable stack$a-add-binding
                                        major-stack-bfrlist
                                        major-frame-bfrlist))))


   (defthm bfr-listp-of-fgl-objectlist-bfrlist-cdr
            (implies (bfr-listp (fgl-objectlist-bfrlist x))
                     (bfr-listp (fgl-objectlist-bfrlist (cdr x))))
            :hints(("Goal" :in-theory (enable fgl-objectlist-bfrlist))))

   (defthm bfr-listp-of-fgl-objectlist-bfrlist-nthcdr
            (implies (bfr-listp (fgl-objectlist-bfrlist x))
                     (bfr-listp (fgl-objectlist-bfrlist (nthcdr n x))))
            :hints(("Goal" :in-theory (enable nthcdr))))

   (defthm bfr-listp-of-fgl-object-bfrlist-car
            (implies (bfr-listp (fgl-objectlist-bfrlist x))
                     (bfr-listp (fgl-object-bfrlist (car x))))
            :hints(("Goal" :expand ((fgl-objectlist-bfrlist x))
                    :in-theory (enable default-car))))

   (defthm bfr-listp-of-fgl-objectlist-bfrlist-take
            (implies (bfr-listp (fgl-objectlist-bfrlist x))
                     (bfr-listp (fgl-objectlist-bfrlist (take n x))))
            :hints(("Goal" :in-theory (enable take))))

   (defthm fgl-objectlist-bfrlist-of-rev
            (set-equiv (fgl-objectlist-bfrlist (rev x))
                       (fgl-objectlist-bfrlist x))
            :hints(("Goal" :in-theory (enable rev fgl-objectlist-bfrlist))))

   (defthm bfr-listp-of-constraint-instancelist-bfrlist-cdr
            (implies (bfr-listp (constraint-instancelist-bfrlist x))
                     (bfr-listp (constraint-instancelist-bfrlist (cdr x))))
            :hints(("Goal" :expand ((constraint-instancelist-bfrlist x))
                    :in-theory (enable default-cdr))))

   (defthm bfr-listp-of-constraint-instancelist-bfrlist-car
            (implies (bfr-listp (constraint-instancelist-bfrlist x))
                     (bfr-listp (constraint-instance-bfrlist (car x))))
            :hints(("Goal" :expand ((constraint-instancelist-bfrlist x))
                    :in-theory (enable default-car))))

   (defthm fgl-object-bindings-bfrlist-of-constraint-instance->subst
            (equal (fgl-object-bindings-bfrlist (constraint-instance->subst x))
                   (constraint-instance-bfrlist x))
            :hints(("Goal" :expand ((constraint-instance-bfrlist x)))))

   (defthm bfr-p-car-of-bfr-list
            (implies (bfr-listp x)
                     (bfr-p (car x)))
            :hints(("Goal" :in-theory (enable default-car bfr-listp))))


   ;; (local (in-theory (disable bfr-listp-of-fgl-objectlist-bfrlist
   ;;                            bfr-listp-of-fgl-object-bfrlist)))

   (defthm update-interp-st->stack-of-update-interp-st->stack
     (equal (update-interp-st->stack x (update-interp-st->stack x1 interp-st))
            (update-interp-st->stack x interp-st))
     :hints(("Goal" :in-theory (enable update-interp-st->stack))))

   (in-theory (enable bfr-listp-when-not-member-witness))

   (defthm bfr-p-of-g-boolean->bool-when-bfr-listp
     (implies (and (fgl-object-case x :g-boolean)
                   (bfr-listp (fgl-object-bfrlist x)))
              (b* (((g-boolean x)))
                (bfr-p x.bool)))
     :hints(("Goal" :in-theory (enable fgl-object-bfrlist))))




   (defthm bfr-p-of-bool-fix
     (bfr-p (bool-fix x))
     :hints(("Goal" :in-theory (enable bfr-p aig-p acl2::ubddp ubddp max-depth))))


   (in-theory (disable member-equal))



   (encapsulate nil
     (local (defthm pseudo-var-listp-when-nonnil-symbol-listp
              (implies (and (symbol-listp x)
                            (not (member nil x)))
                       (pseudo-var-list-p x))
              :hints(("Goal" :in-theory (enable member)))))

     (defthm pseudo-var-listp-of-fn-get-def-formals
       (pseudo-var-list-p (mv-nth 1 (acl2::fn-get-def fn state)))
       :hints(("Goal" :in-theory (enable acl2::fn-get-def)))))

   (defthm fgl-object-bindings-bfrlist-of-pairlis$
     (implies (and (pseudo-var-list-p vars)
                   (equal (len vars) (len vals)))
              (equal (fgl-object-bindings-bfrlist (pairlis$ vars vals))
                     (fgl-objectlist-bfrlist vals)))
     :hints(("Goal" :in-theory (enable fgl-objectlist-bfrlist fgl-object-bindings-bfrlist pairlis$
                                       pseudo-var-list-p len))))


   (defcong major-stack-scratch-isomorphic
     scratchobj-isomorphic
     (stack$a-top-scratch stack) 1
     :hints(("Goal" :in-theory (enable stack$a-top-scratch))))

   (local (defun nth-scratch-iso-ind (n x y)
            (if (zp n)
                (list x y)
              (nth-scratch-iso-ind (1- n) (cdr x) (cdr y)))))

   (defcong scratchlist-isomorphic scratchobj-isomorphic (nth n scratch) 2
     :hints (("goal" :induct (nth-scratch-iso-ind n scratch scratch-equiv)
              :expand ((scratchlist-isomorphic scratch scratch-equiv)))))

   (local (defun minor-stack-nth-scratch-iso-ind (n stack stack-equiv)
            (declare (xargs :measure (len stack)))
            (if (< (nfix n) (len (minor-frame->scratch (car stack))))
                stack-equiv
              (and (consp (cdr stack))
                   (minor-stack-nth-scratch-iso-ind
                    (- (nfix n) (len (minor-frame->scratch (car stack))))
                    (cdr stack) (cdr stack-equiv))))))

   (defcong minor-stack-scratch-isomorphic
     scratchobj-isomorphic
     (minor-stack-nth-scratch n stack) 2
     :hints(("Goal" :in-theory (enable minor-stack-nth-scratch
                                       minor-stack-scratch-isomorphic
                                       minor-frame-scratch-isomorphic)
             :induct (minor-stack-nth-scratch-iso-ind n stack stack-equiv)
             :expand ((:free (stack) (minor-stack-nth-scratch n stack))
                      (minor-stack-scratch-isomorphic stack stack-equiv)))))

   (defcong minor-stack-scratch-isomorphic
     equal
     (minor-stack-scratch-len stack) 1
     :hints(("Goal" :in-theory (enable minor-stack-scratch-len
                                       minor-stack-scratch-isomorphic))))

   (local (defun major-stack-nth-scratch-iso-ind (n stack stack-equiv)
            (declare (xargs :measure (len stack)))
            (if (< (nfix n) (minor-stack-scratch-len (major-frame->minor-stack (car stack))))
                stack-equiv
              (and (consp (cdr stack))
                   (major-stack-nth-scratch-iso-ind
                    (- (nfix n) (minor-stack-scratch-len (major-frame->minor-stack (car stack))))
                    (cdr stack) (cdr stack-equiv))))))

   (defcong major-stack-scratch-isomorphic
     scratchobj-isomorphic
     (major-stack-nth-scratch n stack) 2
     :hints(("Goal" :in-theory (enable major-stack-nth-scratch
                                       major-stack-scratch-isomorphic
                                       major-frame-scratch-isomorphic)
             :induct (major-stack-nth-scratch-iso-ind n stack stack-equiv)
             :expand ((:free (stack) (major-stack-nth-scratch n stack))
                      (major-stack-scratch-isomorphic stack stack-equiv)))))

   (defcong major-stack-scratch-isomorphic
     equal
     (major-stack-scratch-len stack) 1
     :hints(("Goal" :in-theory (enable major-stack-scratch-len
                                       major-stack-scratch-isomorphic))))

   (defcong major-stack-scratch-isomorphic
     scratchobj-isomorphic
     (major-stack-nth-scratch n stack) 2
     :hints(("Goal" :in-theory (enable major-stack-nth-scratch))))

   (defcong major-stack-scratch-isomorphic
     scratchobj-isomorphic
     (stack$a-nth-scratch n stack) 2
     :hints(("Goal" :in-theory (enable stack$a-nth-scratch))))

   (defcong major-stack-scratch-isomorphic
     equal
     (stack$a-full-scratch-len stack) 1
     :hints(("Goal" :in-theory (enable stack$a-full-scratch-len))))

   (defthm stack$a-top-scratch-of-stack$a-push-scratch
     (equal (stack$a-top-scratch (stack$a-push-scratch obj stack))
            (scratchobj-fix obj))
     :hints(("Goal" :in-theory (enable stack$a-push-scratch stack$a-top-scratch))))

   (defthm bfr-p-of-scratchobj-bfr->val
            (implies (double-rewrite (scratchobj-case x :bfr))
                     (equal (bfr-p (scratchobj-bfr->val x))
                            (bfr-listp (scratchobj->bfrlist x))))
            :hints(("Goal" :in-theory (enable scratchobj->bfrlist))))


   (encapsulate nil

      (local (include-book "scratchobj"))

      (make-event
       (cons 'progn
             (acl2::template-proj
              '(defthm bfrlist-of-scratchobj-<kind>->val-double-rewrite
                 (implies (double-rewrite (scratchobj-case x :<kind>))
                          (equal (<prefix>-bfrlist (scratchobj-<kind>->val x))
                                 (scratchobj->bfrlist x))))
              (scratchobj-tmplsubsts (acl2::remove-assoc
                                      :bfr (acl2::remove-assoc :bfrlist *scratchobj-types*)))))))




   (defcong interp-st-scratch-isomorphic interp-st-scratch-isomorphic
     (update-interp-st->reclimit reclimit interp-st) 2
     :hints(("Goal" :in-theory (enable interp-st-scratch-isomorphic))))

   (Defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic
     (stack$a-push-scratch obj stack) 2
     :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

   (Defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic
     (stack$a-pop-scratch stack) 1
     :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

   ))


(local
 (defsection scratch-isomorphic-lemmas

   (defthm alistp-when-fgl-object-bindings-p-rw
     (implies (fgl-object-bindings-p x)
              (alistp x))
     :hints(("Goal" :in-theory (enable fgl-object-bindings-p))))


   (Defthm stack$a-scratch-len-of-set-term
     (equal (stack$a-scratch-len (stack$a-set-term obj stack))
            (stack$a-scratch-len stack))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-set-term))))

   (Defthm stack$a-scratch-len-of-set-term-index
     (equal (stack$a-scratch-len (stack$a-set-term-index obj stack))
            (stack$a-scratch-len stack))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-set-term-index))))

   (Defthm stack$a-scratch-len-of-set-minor-bindings
     (equal (stack$a-scratch-len (stack$a-set-minor-bindings obj stack))
            (stack$a-scratch-len stack))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-set-minor-bindings))))

   (Defthm stack$a-scratch-len-of-push-minor-frame
     (equal (stack$a-scratch-len (stack$a-push-minor-frame stack))
            0)
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-push-minor-frame))))

   (defcong major-stack-scratch-isomorphic equal (stack$a-scratch-len x) 1
     :hints(("Goal" :in-theory (enable stack$a-scratch-len))))

   (defcong major-stack-scratch-isomorphic equal (stack$a-minor-frames x) 1
     :hints(("Goal" :in-theory (e/d (stack$a-minor-frames pos-fix)
                                    (minor-stack-scratch-isomorphic-implies-pos-equiv-len-1))
             :use ((:instance minor-stack-scratch-isomorphic-implies-pos-equiv-len-1
                    (x (major-frame->minor-stack (car x)))
                    (x-equiv (major-frame->minor-stack (car x-equiv))))))))

   (defcong major-stack-scratch-isomorphic equal (stack$a-frames x) 1
     :hints(("Goal" :in-theory (e/d (stack$a-frames pos-fix)
                                    (major-stack-scratch-isomorphic-implies-pos-equiv-len-1))
             :use ((:instance major-stack-scratch-isomorphic-implies-pos-equiv-len-1)))))

   (Defthm stack$a-minor-frames-of-set-term
     (equal (stack$a-minor-frames (stack$a-set-term obj stack))
            (stack$a-minor-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-set-term
                                       len))))

   (Defthm stack$a-minor-frames-of-set-term-index
     (equal (stack$a-minor-frames (stack$a-set-term-index obj stack))
            (stack$a-minor-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-set-term-index
                                       len))))

   (Defthm stack$a-minor-frames-of-set-minor-bindings
     (equal (stack$a-minor-frames (stack$a-set-minor-bindings obj stack))
            (stack$a-minor-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-set-minor-bindings
                                       len))))

   (Defthm stack$a-minor-frames-of-push-minor-frame
     (equal (stack$a-minor-frames (stack$a-push-minor-frame stack))
            (+ 1 (stack$a-minor-frames stack)))
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-push-minor-frame))))


   (defthm pathcond-rewind-ok-by-stack-len
     (implies (and (equal stack-len (pathcond-rewind-stack-len bfr-mode pathcond))
                   (bind-free (case-match stack-len
                                (('maybe-incr cond x) `((cond . ,cond) (x . ,x)))))
                   (equal stack-len (maybe-incr cond x))
                   (iff* cond (nth *pathcond-enabledp* pathcond)))
              (pathcond-rewind-ok bfr-mode pathcond))
     :hints(("Goal" :in-theory (enable pathcond-rewind-ok maybe-incr))))

   (defthm fgl-object-bindings-p-of-pairlis$
     (implies (and (fgl-objectlist-p vals)
                   (pseudo-var-list-p vars)
                   (equal (len vars) (len vals)))
              (fgl-object-bindings-p (pairlis$ vars vals)))
     :hints(("Goal" :in-theory (enable pairlis$ fgl-object-bindings-p))))



   (Defthm stack$a-scratch-len-of-push-scratch
     (equal (stack$a-scratch-len (stack$a-push-scratch obj stack))
            (+ 1 (stack$a-scratch-len stack)))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-push-scratch))))

   (Defthm stack$a-full-scratch-len-of-push-scratch
     (equal (stack$a-full-scratch-len (stack$a-push-scratch obj stack))
            (+ 1 (stack$a-full-scratch-len stack)))
     :hints(("Goal" :in-theory (enable stack$a-full-scratch-len
                                       stack$a-push-scratch
                                       major-stack-scratch-len
                                       minor-stack-scratch-len))))

   (Defthm stack$a-scratch-len-of-pop-scratch
     (equal (stack$a-scratch-len (stack$a-pop-scratch stack))
            (nfix (+ -1 (stack$a-scratch-len stack))))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-pop-scratch len))))

   (Defthm stack$a-scratch-len-of-update-scratch
     (implies (< (nfix n) (stack$a-scratch-len stack))
              (equal (stack$a-scratch-len (stack$a-update-scratch n obj stack))
                     (stack$a-scratch-len stack)))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-update-scratch len))))

   (Defthm stack$a-frames-of-push-frame
     (equal (stack$a-frames (stack$a-push-frame stack))
            (+ 1 (stack$a-frames stack)))
     :hints(("Goal" :in-theory (enable stack$a-frames
                                       stack$a-push-frame))))

   (Defthm stack$a-minor-frames-of-push-frame
     (equal (stack$a-minor-frames (stack$a-push-frame stack))
            1)
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-push-frame))))

   (Defthm stack$a-minor-frames-of-set-rule
     (equal (stack$a-minor-frames (stack$a-set-rule obj stack))
            (stack$a-minor-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-set-rule))))

   (Defthm stack$a-frames-of-set-rule
     (equal (stack$a-frames (stack$a-set-rule obj stack))
            (stack$a-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-frames
                                       stack$a-set-rule len))))

   (Defthm stack$a-minor-frames-of-set-phase
     (equal (stack$a-minor-frames (stack$a-set-phase obj stack))
            (stack$a-minor-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                       stack$a-set-phase))))

   (Defthm stack$a-frames-of-set-phase
     (equal (stack$a-frames (stack$a-set-phase obj stack))
            (stack$a-frames stack))
     :hints(("Goal" :in-theory (enable stack$a-frames
                                       stack$a-set-phase len))))

   (Defthm stack$a-scratch-len-of-set-rule
     (equal (stack$a-scratch-len (stack$a-set-rule obj stack))
            (stack$a-scratch-len stack))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-set-rule))))


   (Defthm stack$a-scratch-len-of-set-phase
     (equal (stack$a-scratch-len (stack$a-set-phase obj stack))
            (stack$a-scratch-len stack))
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-set-phase))))

   (Defthm stack$a-scratch-len-of-push-frame
     (equal (stack$a-scratch-len (stack$a-push-frame stack))
            0)
     :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                       stack$a-push-frame))))

   (defcong scratchobj-isomorphic major-stack-scratch-isomorphic (stack$a-push-scratch obj stack) 1
     :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

   ))


(make-event
 `(define fgl-rewrite-try-primitive ((rule fgl-rule-p)
                                     (fn pseudo-fnsym-p)
                                     (args fgl-objectlist-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
    :guard (and (fgl-rule-case rule :primitive)
                (interp-st-bfr-listp (fgl-objectlist-bfrlist args)))
    :returns (mv successp
                 (ans fgl-object-p)
                 new-interp-st new-state)
    :prepwork ((local (in-theory (enable bfr-listp-when-not-member-witness))))
    (b* ((interp-st (interp-st-prof-push (fgl-rule->rune rule) interp-st))
         (rule (fgl-rule-fix rule))
         (tracep (fgl-rewrite-do-trace? rule fn args interp-st state))
         (interp-st (fgl-rewrite-trace-start tracep rule fn args interp-st state))
         ((fgl-interp-value successp ans)
          (fgl-primitive-fncall-stub (fgl-rule-primitive->name rule) fn args interp-st state))
         (interp-st (fgl-rewrite-trace-finish tracep successp ans rule fn args interp-st state))
         (interp-st (interp-st-prof-pop-increment successp interp-st)))
      (fgl-interp-value successp ans))
    ///
    (local (acl2::use-trivial-ancestors-check))
    ,@*fgl-primitive-rule-thms*
    (defret eval-of-<fn>
      (implies (and successp
                    (equal contexts (interp-st->equiv-contexts interp-st))
                    (fgl-ev-meta-extract-global-facts :state st)
                    ;; (,name-formula-checks st)
                    (fgl-formula-checks-stub st)
                    (equal (w st) (w state))
                    (interp-st-bfrs-ok interp-st)
                    (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                    (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                            (interp-st->constraint interp-st)
                                            (interp-st->logicman interp-st))
                    (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                            (interp-st->pathcond interp-st)
                                            (interp-st->logicman interp-st)))
               (equal (fgl-ev-context-fix contexts
                                          (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
                      (fgl-ev-context-fix contexts
                                          (fgl-object-eval (g-apply fn args) env (interp-st->logicman interp-st))))))

    (defret return-values-correct-of-<fn>
      (equal (list . <values>)
             <call>))))

(defines fgl-minor-frame-subterm-count
  :ruler-extenders :all
  (define fgl-minor-frame-subterm-count ((x pseudo-termp))
    :measure (pseudo-term-count x)
    (+ 1
       (pseudo-term-case x
         :const 0
         :var 0
         :lambda 0
         :fncall
         (fgl-minor-frame-subtermlist-count x.args))))
  (define fgl-minor-frame-subtermlist-count ((x pseudo-term-listp))
    :measure (pseudo-term-list-count x)
    (if (atom x)
        0
      (+ (fgl-minor-frame-subterm-count (car x))
         (fgl-minor-frame-subtermlist-count (cdr x))))))

(define interp-st-term-index (interp-st)
  :enabled t :hooks nil :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (idx)
             (stack-term-index stack)
             idx))

(define term-index-incr ((n posp) (term-index acl2::maybe-natp))
  :inline t
  :returns (new-index natp :rule-classes :type-prescription)
  (+ (lposfix n) (or (acl2::maybe-natp-fix term-index) -1)))

(define interp-st-incr-term-index ((n posp) interp-st)
  :enabled t :hooks nil :inline t
  ;; Note: this increments by a positive value, starting from a default value
  ;; (when nil) of -1.  This is so that we can increment every time we enter
  ;; the term interpreter, but have the first term correspond to index 0.
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-term-index (term-index-incr n (stack-term-index stack)) stack)
             interp-st))

(define interp-st-incr-phase (interp-st)
  :enabled t :hooks nil :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-phase (+ 1 (or (stack-phase stack) 0)) stack)
             interp-st))

(define interp-st-phase (interp-st)
  :enabled t :hooks nil :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (phase)
             (stack-phase stack)
             phase))


(define interp-st-push-rule-frame ((rule fgl-generic-rule-p)
                                   (bindings fgl-object-bindings-p)
                                   interp-st)
  :enabled t
  :guard-hints (("goal" :in-theory (enable stack$a-set-phase
                                           stack$a-set-rule
                                           stack$a-set-bindings
                                           stack$a-push-frame)))
  ;; (mbe :logic (non-exec (update-interp-st->stack
  ;;                        (cons (make-major-frame :rule (fgl-generic-rule-fix rule)
  ;;                                                :bindings bindings
  ;;                                                :phase 0)
  ;;                              (major-stack-fix (interp-st->stack interp-st)))
  ;;                        interp-st))
  ;;      :exec
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((stack (stack-push-frame stack))
                  (stack (stack-set-bindings bindings stack))
                  (stack (stack-set-rule (fgl-generic-rule-fix rule) stack)))
               (stack-set-phase 0 stack))
             interp-st))


(define interp-st-boolean-fncall-p ((x fgl-object-p) interp-st w)
  (declare (ignorable interp-st w))
  (fgl-object-case x
    :g-apply (or (eq x.fn 'intcar)
                 (eq x.fn 'equal)
                 (eq x.fn 'consp)
                 (eq x.fn 'integerp)
                 (eq x.fn '<))
    :otherwise nil)
  ///
  (defthmd interp-st-boolean-fncall-p-correct
    (implies (and (interp-st-boolean-fncall-p x interp-st w)
                  (fgl-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (booleanp (fgl-object-eval x env)))
    :hints(("Goal" :in-theory (enable fgl-apply)))))

(define fgl-var-lookup ((varname pseudo-var-p) interp-st)
  :enabled t
  (b* ((varname (pseudo-var-fix varname)))
    (or (assoc-eq varname (interp-st-bindings interp-st))
        (assoc-eq varname (interp-st-minor-bindings interp-st)))))

(define fgl-free-var-p ((arg pseudo-termp) interp-st)
  (b* (((unless (pseudo-term-case arg :var)) nil)
       (varname (pseudo-term-var->name arg)))
    (not (fgl-var-lookup varname interp-st)))
  ///
  (defthm pseudo-term-kind-when-free-var
    (implies (fgl-free-var-p arg interp-st)
             (equal (pseudo-term-kind arg) :var))
    :rule-classes :forward-chaining))

(define fgl-binder-args-p ((args pseudo-term-listp)
                           interp-st)
  (and (consp args)
       (fgl-free-var-p (car args) interp-st)))


(local (defthm fgl-equivp-correct-for-fgl-ev
         (implies (and (fgl-ev-meta-extract-global-facts)
                       (fgl-equivp fn (w state)))
                  (fgl-ev (cmr::equiv-rel-term fn) a))
         :hints (("goal" :use ((:functional-instance fgl-equivp-correct
                                (rules-ev fgl-ev)
                                (rules-ev-list fgl-ev-list)
                                (rules-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
                                (rules-ev-good-fgl-binder-rules-p fgl-good-fgl-binder-rules-p)
                                (rules-ev-good-fgl-binder-rule-p fgl-good-fgl-binder-rule-p)
                                (rules-ev-falsify fgl-ev-falsify)))))))

(local (defthmd fgl-equivp-correct1-for-fgl-ev
         (implies (and (fgl-ev-meta-extract-global-facts)
                       (fgl-equivp fn (w state))
                       (pseudo-fnsym-p fn))
                  (and (fgl-ev (list fn x x) a)
                       (implies (fgl-ev (list fn x y) a)
                                (fgl-ev (list fn y x) a))
                       (implies (and (fgl-ev (list fn x y) a)
                                     (fgl-ev (list fn y z) a))
                                (fgl-ev (list fn x z) a))))
         :hints (("goal" :use ((:functional-instance fgl-equivp-correct1
                                (rules-ev fgl-ev)
                                (rules-ev-list fgl-ev-list)
                                (rules-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
                                (rules-ev-good-fgl-binder-rules-p fgl-good-fgl-binder-rules-p)
                                (rules-ev-good-fgl-binder-rule-p fgl-good-fgl-binder-rule-p)
                                (rules-ev-falsify fgl-ev-falsify)))))))


(acl2::def-universal-equiv fgl-ev-equiv
  :qvars (env)
  :equiv-terms ((equal (fgl-ev x env))))

(defrefinement pseudo-term-equiv fgl-ev-equiv
  :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

(defcong fgl-ev-equiv equal (fgl-ev x env) 1
  :hints(("Goal" :in-theory (enable fgl-ev-equiv-necc))))


(acl2::def-universal-equiv fgl-ev-iff-equiv
  :qvars (env)
  :equiv-terms ((iff (fgl-ev x env))))

(defrefinement fgl-ev-equiv fgl-ev-iff-equiv
  :hints(("Goal" :in-theory (enable fgl-ev-iff-equiv))))

(defcong fgl-ev-equiv iff (fgl-ev x env) 1
  :hints(("Goal" :in-theory (enable fgl-ev-equiv-necc))))


(define check-equivbind-hyp ((hyp pseudo-termp) interp-st state)
  :returns (mv (var (iff (pseudo-var-p var) var))
               (term pseudo-termp)
               (equiv pseudo-fnsym-p)
               ;; amount to increment the term index before interpreting the term
               (incr posp :rule-classes :type-prescription))
  (pseudo-term-case hyp
    :fncall (b* (((unless (eql (len hyp.args) 2))
                  (mv nil nil nil 1))
                 ((mv var term incr)
                  (cond ((fgl-free-var-p (first hyp.args) interp-st)
                         (mv (pseudo-term-var->name (first hyp.args))
                             (second hyp.args)
                             2))
                        ((fgl-free-var-p (second hyp.args) interp-st)
                         (mv (pseudo-term-var->name (second hyp.args))
                             (first hyp.args)
                             1))
                        (t (mv nil nil 1))))
                 ((unless var)
                  (mv nil nil nil 1))
                 ;; The expensive part, presumably, except for equal/iff/unequiv
                 ((unless (fgl-equivp hyp.fn (w state)))
                  (mv nil nil nil 1)))
              (mv var term hyp.fn incr))
    :otherwise (mv nil nil nil 1))
  ///
  (defret check-equivbind-hyp-is-an-equivalence
    (implies (and var
                  (fgl-ev-meta-extract-global-facts))
             (fgl-ev (cmr::equiv-rel-term equiv) a)))

  (defret check-equivbind-hyp-fgl-equivp
    (implies (and var
                  (fgl-ev-meta-extract-global-facts))
             (fgl-equivp equiv (w state))))

  (defret check-equivbind-hyp-correct-lemma
    (implies (and var
                  (fgl-ev-meta-extract-global-facts))
             (iff (fgl-ev (list equiv
                                (pseudo-term-quote (cdr (hons-assoc-equal var env)))
                                (pseudo-term-quote (fgl-ev term env)))
                          nil)
                  (fgl-ev hyp env)))
    :hints(("Goal" :in-theory (enable fgl-ev-of-fncall-args
                                      fgl-equivp-correct1-for-fgl-ev))))

  (local (defthmd fgl-ev-when-theoremp
           (implies (fgl-ev-theoremp x)
                    (fgl-ev x a))
           :hints (("goal" :use fgl-ev-falsify))))

  (local (defthmd fgl-ev-when-global-facts
           (implies (fgl-ev-meta-extract-global-facts)
                    (fgl-ev-theoremp
                     (meta-extract-global-fact+ obj st state)))
           :hints (("goal" :use ((:instance fgl-ev-meta-extract-global-badguy
                                  (obj obj) (st st)))))))

  (local
     (defthm fgl-ev-meta-extract-global-facts-when-world-equiv
       (implies (and (equal (w new) (w old))
                     (fgl-ev-meta-extract-global-facts :state old))
                (fgl-ev-meta-extract-global-facts :state new))
       :hints (("goal" :use ((:instance
                              (:functional-instance
                               cmr::base-ev-meta-extract-global-facts-when-world-equiv
                               (cmr::base-ev fgl-ev)
                               (cmr::base-ev-list fgl-ev-list)
                               (cmr::base-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
                               (cmr::base-ev-falsify fgl-ev-falsify))
                              (old old) (new new)))
                :in-theory (enable fgl-ev-when-theoremp
                                   fgl-ev-of-nonsymbol-atom
                                   fgl-ev-of-bad-fncall
                                   fgl-ev-of-fncall-args
                                   fgl-ev-when-global-facts)))))


  ;; (defthmd check-equivbind-hyp-correct
  ;;   (b* (((mv var term equiv) (check-equivbind-hyp hyp ist st)))
  ;;     (implies (and (acl2::rewriting-negative-literal `(mv-nth '0 (check-equivbind-hyp ,hyp ,ist ,st)))
  ;;                   (fgl-ev-meta-extract-global-facts :state state)
  ;;                   (equal (w st) (w state)))
  ;;              (iff var
  ;;                   (and (hide var)
  ;;                        (fgl-ev-iff-equiv hyp
  ;;                                          (list equiv (pseudo-term-var var) term))))))
  ;;   :hints(("Goal" :in-theory (e/d (fgl-ev-iff-equiv
  ;;                                   fgl-ev-of-fncall-args)
  ;;                                  (check-equivbind-hyp))
  ;;           :expand ((:free (x) (hide x))))))

  (defthm check-equivbind-hyp-correct
    (b* (((mv var term equiv) (check-equivbind-hyp hyp ist st)))
      (implies (and var
                    (fgl-ev-meta-extract-global-facts :state state)
                    (equal (w st) (w state)))
               (equal (fgl-ev-iff-equiv hyp
                                        (list equiv (pseudo-term-var var) term))
                      t)))
    :hints(("Goal" :in-theory (e/d (fgl-ev-iff-equiv
                                    fgl-ev-of-fncall-args)
                                   (check-equivbind-hyp)))))

  ;; (defret check-equivbind-hyp-fgl-equivp-w-st
  ;;   (implies (and var
  ;;                 (fgl-ev-meta-extract-global-facts :state st)
  ;;                 (equal (w st) (w state))
  ;;                 (equal wrld (w state)))
  ;;            (fgl-equivp equiv wrld)))

  (defret check-equivbind-hyp-fgl-ev-equiv-relation-p
    (implies (and var
                  (fgl-ev-meta-extract-global-facts :state st)
                  (equal (w st) (w state)))
             (fgl-ev (cmr::equiv-rel-term equiv) a))
    :hints(("Goal" :in-theory (e/d ()
                                   (check-equivbind-hyp))))))


(define equiv-contexts-from-equiv ((equiv pseudo-fnsym-p))
  :returns (contexts equiv-contextsp)
  (b* ((equiv (pseudo-fnsym-fix equiv)))
    (if (eq equiv 'equal)
        nil
      (list equiv))))




(progn
  (with-output
    :off (event prove)
    (defines fgl-interp
      :flag-local nil
      :flag-hints ((let ((fns (acl2::recursivep 'fgl-interp-test t world)))
                     `(:clause-processor
                       (cmr::resolve-flags-cp
                        clause ',(cons 'flag fns))
                       :in-theory (disable . ,fns))))
      (define fgl-interp-test ((x pseudo-termp)
                              (interp-st interp-st-bfrs-ok)
                              state)
        ;; Translate a term to a FGL object under the given alist substitution, preserving IFF.
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count x) 60)
        :well-founded-relation acl2::nat-list-<
        :verify-guards nil
        :measure-debug t
        ;; :guard (bfr-listp (fgl-object-bindings-bfrlist alist) (interp-st->bfrstate interp-st))
        :returns (mv xbfr
                     new-interp-st new-state)
        (b* (((interp-st-bind
               (equiv-contexts (fgl-interp-test-equiv-contexts (interp-st->equiv-contexts interp-st))))
              (was-fncall-p (pseudo-term-case x :call))
              ((fgl-interp-recursive-call xobj)
               (fgl-interp-term-equivs x interp-st state))))
          ;; already-rewritten: xobj has probably already been rewritten under
          ;; IFF if x was a function/lambda call, otherwise probably not.
          ;; E.g. if x was a variable, it was probably not bound in an IFF
          ;; context.
          (fgl-interp-simplify-if-test was-fncall-p xobj interp-st state)))

      (define fgl-interp-term-equivs ((x pseudo-termp)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020 (pseudo-term-binding-count x) 40)
        :returns (mv
                  (xobj fgl-object-p)
                  new-interp-st new-state)
        (b* (((fgl-interp-value xobj)
              (fgl-interp-term x interp-st state))
             ;; ((when err) (mv nil interp-st state))
             ((unless (fgl-term-obj-p xobj))
              (fgl-interp-value xobj))
             (contexts (interp-st->equiv-contexts interp-st)))
          (stobj-let ((pathcond (interp-st->pathcond interp-st))
                      (logicman (interp-st->logicman interp-st))
                      (bvar-db (interp-st->bvar-db interp-st)))
                     (error val pathcond)
                     (try-equivalences-loop
                      xobj contexts 100 ;; bozo, configure reclimit for try-equivalences-loop?
                      pathcond bvar-db logicman state)
                     (b* (((when error)
                           (fgl-interp-error
                            :msg (fgl-msg "Try-equivalences-loop failed: ~@0" error))))
                       (fgl-interp-value val)))))

      (define fgl-interp-term-top ((x pseudo-termp)
                                   (interp-st interp-st-bfrs-ok)
                                   state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count x) 80)
        :returns (mv
                  (xobj fgl-object-p)
                  new-interp-st new-state)
        (b* ((contexts (interp-st->equiv-contexts interp-st))
             ((when (member-eq 'iff contexts))
              (b* (((fgl-interp-value xbfr) (fgl-interp-test x interp-st state)))
                (fgl-interp-value (mk-g-boolean xbfr))))
             ((fgl-interp-recursive-call xobj)
              (fgl-interp-term-equivs x interp-st state))
             ((when (interp-st-boolean-fncall-p xobj interp-st (w state)))
              (b* (((fgl-interp-value xbfr) (fgl-interp-simplify-if-test nil xobj interp-st state)))
                (fgl-interp-value (mk-g-boolean xbfr)))))
          (fgl-interp-value xobj)))


      (define fgl-interp-term ((x pseudo-termp)
                              (interp-st interp-st-bfrs-ok)
                              state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count x) 20)
        :returns (mv
                  (xobj fgl-object-p)
                  new-interp-st new-state)
        ;; Note: this increment sets the term index to 0 if it was NIL before.
        (b* ((interp-st (interp-st-incr-term-index 1 interp-st)))
          (pseudo-term-case x
            :const (fgl-interp-value (g-concrete x.val))
            :var (b* ((minor-look (assoc-eq x.name (interp-st-minor-bindings interp-st)))
                      ((when minor-look)
                       (fgl-interp-value (cdr minor-look)))
                      (major-look (assoc-eq x.name (interp-st-bindings interp-st)))
                      ((unless major-look)
                       (fgl-interp-error
                        :msg (msg "Unbound variable: ~x0" x.name))))
                   (fgl-interp-value (cdr major-look)))
            :lambda
            (b* (((mv x-bindings body) (lambda-nest-to-bindinglist x))
                 (interp-st (interp-st-push-minor-frame interp-st))
                 (interp-st (interp-st-set-term x interp-st))
                 ;; We set the term index to 0 here so that it will then be
                 ;; incremented to 1.  This distinguishes this case, where the
                 ;; minor frame's term is a lambda and we are actually pointing
                 ;; into the corresponding bindinglist or body, from the other
                 ;; case, where we set the minor frame's term to a lambda
                 ;; corresponding to a hyp or rule RHS and then interpret that
                 ;; term directly.  In that other case the term-index will be
                 ;; unset so that it will start by being "incremented" to 0.
                 (interp-st (interp-st-set-term-index 0 interp-st))
                 ((interp-st-bind
                   (equiv-contexts (fgl-interp-lambda-arglist-equiv-contexts (interp-st->equiv-contexts interp-st))))
                  ((fgl-interp-recursive-call)
                   ;; replaces the top of stack with the bindings
                   (fgl-interp-bindinglist x-bindings interp-st state)))

                 ;; Note: Was interp-term-equivs
                 ((fgl-interp-value val)
                  (fgl-interp-term body interp-st state))
                 (interp-st (interp-st-pop-minor-frame interp-st)))
              (fgl-interp-value val))
            :fncall
            (b* (((fgl-interp-recursive-call successp ans)
                  (fgl-interp-fncall-special x.fn x.args interp-st state))
                 ((when successp)
                  (fgl-interp-value ans))
                 ((when (fgl-binder-args-p x.args interp-st))
                  (fgl-interp-binder x interp-st state))

                 (argcontexts (fgl-interp-arglist-equiv-contexts (interp-st->equiv-contexts interp-st)
                                                                 x.fn (len x.args) (w state)))

                 ((fgl-interp-recursive-call args)
                  (fgl-interp-arglist x.args argcontexts interp-st state))

                 ;; ((when err)
                 ;;  (mv nil interp-st state))
                 )
              (fgl-interp-fncall-casesplit x.fn args interp-st state)))))

      (define fgl-interp-fncall-special ((fn pseudo-fnsym-p)
                                        (args pseudo-term-listp)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-list-binding-count args) 100)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (fgl-interp-fncall-special-case
          (pseudo-fnsym-fix fn)
          ((if 3)
           (fgl-interp-if/or (first args)
                            (second args)
                            (third args)
                            interp-st state))
          ((return-last 3)
           (fgl-interp-return-last (first args)
                                  (second args)
                                  (third args)
                                  interp-st state))

          ;; ((bind-var 2)
          ;;  (fgl-interp-bind-var (first args) (second args) interp-st state))

          ((binder 1)
           (fgl-interp-binder (first args) interp-st state))

          ((abort-rewrite 1)
           (b* ((interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count (first args)) interp-st))
                (interp-st (interp-st-set-error :abort-rewrite interp-st)))
             (fgl-interp-value nil)))

          ;; ((fgl-sat-check 2)
          ;;  (fgl-interp-sat-check (first args)
          ;;                       (second args)
          ;;                       interp-st state))

          ((syntax-interp-fn 2)
           (b* ((interp-st (interp-st-incr-term-index (+ (fgl-minor-frame-subterm-count (first args))
                                                         (fgl-minor-frame-subterm-count (second args)))
                                                      interp-st)))
             (fgl-interp-syntax-interp (first args)
                                       (second args)
                                       interp-st state)))

          ((assume 2)
           (fgl-interp-assume (first args)
                             (second args)
                             interp-st state))

          ((narrow-equiv 2)
           (fgl-interp-narrow-equiv (first args)
                                   (second args)
                                   interp-st state))

          ((fgl-time-fn 2)
           (fgl-interp-time$ (first args)
                            (second args)
                            interp-st state))

          ;; ((fgl-prog2 2)
          ;;  (fgl-interp-prog2 (first args)
          ;;                   (second args)
          ;;                   interp-st state))

          ((fgl-interp-obj 1)
           (fgl-interp-fgl-interp-obj (first args)
                                     interp-st state))))

      (define fgl-interp-arglist ((args pseudo-term-listp)
                                  (argcontexts equiv-argcontexts-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-list-binding-count args) 20)
        :returns (mv
                  (arg-objs fgl-objectlist-p)
                  new-interp-st new-state)
        (b* (((when (atom args)) (fgl-interp-value nil))
             ((interp-st-bind
               (equiv-contexts (equiv-argcontexts-first argcontexts)))
              ((fgl-interp-recursive-call arg1)
               (fgl-interp-term-top (car args) interp-st state)))
             ;; ((when err) (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-fgl-obj arg1 interp-st))
             ((fgl-interp-value rest)
              (fgl-interp-arglist (cdr args) (equiv-argcontexts-rest argcontexts) interp-st state))
             ((mv arg interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
          (fgl-interp-value (cons arg rest))))

      (define fgl-interp-lambda-arglist ((args pseudo-term-listp)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-list-binding-count args) 20)
        :returns (mv
                  (arg-objs fgl-objectlist-p)
                  new-interp-st new-state)
        (b* (((when (atom args)) (fgl-interp-value nil))
             ((fgl-interp-recursive-call arg1)
              (fgl-interp-term-top (car args) interp-st state))
             ;; ((when err) (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-fgl-obj arg1 interp-st))
             ((fgl-interp-value rest)
              (fgl-interp-lambda-arglist (cdr args) interp-st state))
             ((mv arg interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
          (fgl-interp-value (cons arg rest))))

      (define fgl-interp-bindinglist ((bindings cmr::bindinglist-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (cmr::bindinglist-count bindings)
                       20)
        :returns (mv new-interp-st new-state)
        (b* (((when (atom bindings)) (fgl-interp-value))
             ((cmr::binding x1) (car bindings))
             ((fgl-interp-recursive-call args)
              (fgl-interp-lambda-arglist x1.args interp-st state))
             ;; ((when err) (mv interp-st state))
             (interp-st (interp-st-add-minor-bindings (pairlis$ x1.formals args) interp-st)))
          (fgl-interp-bindinglist (cdr bindings) interp-st state)))

      (define fgl-interp-fncall-casesplit ((fn pseudo-fnsym-p)
                                          (args fgl-objectlist-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)

        :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2010 0 12)
        :returns (mv (ans fgl-object-p)
                     new-interp-st new-state)
        (b* ((ite (fgl-objectlist-find-ite args))
             ((unless (and** ite
                             ;; bozo should this be another flag?
                             (interp-flags->branch-on-ifs (interp-st->flags interp-st))
                             (fgl-function-mode->split-ifs
                              (fgl-function-mode-lookup
                               fn (fgl-config->function-modes
                                   (interp-st->config interp-st))))))
              (fgl-interp-fncall fn args interp-st state))
             (test (g-ite->test ite))
             ((mv then-args else-args) (fgl-objectlist-split test args))
             (interp-st (interp-st-push-scratch-fgl-objlist else-args interp-st))
             (interp-st (interp-st-push-scratch-fgl-objlist then-args interp-st))
             ((fgl-interp-recursive-call testbfr)
              ;; already-rewritten: presumably since it already ended up as the
              ;; test of an IF.
              (fgl-interp-simplify-if-test t test interp-st state))
             ((mv then-args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))
             ((mv else-args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st)))
          (fgl-interp-fncall-casesplit-branches testbfr fn then-args else-args interp-st state)))

      (define fgl-interp-fncall-casesplit-branches ((testbfr interp-st-bfr-p)
                                                   (fn pseudo-fnsym-p)
                                                   (then-args fgl-objectlist-p)
                                                   (else-args fgl-objectlist-p)
                                                   (interp-st interp-st-bfrs-ok)
                                                   state)

        :guard (and (interp-st-bfr-listp (fgl-objectlist-bfrlist then-args))
                    (interp-st-bfr-listp (fgl-objectlist-bfrlist else-args)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2010 0 11)
        :returns (mv (ans fgl-object-p)
                     new-interp-st new-state)
        (b* ((interp-st (interp-st-push-scratch-fgl-objlist else-args interp-st))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((fgl-interp-recursive-call then-unreachable then-val)
              (fgl-maybe-interp-fncall-casesplit testbfr fn then-args interp-st state))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv else-args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))
             (interp-st (interp-st-push-scratch-fgl-obj then-val interp-st))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((fgl-interp-recursive-call else-unreachable else-val)
              (fgl-maybe-interp-fncall-casesplit (interp-st-bfr-not testbfr) fn else-args interp-st state))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv then-val interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
             ((when then-unreachable)
              (if else-unreachable
                  (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
                    (fgl-interp-value nil))
                (fgl-interp-value else-val)))
             ((when else-unreachable)
              (fgl-interp-value then-val)))
          (fgl-interp-merge-branches testbfr then-val else-val interp-st state)))


      (define fgl-maybe-interp-fncall-casesplit ((test interp-st-bfr-p)
                                                (fn pseudo-fnsym-p)
                                                (args fgl-objectlist-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
        :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2010 0 10)
        :returns (mv
                  unreachable
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* ((reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error
               :msg (fgl-msg "The recursion limit ran out.")
               :nvals 2))
             ((mv contra interp-st)
              (interp-st-pathcond-assume test interp-st))
             ((when contra)
              (fgl-interp-value t nil))
             ((when (interp-st->errmsg interp-st))
              (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                ;; We cancel an error below, so we need to ensure it's not one
                ;; that originated outside of this call.
                (fgl-interp-value nil nil)))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((fgl-interp-value ans)
               (fgl-interp-fncall-casesplit fn args interp-st state)))
             (interp-st (interp-st-pathcond-rewind interp-st))
             ((when (eq (interp-st->errmsg interp-st) :unreachable))
                (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
                  (fgl-interp-value t nil))))
          (fgl-interp-value nil ans)))


      (define fgl-interp-fncall ((fn pseudo-fnsym-p)
                                (args fgl-objectlist-p)
                                (interp-st interp-st-bfrs-ok)
                                state)
        :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       0 0 1)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* ((fn (pseudo-fnsym-fix fn))
             ((fgl-function-mode fn-mode)
              (fgl-function-mode-lookup fn (fgl-config->function-modes
                                           (interp-st->config interp-st))))
             ((mv successp ans)
              (fncall-try-concrete-eval fn args fn-mode.dont-concrete-exec state))
             ((when successp)
              (b* ((interp-st (interp-st-prof-simple-increment-exec fn interp-st)))
                (fgl-interp-value ans)))
             (interp-st (interp-st-push-scratch-fgl-objlist args interp-st))
             ((fgl-interp-value successp ans)
              (fgl-rewrite-fncall fn args fn-mode.dont-rewrite interp-st state))
             ((mv args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st)))
          (fgl-interp-value (if successp ans (g-apply fn args)))))



      (define fgl-rewrite-fncall ((fn pseudo-fnsym-p)
                                 (args fgl-objectlist-p)
                                 (dont)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 0 0 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* (((when dont)
              (fgl-interp-value nil nil))
             (reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.") :nvals 2))
             ((mv rules interp-st) (interp-st-function-rules fn interp-st state))
             ((unless rules)
              (fgl-interp-value nil nil))
             (interp-st (interp-st-push-scratch-fgl-objlist args interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((fgl-interp-value successp ans)
               (fgl-rewrite-try-rules rules fn interp-st state)))
             (interp-st (interp-st-pop-scratch interp-st)))
          (fgl-interp-value successp ans)))


      (define fgl-rewrite-try-rules ((rules fgl-rulelist-p)
                                     (fn pseudo-fnsym-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :guard (and (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        ;; :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 (len rules) 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* (((when (atom rules))
              (fgl-interp-value nil nil))
             ((fgl-interp-recursive-call successp ans)
              (fgl-rewrite-try-rule (car rules) fn interp-st state))
             ((when successp)
              (fgl-interp-value successp ans)))
          (fgl-rewrite-try-rules (cdr rules) fn interp-st state)))

      (define fgl-rewrite-try-rule ((rule fgl-rule-p)
                                    (fn pseudo-fnsym-p)
                                    (interp-st interp-st-bfrs-ok)
                                   state)
        :guard (and (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 2)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (fgl-rule-case rule
          :rewrite (fgl-rewrite-try-rewrite rule fn interp-st state)
          :meta (fgl-rewrite-try-meta rule fn interp-st state)
          :primitive (fgl-rewrite-try-primitive rule fn
                                                (interp-st-top-scratch-fgl-objlist interp-st)
                                                interp-st
                                                state)))


      (define fgl-rewrite-apply-rule ((rule fgl-generic-rule-p)
                                      (fn pseudo-fnsym-p)
                                      (bindings fgl-object-bindings-p)
                                      (hyps pseudo-term-listp)
                                      (rhs pseudo-termp)
                                      (rhs-equiv equiv-contextsp)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :guard (interp-st-bfr-listp (fgl-object-bindings-bfrlist bindings))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     (new-bindings fgl-object-bindings-p)
                     new-interp-st new-state)
        (b* (((when (interp-st->errmsg interp-st))
              ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
              (fgl-interp-value nil nil nil))
             (rune (fgl-generic-rule->rune rule))
             (interp-st (interp-st-push-rule-frame rule bindings interp-st))
             (interp-st (interp-st-prof-push rune interp-st))
             (tracep (interp-st-do-trace? fn interp-st state))
             (interp-st (interp-st-trace-start tracep fn interp-st state))

             (backchain-limit (interp-st->backchain-limit interp-st))
             ;; (hyps-flags  (!interp-flags->intro-bvars nil flags))
             ((interp-st-bind
               ;; (flags hyps-flags flags)
               ;; NOTE: Even when in an unequiv context, we rewrite the hyps under IFF.
               (equiv-contexts '(iff))
               (backchain-limit (1- backchain-limit) backchain-limit))

              ((fgl-interp-recursive-call failed-hyp)
               (fgl-rewrite-relieve-hyps hyps interp-st state)))

             ((when (or** failed-hyp (interp-st->errmsg interp-st)))
              (b* ((interp-st (interp-st-trace-hyp-failure tracep failed-hyp fn interp-st state))
                   (interp-st (interp-st-prof-pop-increment nil interp-st))
                   (interp-st (interp-st-pop-frame interp-st))
                   (interp-st (interp-st-cancel-error :intro-bvars-fail interp-st))
                   (interp-st (interp-st-cancel-error :abort-rewrite interp-st)))
                (fgl-interp-value nil nil nil)))

             (interp-st (interp-st-set-term rhs interp-st))
             (interp-st (interp-st-set-term-index nil interp-st))
             ((interp-st-bind
               (equiv-contexts rhs-equiv))
              ((fgl-interp-value val)
               ;; Note: Was interp-term-equivs
               (fgl-interp-term rhs interp-st state)))

             (successp (not (interp-st->errmsg interp-st)))
             (interp-st (interp-st-cancel-error :abort-rewrite interp-st))
             (interp-st (interp-st-prof-pop-increment successp interp-st))
             (interp-st (interp-st-trace-finish tracep successp val fn interp-st state))

             (new-bindings (interp-st-bindings interp-st))
             (interp-st (interp-st-pop-frame interp-st)))
          (fgl-interp-value successp val new-bindings)))

      (define fgl-rewrite-try-rewrite ((rule fgl-rule-p)
                                    (fn pseudo-fnsym-p)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :guard (and (fgl-rule-case rule :rewrite)
                    (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 1)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* (((fgl-rule-rewrite rule))
             (backchain-limit (interp-st->backchain-limit interp-st))
             ((when (and** rule.hyps (eql 0 backchain-limit)))
              (fgl-interp-value nil nil))
             ((unless (and (fgl-interp-equiv-refinementp rule.equiv
                                                         (interp-st->equiv-contexts interp-st))
                           (pseudo-term-case rule.lhs :fncall)))
              (fgl-interp-value nil nil))
             (args (interp-st-top-scratch-fgl-objlist interp-st))
             ;; (rule.lhs.args (pseudo-term-call->args rule.lhs))
             ((mv unify-ok bindings) (fgl-unify-term/gobj-fn/args
                                      (pseudo-term-fncall->fn rule.lhs)
                                      (pseudo-term-call->args rule.lhs)
                                      fn args
                                      nil (interp-st-bfr-state)))
             ((unless unify-ok) (fgl-interp-value nil nil))
             ((fgl-interp-value successp ans ?bindings)
              (fgl-rewrite-apply-rule
               (fgl-rule-fix rule) fn
               bindings
               rule.hyps
               rule.rhs
               (interp-st->equiv-contexts interp-st)
               interp-st state)))
          (fgl-interp-value successp ans)))

      (define fgl-rewrite-try-meta ((rule fgl-rule-p)
                                    (fn pseudo-fnsym-p)
                                    (interp-st interp-st-bfrs-ok)
                                    state)
        :guard (and (fgl-rule-case rule :meta)
                    (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* ((args (interp-st-top-scratch-fgl-objlist interp-st))
             (rule (fgl-rule-fix rule))
             (fn (pseudo-fnsym-fix fn))
             (tracep (fgl-rewrite-do-trace? rule fn args interp-st state))
             (interp-st (fgl-rewrite-trace-start tracep rule fn args interp-st state))
             (interp-st (interp-st-prof-push (fgl-rule->rune rule) interp-st))
             ((fgl-interp-value successp rhs bindings)
              (fgl-meta-fncall-stub (fgl-rule-meta->name rule) fn args interp-st state))
             ((when (or** (not successp) (interp-st->errmsg interp-st)))
              (b* ((interp-st (interp-st-prof-pop-increment nil interp-st))
                   (interp-st (fgl-rewrite-trace-finish tracep successp nil rule fn args interp-st state)))
                (fgl-interp-value nil nil)))

             (interp-st (interp-st-push-rule-frame rule bindings interp-st))
             (interp-st (interp-st-set-term rhs interp-st))
             ((fgl-interp-value val) (fgl-interp-term rhs interp-st state))

             (successp (not (interp-st->errmsg interp-st)))
             (interp-st (interp-st-prof-pop-increment successp interp-st))
             (interp-st (interp-st-cancel-error :abort-rewrite interp-st))
             (interp-st (fgl-rewrite-trace-finish tracep successp val rule fn args interp-st state))
             (interp-st (interp-st-pop-frame interp-st)))
          (fgl-interp-value successp val)))


      (define fgl-rewrite-relieve-hyps ((hyps pseudo-term-listp)
                                       (interp-st interp-st-bfrs-ok)
                                       state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 9000
                       (pseudo-term-list-binding-count hyps) 0)
        :returns (mv (failed-hyp acl2::maybe-natp :rule-classes :type-prescription)
                     new-interp-st new-state)
        (b* (((when (atom hyps))
              (fgl-interp-value nil))
             ((fgl-interp-recursive-call ok)
              (fgl-rewrite-relieve-hyp (car hyps) interp-st state))
             ((when (not ok))
              (fgl-interp-value (or (interp-st-phase interp-st) 0)))
             (interp-st (interp-st-incr-phase interp-st)))
          (fgl-rewrite-relieve-hyps (cdr hyps) interp-st state)))

      (define fgl-rewrite-relieve-hyp ((hyp pseudo-termp)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 9000
                       (pseudo-term-binding-count hyp) 0)
        :returns (mv successp
                     new-interp-st new-state)
        (b* ((interp-st (interp-st-set-term hyp interp-st))
             (interp-st (interp-st-set-term-index nil interp-st))
             ((mv synp-type untrans-form trans-term vars)
              (fgl-interp-match-synp hyp))
             ((when synp-type)
              (fgl-rewrite-relieve-hyp-synp synp-type trans-term vars untrans-form interp-st state))
             ((fgl-interp-recursive-call bind-ok)
              (fgl-interp-binding-hyp hyp interp-st state))
             ((when bind-ok)
              (fgl-interp-value t))
             ((fgl-interp-value test-bfr)
              (fgl-interp-test hyp interp-st state)))
          ;; Could check against the pathcond here...
          (fgl-interp-value (eq test-bfr t))))

      (define fgl-interp-time$ ((timing-arg pseudo-termp)
                               (x pseudo-termp)
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                       (+ (pseudo-term-binding-count timing-arg)
                          (pseudo-term-binding-count x))
                       30)
        :returns (mv
                  (xobj fgl-object-p)
                  new-interp-st new-state)
        (b* (((interp-st-bind
               (equiv-contexts nil))
              ((fgl-interp-recursive-call time$-arg)
               (fgl-interp-term-equivs timing-arg interp-st state)))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             (time$-arg (fgl-interp-time$-arg time$-arg x)))
          (acl2::time$1 time$-arg
                        ;; Note: Was interp-term-equivs
                        (fgl-interp-term x interp-st state))))


      (define fgl-interp-return-last ((return-last-fnname pseudo-termp)
                                     (first-arg pseudo-termp)
                                     (x pseudo-termp)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                       (+ (pseudo-term-binding-count first-arg)
                          (pseudo-term-binding-count x))
                       40)
        :returns (mv
                  (xobj fgl-object-p)
                  new-interp-st new-state)
        (b* (((when (equal return-last-fnname ''acl2::time$1-raw))
              (fgl-interp-time$ first-arg x interp-st state))
             (interp-st (interp-st-incr-term-index (+ (fgl-minor-frame-subterm-count return-last-fnname)
                                                      (fgl-minor-frame-subterm-count first-arg))
                                                   interp-st)))
          ;; Otherwise just evaluate the last-arg.
          ;; Note: Was interp-term-equivs
          (fgl-interp-term x interp-st state)))

      ;; (define fgl-interp-bind-var ((free-var pseudo-termp)
      ;;                             (form pseudo-termp)
      ;;                             (interp-st interp-st-bfrs-ok)
      ;;                             state)
      ;;   :measure (list (nfix (interp-st->reclimit interp-st))
      ;;                  2020 (pseudo-term-binding-count form)
      ;;                  70)
      ;;   :returns (mv (xobj fgl-object-p)
      ;;                new-interp-st new-state)
      ;;   (b* (((unless (pseudo-term-case free-var :var))
      ;;         (fgl-interp-error :msg (fgl-msg "Bad bind-var form -- first ~
      ;;                                        argument must be a variable, but ~
      ;;                                        was ~x0."
      ;;                                       (pseudo-term-fix free-var))))
      ;;        (varname (pseudo-term-var->name free-var))
      ;;        ;; increment term index for first arg (variable)
      ;;        (interp-st (interp-st-incr-term-index 1 interp-st))
      ;;        ((interp-st-bind
      ;;          (equiv-contexts '(unequiv)))
      ;;         ((fgl-interp-value val) (fgl-interp-term-equivs form interp-st state)))
      ;;        ((when (or (assoc-eq varname (interp-st-bindings interp-st))
      ;;                   (assoc-eq varname (interp-st-minor-bindings interp-st))))
      ;;         (fgl-interp-error
      ;;          :msg (fgl-msg "Bind-var error: ~x0 was supposed to be bound in ~
      ;;                        a bind-var form but was already bound."
      ;;                       varname)))
      ;;        (interp-st (interp-st-add-binding varname val interp-st)))
      ;;     (fgl-interp-value val)))

      (define fgl-interp-binding-hyp ((hyp pseudo-termp)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2040 (pseudo-term-binding-count hyp)
                       18)
        :returns (mv okp new-interp-st new-state)
        (b* (((mv var form equiv incr)
              (check-equivbind-hyp hyp interp-st state))
             ((unless var) (fgl-interp-value nil))
             ((interp-st-bind
               (equiv-contexts (equiv-contexts-from-equiv equiv)))
              (interp-st (interp-st-incr-term-index incr interp-st))
              ((fgl-interp-recursive-call result)
               (fgl-interp-term-top form interp-st state)))
             ((when (fgl-var-lookup var interp-st))
              (fgl-interp-error
               :msg (fgl-msg "Binding hyp's free variable ~x0 was bound within its binding term: ~x1" var form)))
             (interp-st (interp-st-add-binding var result interp-st)))
          (fgl-interp-value t)))



      (define fgl-interp-binder ((form pseudo-termp)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count form)
                       18)
        :returns (mv (xobj fgl-object-p)
                     new-interp-st new-state)
        (b* (((unless (pseudo-term-case form :fncall))
              (fgl-interp-error :msg (fgl-msg "Bad binder form -- the ~
                                               argument must be a function ~
                                               call, but was ~x0."
                                            (pseudo-term-fix form))))
             ((pseudo-term-fncall form))
             ((unless (and (consp form.args)
                           (pseudo-term-case (car form.args) :var)))
              (fgl-interp-error :msg (fgl-msg "Bad binder form -- the ~
                                               argument must be a function ~
                                               call whose first argument is ~
                                               the variable to be bound, but instead ~@0."
                                              (if (consp form.args)
                                                  (msg "was ~x0" (car form.args))
                                                (msg "the function call was 0-ary.")))))
             (varname (pseudo-term-var->name (car form.args)))

             ;; increment term index for function and first arg
             (interp-st (interp-st-incr-term-index 2 interp-st))
             (argcontexts (equiv-argcontexts-rest
                           (fgl-interp-arglist-equiv-contexts
                            (interp-st->equiv-contexts interp-st)
                            form.fn (len form.args) (w state))))
             ((fgl-interp-recursive-call argvals)
              (fgl-interp-arglist (cdr form.args) argcontexts interp-st state))

             ((when (or (assoc-eq varname (interp-st-bindings interp-st))
                        (assoc-eq varname (interp-st-minor-bindings interp-st))))
              (fgl-interp-error
               :msg (fgl-msg "Binder error: ~x0 was supposed to be bound in ~
                             a binder form but was already bound."
                            varname)))

             ((fgl-interp-recursive-call successp var-val)
              (fgl-rewrite-binder-fncall form.fn argvals interp-st state))
             ((unless successp)
              (fgl-interp-error
               :msg (fgl-msg "Binder error: no binder rule succeeded on ~x0 to bind ~x1" form.fn varname)))
             (interp-st (interp-st-add-binding varname var-val interp-st)))
          (fgl-interp-value var-val)))

      (define fgl-rewrite-binder-fncall ((fn pseudo-fnsym-p)
                                         (args fgl-objectlist-p)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
        :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 0 0 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* ((reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.") :nvals 2))
             ((mv rules interp-st) (interp-st-function-binder-rules fn interp-st state))
             ((unless rules)
              (fgl-interp-value nil nil))
             (interp-st (interp-st-push-scratch-fgl-objlist args interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((fgl-interp-value successp ans)
               (fgl-rewrite-binder-try-rules rules fn interp-st state)))
             (interp-st (interp-st-pop-scratch interp-st)))
          (fgl-interp-value successp ans)))


      (define fgl-rewrite-binder-try-rules ((rules fgl-binder-rulelist-p)
                                            (fn pseudo-fnsym-p)
                                            (interp-st interp-st-bfrs-ok)
                                            state)
        :guard (and (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        ;; :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 (len rules) 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* (((when (atom rules))
              (fgl-interp-value nil nil))
             ((fgl-interp-recursive-call successp ans)
              (fgl-rewrite-binder-try-rule (car rules) fn interp-st state))
             ((when successp)
              (fgl-interp-value successp ans)))
          (fgl-rewrite-binder-try-rules (cdr rules) fn interp-st state)))

      (define fgl-rewrite-binder-try-rule ((rule fgl-binder-rule-p)
                                           (fn pseudo-fnsym-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
        :guard (and (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 2)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (fgl-binder-rule-case rule
          :brewrite (fgl-rewrite-binder-try-rewrite rule fn interp-st state)
          :bmeta (fgl-rewrite-binder-try-meta rule fn interp-st state)))

      (define fgl-rewrite-binder-try-rewrite ((rule fgl-binder-rule-p)
                                              (fn pseudo-fnsym-p)
                                              (interp-st interp-st-bfrs-ok)
                                              state)
        :guard (and (fgl-binder-rule-case rule :brewrite)
                    (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 1)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* (((fgl-binder-rule-brewrite rule))
             (backchain-limit (interp-st->backchain-limit interp-st))
             ((when (and** rule.hyps (eql 0 backchain-limit)))
              (fgl-interp-value nil nil))
             ((unless (fgl-interp-equiv-refinementp rule.equiv
                                                   (interp-st->equiv-contexts interp-st)))
              (fgl-interp-value nil nil))
             ((unless (eq rule.lhs-fn (pseudo-fnsym-fix fn)))
              (fgl-interp-value nil nil))
             (args (interp-st-top-scratch-fgl-objlist interp-st))
             ;; (rule.lhs.args (pseudo-term-call->args rule.lhs))
             ((mv unify-ok bindings) (fgl-unify-term/gobj-list rule.lhs-args
                                                               args
                                                               nil
                                                               (interp-st-bfr-state)))
             ((unless unify-ok) (fgl-interp-value nil nil))
             ((fgl-interp-value successp ans ?bindings)
              (fgl-rewrite-apply-rule
               (fgl-binder-rule-fix rule) fn bindings rule.hyps
               rule.rhs (list rule.r-equiv) interp-st state)))
          (fgl-interp-value successp ans)))

      (define fgl-rewrite-binder-try-meta ((rule fgl-binder-rule-p)
                                              (fn pseudo-fnsym-p)
                                              (interp-st interp-st-bfrs-ok)
                                              state)
        :guard (and (fgl-binder-rule-case rule :bmeta)
                    (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* ((args (interp-st-top-scratch-fgl-objlist interp-st))
             (rule (fgl-binder-rule-fix rule))
             (fn (pseudo-fnsym-fix fn))
             (tracep (fgl-rewrite-do-trace? rule fn args interp-st state))
             (interp-st (fgl-rewrite-trace-start tracep rule fn args interp-st state))
             (interp-st (interp-st-prof-push (fgl-binder-rule->rune rule) interp-st))
             ((fgl-interp-value successp rhs bindings rhs-contexts)
              (fgl-binder-fncall-stub (fgl-binder-rule-bmeta->name rule) fn args interp-st state))
             ((when (or** (not successp) (interp-st->errmsg interp-st)))
              (b* ((interp-st (interp-st-prof-pop-increment nil interp-st))
                   (interp-st (fgl-rewrite-trace-finish tracep successp nil rule fn args interp-st state)))
                (fgl-interp-value nil nil)))

             (interp-st (interp-st-push-rule-frame rule bindings interp-st))
             (interp-st (interp-st-set-term rhs interp-st))
             ((interp-st-bind
               (equiv-contexts rhs-contexts))
              ((fgl-interp-value val) (fgl-interp-term rhs interp-st state)))

             (successp (not (interp-st->errmsg interp-st)))
             (interp-st (interp-st-prof-pop-increment successp interp-st))
             (interp-st (interp-st-cancel-error :abort-rewrite interp-st))
             (interp-st (fgl-rewrite-trace-finish tracep successp val rule fn args interp-st state))
             (interp-st (interp-st-pop-frame interp-st)))
          (fgl-interp-value successp val)))

      (define fgl-interp-if/or ((test pseudo-termp)
                               (then pseudo-termp)
                               (else pseudo-termp)
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count then)
                          (pseudo-term-binding-count else))
                       60)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (if (interp-flags->branch-on-ifs (interp-st->flags interp-st))
            (if (hons-equal test then)
                (fgl-interp-or test else interp-st state)
              (fgl-interp-if test then else interp-st state))
          (if (hons-equal test then)
              (fgl-interp-or-nonbranching test else interp-st state)
            (fgl-interp-if-nonbranching test then else interp-st state))))

      (define fgl-interp-if-nonbranching ((test pseudo-termp)
                                         (then pseudo-termp)
                                         (else pseudo-termp)
                                         (interp-st interp-st-bfrs-ok)
                                         state)

        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count then)
                          (pseudo-term-binding-count else))
                       40)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* (((interp-st-bind
               (equiv-contexts (fgl-interp-test-equiv-contexts (interp-st->equiv-contexts interp-st))))
              ((fgl-interp-recursive-call testobj)
               (fgl-interp-term-equivs test interp-st state)))
             ((mv ok boolfix) (gobj-syntactic-boolean-fix testobj))
             ((unless (and** ok (fgl-object-case boolfix :g-concrete)))
              (fgl-interp-error :msg (fgl-msg "Symbolic IF test occurred under ~
                                             nonbranching context -- see ~
                                             debug obj. Resulted from term: ~
                                             ~x0"
                                            (pseudo-term-fix test))
                               :debug-obj boolfix)))
          (if (g-concrete->val boolfix)
              (b* (((fgl-interp-value ans)
                    (fgl-interp-term-top then interp-st state))
                   (interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count else) interp-st)))
                (fgl-interp-value ans))
            (b* ((interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count then) interp-st)))
              (fgl-interp-term-top else interp-st state)))))

      (define fgl-interp-or-nonbranching ((test pseudo-termp)
                                         (else pseudo-termp)
                                         (interp-st interp-st-bfrs-ok)
                                         state)

        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count else))
                       40)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* ((equiv-contexts  (interp-st->equiv-contexts interp-st))
             ((interp-st-bind
               (equiv-contexts (fgl-interp-or-test-equiv-contexts equiv-contexts) equiv-contexts))
              ((fgl-interp-recursive-call testobj)
               (fgl-interp-term-equivs test interp-st state)))
             ((mv ok boolfix) (gobj-syntactic-boolean-fix testobj))
             ((unless (and** ok (fgl-object-case boolfix :g-concrete)))
              (fgl-interp-error :msg (fgl-msg "Symbolic IF test occurred under ~
                                             nonbranching context -- see ~
                                             debug obj. Resulted from term: ~
                                             ~x0"
                                            (pseudo-term-fix test))
                               :debug-obj boolfix)))
          (if (g-concrete->val boolfix)
              (b* ((interp-st (interp-st-incr-term-index
                               (+ (fgl-minor-frame-subterm-count test)
                                  (fgl-minor-frame-subterm-count else))
                               interp-st)))
                (fgl-interp-value testobj))
            (b* ((interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count test) interp-st)))
              (fgl-interp-term-top else interp-st state)))))


      (define fgl-interp-if ((test pseudo-termp)
                            (then pseudo-termp)
                            (else pseudo-termp)
                            (interp-st interp-st-bfrs-ok)
                            state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count then)
                          (pseudo-term-binding-count else))
                       40)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        ;; Tricky because we have to keep the test/thenval on the stack while we
        ;; run the then/else branches, because we might simplify the logicman while
        ;; running them.
        (b* (((fgl-interp-recursive-call testbfr)
              (fgl-interp-test test interp-st state))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((fgl-interp-recursive-call then-unreachable thenval)
              ;; pushes val onto scratch if not unreachable
              (fgl-maybe-interp testbfr then interp-st state))
             (testbfr (interp-st-top-scratch-bfr interp-st))
             (interp-st (interp-st-push-scratch-fgl-obj thenval interp-st))
             ((fgl-interp-recursive-call else-unreachable elseval)
              ;; pushes val onto scratch if not unreachable
              (fgl-maybe-interp (interp-st-bfr-not testbfr) else interp-st state))
             ((mv thenval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((when then-unreachable)
              (if else-unreachable
                  (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
                    (fgl-interp-value nil))
                (fgl-interp-value elseval)))
             ((when else-unreachable)
              (fgl-interp-value thenval)))
          (fgl-interp-merge-branches testbfr thenval elseval interp-st state)))



      (define fgl-interp-or ((test pseudo-termp)
                            (else pseudo-termp)
                            (interp-st interp-st-bfrs-ok)
                            state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count else))
                       40)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* ((equiv-contexts (interp-st->equiv-contexts interp-st))
             (or-test-equiv-contexts (fgl-interp-or-test-equiv-contexts equiv-contexts))
             ((interp-st-bind
               (equiv-contexts or-test-equiv-contexts equiv-contexts))
              ((fgl-interp-recursive-call testval)
               (fgl-interp-term-equivs test interp-st state)))
             (interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count test) interp-st))
             ;; ((when err) (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-fgl-obj testval interp-st))
             ((fgl-interp-recursive-call testbfr)
              (fgl-interp-simplify-if-test
               ;; Already rewritten under IFF/unequiv if original contexts
               ;; contained IFF/unequiv.
               (fgl-interp-or-test-already-rewrittenp equiv-contexts)
               testval interp-st state))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((fgl-interp-recursive-call else-unreachable elseval)
              (fgl-maybe-interp (interp-st-bfr-not testbfr) else interp-st state))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv testval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
             ((when else-unreachable)
              (fgl-interp-value testval)))
          (fgl-interp-merge-branches testbfr testval elseval interp-st state)))

      (define fgl-interp-assume ((test pseudo-termp)
                                (x pseudo-termp)
                                (interp-st interp-st-bfrs-ok)
                                state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count x))
                       40)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* (((unless (member-eq 'unequiv (interp-st->equiv-contexts interp-st)))
              (fgl-interp-error :msg (fgl-msg "Assume called not in an unequiv context: args ~x0."
                                            (list (pseudo-term-fix test) (pseudo-term-fix x)))))
             ((fgl-interp-recursive-call testbfr)
              (fgl-interp-test test interp-st state))
             ((fgl-interp-value ?unreachp ans)
              (fgl-maybe-interp testbfr x interp-st state)))
          (fgl-interp-value ans)))

      (define fgl-interp-narrow-equiv ((equiv pseudo-termp)
                                     (x pseudo-termp)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count equiv)
                          (pseudo-term-binding-count x))
                       40)
        :returns (mv
                  (xobj fgl-object-p)
                  new-interp-st new-state)
        (b* (((fgl-interp-recursive-call equivobj)
              (fgl-interp-term-equivs equiv interp-st state))
             ((unless (fgl-object-case equivobj :g-concrete))
              (fgl-interp-error :msg (fgl-msg "First argument to narrow-equiv ~
                                             yielded a non-constant object: ~
                                             args ~x0."
                                            (list (pseudo-term-fix equiv) (pseudo-term-fix x)))))
             (contexts (g-concrete->val equivobj))
             ((unless (equiv-contextsp contexts))
              (fgl-interp-error :msg (fgl-msg "First argument to narrow-equiv ~
                                             yielded a value that did not ~
                                             satisfy equiv-contextsp: args ~
                                             ~x0."
                                            (list (pseudo-term-fix equiv) (pseudo-term-fix x)))))
             ((unless (equiv-contexts-coarsening-p (interp-st->equiv-contexts interp-st) contexts))
              (fgl-interp-error :msg (fgl-msg "First argument to narrow-equiv ~
                                             yielded a value was not a ~
                                             narrowing of the current equiv ~
                                             contexts: ~x0.  Current equiv contexts: ~x1"
                                            (pseudo-term-fix equiv)
                                            (interp-st->equiv-contexts interp-st))))
             ((interp-st-bind
               (equiv-contexts contexts))
              ((fgl-interp-value ans)
               (fgl-interp-term-top x interp-st state))))
          (fgl-interp-value ans)))

      ;; (define fgl-interp-prog2 ((first-arg pseudo-termp)
      ;;                          (x pseudo-termp)
      ;;                          (interp-st interp-st-bfrs-ok)
      ;;                          state)
      ;;   :measure (list (nfix (interp-st->reclimit interp-st))
      ;;                  2020
      ;;                  (+ (pseudo-term-binding-count first-arg)
      ;;                     (pseudo-term-binding-count x))
      ;;                  40)
      ;;   :returns (mv
      ;;             (xobj fgl-object-p)
      ;;             new-interp-st new-state)
      ;;   (b* (((interp-st-bind
      ;;          (equiv-contexts '(unequiv)))
      ;;         ((fgl-interp-recursive-call ?ign)
      ;;          (fgl-interp-term-equivs first-arg interp-st state))))
      ;;     (fgl-interp-term-equivs x interp-st state)))

      (define fgl-interp-fgl-interp-obj ((x pseudo-termp)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (pseudo-term-binding-count x)
                       60)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* (((unless (member-eq 'unequiv (interp-st->equiv-contexts interp-st)))
              (fgl-interp-error :msg (fgl-msg "Fgl-interp-obj called not in an unequiv context: args ~x0."
                                            (list (pseudo-term-fix x)))))
             (reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.")))
             ((fgl-interp-recursive-call xobj)
              (fgl-interp-term-equivs x interp-st state))
             ((unless (fgl-object-case xobj :g-concrete))
              (fgl-interp-error :msg (fgl-msg "First argument to fgl-interp-obj ~
                                             yielded a non-constant object: ~
                                             args ~x0."
                                            (list (pseudo-term-fix x)))))
             (term (g-concrete->val xobj))
             ((unless (easy-termp term (w state)))
              (fgl-interp-error :msg (fgl-msg "First argument to fgl-interp-obj ~
                                             yielded a value that did not ~
                                             satisfy termp: args ~
                                             ~x0."
                                            (list (pseudo-term-fix x)))))
             (interp-st (interp-st-incr-term-index 1 interp-st))
             (interp-st (interp-st-push-minor-frame interp-st))
             (interp-st (interp-st-set-term term interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((fgl-interp-value ans)
               (fgl-interp-term-top term interp-st state)))
             (interp-st (interp-st-pop-minor-frame interp-st)))
          (fgl-interp-value ans)))


      (define fgl-maybe-interp ((test interp-st-bfr-p)
                               (x pseudo-termp)
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (pseudo-term-binding-count x)
                       100)
        :returns (mv
                  unreachable
                  (ans fgl-object-p)
                  new-interp-st new-state)
        ;; (pseudo-term-case x
        ;;   :call
          (b* (((mv contra interp-st)
                (interp-st-pathcond-assume test interp-st))
               ((when contra)
                (b* ((interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count x) interp-st)))
                  (fgl-interp-value t nil)))
               ((when (interp-st->errmsg interp-st))
                (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                  ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
                  (fgl-interp-value nil nil)))
               ((fgl-interp-value ans)
                (fgl-interp-term-top x interp-st state))
               (interp-st (interp-st-pathcond-rewind interp-st))
               ((when (eq (interp-st->errmsg interp-st) :unreachable))
                (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
                  (fgl-interp-value t nil))))
            (fgl-interp-value nil ans)))

      (define fgl-interp-maybe-simplify-if-test ((test interp-st-bfr-p)
                                                (xobj fgl-object-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
        :guard (interp-st-bfr-listp (fgl-object-bfrlist xobj))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       0
                       (fgl-object-count xobj)
                       60)
        :returns (mv
                  unreachable
                  xbfr
                  new-interp-st new-state)
        (if (fgl-object-case xobj '(:g-concrete :g-boolean :g-integer :g-cons :g-map))
            ;; Easy cases -- don't bother with the pathcond
            (b* ((reclimit (interp-st->reclimit interp-st))
                 ((when (fgl-interp-check-reclimit interp-st))
                  (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.") :nvals 2))
                 ((interp-st-bind
                   (reclimit (1- reclimit) reclimit))
                  ((fgl-interp-value ans)
                   (fgl-interp-simplify-if-test nil xobj interp-st state))))
              (fgl-interp-value nil ans))
          ;; Harder cases.
          (b* (((mv contra interp-st)
                (interp-st-pathcond-assume test interp-st))
               ((when contra)
                (fgl-interp-value t nil))
               (reclimit (interp-st->reclimit interp-st))
               ((when (fgl-interp-check-reclimit interp-st))
                (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                  (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.") :nvals 2)))
               ((when (interp-st->errmsg interp-st))
                (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                  ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
                  (fgl-interp-value nil nil)))
               ((interp-st-bind
                 (reclimit (1- reclimit) reclimit))
                ((fgl-interp-value ans)
                 (fgl-interp-simplify-if-test nil xobj interp-st state)))
               (interp-st (interp-st-pathcond-rewind interp-st))
               ((when (eq (interp-st->errmsg interp-st) :unreachable))
                (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
                  (fgl-interp-value t nil))))
            (fgl-interp-value nil ans))))

      (define fgl-interp-simplify-if-test ((already-rewrittenp)
                                          (xobj fgl-object-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)
        :guard (interp-st-bfr-listp (fgl-object-bfrlist xobj))
        :returns (mv
                  xbfr
                  new-interp-st new-state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (fgl-object-count xobj)
                       40)
        (fgl-object-case xobj
          :g-concrete (fgl-interp-value (bool-fix xobj.val))
          :g-boolean (fgl-interp-value xobj.bool)
          :g-integer (fgl-interp-value t)
          :g-cons (fgl-interp-value t)
          :g-var (b* (((mv ans interp-st) (interp-st-add-term-bvar-unique xobj interp-st state)))
                   (fgl-interp-value ans))
          :g-ite (fgl-interp-simplify-if-test-ite xobj interp-st state)
          :g-apply (fgl-interp-simplify-if-test-fncall already-rewrittenp xobj interp-st state)
          :g-map (fgl-interp-value (bool-fix xobj.alist))))

      ;; BOZO should we have a version of this for OR?
      (define fgl-interp-simplify-if-test-ite ((xobj fgl-object-p)
                                              (interp-st interp-st-bfrs-ok)
                                              state)
        :guard (and (fgl-object-case xobj :g-ite)
                    (interp-st-bfr-listp (fgl-object-bfrlist xobj)))
        :returns (mv
                  xbfr
                  new-interp-st new-state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (fgl-object-count xobj)
                       30)
        (b* (((unless (mbt (fgl-object-case xobj :g-ite)))
              (fgl-interp-error :msg (fgl-msg "Impossible case")))
             ((g-ite xobj))
             (interp-st (interp-st-push-scratch-fgl-obj xobj.else interp-st))
             (interp-st (interp-st-push-scratch-fgl-obj xobj.then interp-st))
             ;; scratch: xobj.then, xobj.else
             ((fgl-interp-recursive-call test-bfr)
              (fgl-interp-simplify-if-test t xobj.test interp-st state))
             (xobj.then (interp-st-top-scratch-fgl-obj interp-st))
             (interp-st (interp-st-update-scratch-bfr 0 test-bfr interp-st))
             ;; scratch: test-bfr, xobj.else
             ((fgl-interp-recursive-call then-unreachable then-bfr)
              (fgl-interp-maybe-simplify-if-test test-bfr xobj.then interp-st state))
             (test-bfr (interp-st-top-scratch-bfr interp-st))
             (xobj.else (interp-st-nth-scratch-fgl-obj 1 interp-st))
             (interp-st (interp-st-update-scratch-bfr 1 then-bfr interp-st))
             (neg-test (stobj-let ((logicman (interp-st->logicman interp-st)))
                                  (not)
                                  (bfr-not test-bfr)
                                  not))
             ;; scratch: test-bfr, then-bfr
             ((fgl-interp-value else-unreachable else-bfr)
              (fgl-interp-maybe-simplify-if-test neg-test xobj.else interp-st state))

             ((mv test-bfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv then-bfr interp-st) (interp-st-pop-scratch-bfr interp-st)))
          (fgl-interp-finish-simplify-if-test-ite
           test-bfr then-bfr else-bfr then-unreachable else-unreachable interp-st state)))

      (define fgl-interp-simplify-if-test-fncall ((already-rewrittenp)
                                                 (xobj fgl-object-p)
                                                 (interp-st interp-st-bfrs-ok)
                                                 state)
        :guard (and (fgl-object-case xobj :g-apply)
                    (interp-st-bfr-listp (fgl-object-bfrlist xobj)))

        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (fgl-object-count xobj)
                       20)
        :returns (mv
                  xbfr
                  new-interp-st new-state)
        (b* (((unless (mbt (fgl-object-case xobj :g-apply)))
              (fgl-interp-error :msg (fgl-msg "Impossible")))
             ((mv not-matched neg-arg)
              (fgl-apply-match-not xobj))
             ((when not-matched)
              (b* (((fgl-interp-value bfr)
                    (fgl-interp-simplify-if-test nil neg-arg interp-st state))
                   ;; ((when err)
                   ;;  (mv nil interp-st state))
                   )
                (fgl-interp-value (interp-st-bfr-not bfr))))
             ((g-apply xobj))
             ((fgl-function-mode fn-mode)
              (fgl-function-mode-lookup xobj.fn (fgl-config->function-modes
                                                (interp-st->config interp-st))))

             ;; We rewrite this fncall again because it presumably might not have
             ;; been done in IFF context before.  E.g.
             ;; (let ((a (foo x)))
             ;;   (if a y z))
             ;; Note we wouldn't do this fully "right" even if we had perfect
             ;; knowledge of congruences because our test term might be bound to a
             ;; variable that is used in both Boolean and non-Boolean contexts.

             ;; Note this is still a little weak -- e.g. if foo above is a
             ;; function that has an IFF congruence under IFF, then in the call
             ;; above x is rewritten under an EQUAL congruence context, and our
             ;; re-rewriting foo under an IFF congruence doesn't help that
             ;; because we're not rewriting the args over again.

             (reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error
               :msg (fgl-msg "The recursion limit ran out.")))
             (interp-st (interp-st-push-scratch-fgl-obj xobj interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit)
               (equiv-contexts '(iff)))
              ((fgl-interp-recursive-call successp ans)
               (fgl-rewrite-fncall xobj.fn xobj.args
                                  (or** already-rewrittenp
                                        fn-mode.dont-rewrite-under-if-test)
                                  interp-st state)))

             ((mv xobj interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             ((when successp)
              (b* (((interp-st-bind
                     (reclimit (1- reclimit) reclimit))
                    ((fgl-interp-value ans)
                     (fgl-interp-simplify-if-test t ans interp-st state))))
                (fgl-interp-value ans)))

             (xobj (hons-copy xobj))
             (look (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
                              (look)
                              (get-term->bvar xobj bvar-db)
                              look))
             ((when look)
              (b* ((bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
                                   (bfr)
                                   (bfr-var look)
                                   bfr)))
                (fgl-interp-value bfr)))

             ((unless (interp-flags->intro-bvars (interp-st->flags interp-st)))
              ;; Note: we only return intro-bvars-fail when this flag is set to
              ;; false, which it is not at the top level.  So when we set the flag
              ;; to true (as we do in relieve-hyp and add-bvar-constraint-substs,
              ;; e.g.) we check for this error specifically and catch it.
              ;; Otherwise we expect callers not to set intro-bvars to nil and then
              ;; they won't have to deal with this error specially.
              (b* ((interp-st (interp-st-set-error :intro-bvars-fail interp-st)))
                (fgl-interp-value nil)))

             ((mv bfr interp-st)
              (interp-st-add-term-bvar xobj interp-st state))

             (interp-st (interp-st-push-scratch-bfr bfr interp-st))

             ((fgl-interp-value)
              (fgl-interp-add-constraints xobj interp-st state))

             ((mv bfr interp-st) (interp-st-pop-scratch-bfr interp-st))

             ;; ((when err)
             ;;  (mv nil interp-st state))
             )
          (fgl-interp-value bfr)))


      (define fgl-interp-add-constraints ((xobj fgl-object-p)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
        :guard (and ;; (fgl-object-case xobj :g-apply)
                    (interp-st-bfr-listp (fgl-object-bfrlist xobj)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       1900
                       (fgl-object-count xobj)
                       15)
        :returns (mv new-interp-st new-state)
        (b* ((constraint-db (interp-st->constraint-db interp-st))
             ((mv constraint-substs constraint-db)
              (gbc-process-new-lit xobj constraint-db (interp-st-bfr-state) state))
             (interp-st (update-interp-st->constraint-db constraint-db interp-st))
             ((unless constraint-substs) (fgl-interp-value))
             (reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.") :nvals 0))
             ;; Disable the pathcond so that constraint thms are simulated in an empty (universal) context.
             ((fgl-interp-value pathcond-enabledp) (stobj-let ((pathcond (interp-st->pathcond interp-st)))
                                                          (enabledp pathcond)
                                                          (b* ((enabledp (pathcond-enabledp pathcond))
                                                               (pathcond (update-pathcond-enabledp nil pathcond)))
                                                            (mv enabledp pathcond))
                                                          (fgl-interp-value enabledp)))

             (flags (interp-st->flags interp-st))
             (new-flags  (!interp-flags->intro-synvars
                          t
                          ;; (!interp-flags->intro-bvars
                          ;;  nil
                           (!interp-flags->simplify-logic nil flags)))
             ((interp-st-bind
               (flags new-flags flags)
               (reclimit (1- reclimit) reclimit)
               (equiv-contexts '(iff)))
              ((fgl-interp-value)
               (fgl-interp-add-constraints-for-substs constraint-substs interp-st state))))

          (stobj-let ((pathcond (interp-st->pathcond interp-st)))
                     (pathcond)
                     (update-pathcond-enabledp pathcond-enabledp pathcond)
                     (fgl-interp-value))))



      (define fgl-interp-add-constraints-for-substs ((substs constraint-instancelist-p)
                                                    (interp-st interp-st-bfrs-ok)
                                                    state)
        :guard (interp-st-bfr-listp (constraint-instancelist-bfrlist substs))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       10000
                       (len substs)
                       10)
        :returns (mv new-interp-st new-state)
        (b* (((when (atom substs)) (fgl-interp-value))
             ((constraint-instance sub1) (car substs))
             (thm-body (meta-extract-formula sub1.thmname state))
             ((unless (pseudo-termp thm-body))
              (fgl-interp-add-constraints-for-substs (cdr substs) interp-st state))
             ((when (interp-st->errmsg interp-st))
              ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
              (fgl-interp-value))
             (interp-st (interp-st-push-scratch-cinstlist (cdr substs) interp-st))
             (interp-st (interp-st-push-frame sub1.subst interp-st))
             ((fgl-interp-recursive-call bfr)
              (fgl-interp-test thm-body interp-st state))
             (interp-st (interp-st-pop-frame interp-st))
             ((mv rest interp-st) (interp-st-pop-scratch-cinstlist interp-st))
             ((unless (mbt (eql (len rest) (len (cdr substs)))))
              ;; impossible case
              (fgl-interp-value))

             ((when (interp-st->errmsg interp-st))
              (b* ((interp-st (interp-st-cancel-error :intro-bvars-fail interp-st)))
                (fgl-interp-add-constraints-for-substs rest interp-st state)))
             ;; ((when err)
             ;;  (mv interp-st state))
             ((fgl-interp-value contra) (stobj-let ((constraint-pathcond (interp-st->constraint interp-st))
                                                (logicman (interp-st->logicman interp-st)))
                                               (contra constraint-pathcond)
                                               (logicman-pathcond-assume bfr constraint-pathcond)
                                               (fgl-interp-value contra)))
             ((when contra)
              (fgl-interp-error
               :msg (fgl-msg "A contradiction has been noted in the ~
                             constraints.  This is likely due to a bug in FGL ~
                             or an unsound fact stored in ACL2 (e.g., via ~
                             TTAG, skip-proofs, defaxiom, or soundness bug). ~
                             The constraint instance that led to the ~
                             contradiction is stored in the interpreter debug ~
                             object, but note that a previous constraint ~
                             instance might have caused the unsoundness.")
               :debug-obj sub1
               :nvals 0)))
          (fgl-interp-add-constraints-for-substs rest interp-st state)))

      (define fgl-interp-merge-branches ((testbfr interp-st-bfr-p)
                                        (thenval fgl-object-p)
                                        (elseval fgl-object-p)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
        :guard (and (interp-st-bfr-listp (fgl-object-bfrlist thenval))
                    (interp-st-bfr-listp (fgl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000 0 0)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* ((thenval (fgl-object-fix thenval))
             (elseval (fgl-object-fix elseval))
             ((when (eq testbfr t)) (fgl-interp-value thenval))
             ((when (eq testbfr nil)) (fgl-interp-value elseval))
             ((when (hons-equal thenval elseval)) (fgl-interp-value thenval)))
          (fgl-interp-merge-branches-rewrite testbfr thenval elseval interp-st state)))

      (define fgl-interp-merge-branches-rewrite ((testbfr interp-st-bfr-p)
                                                (thenval fgl-object-p)
                                                (elseval fgl-object-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
        :guard (and (interp-st-bfr-listp (fgl-object-bfrlist thenval))
                    (interp-st-bfr-listp (fgl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       1900 0 20)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* ((reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.")))

             (thenval (fgl-object-fix thenval))
             (elseval (fgl-object-fix elseval))
             (thenfn (fgl-fncall-object->fn thenval))
             (elsefn (fgl-fncall-object->fn elseval))

             ((mv then-rules else-rules if-rules interp-st)
              (interp-st-if-rules thenfn elsefn interp-st state))


             (interp-st (interp-st-push-scratch-fgl-obj elseval interp-st))
             (interp-st (interp-st-push-scratch-fgl-obj thenval interp-st))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             (interp-st (interp-st-push-scratch-fgl-objlist
                         (list (mk-g-boolean testbfr) thenval elseval)
                         interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((fgl-interp-value successp ans)
               (fgl-rewrite-try-rules3 then-rules else-rules if-rules 'if interp-st state)))
             (interp-st (interp-st-pop-scratch interp-st))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv thenval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
             ((mv elseval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             ((when successp)
              (fgl-interp-value ans)))
          (fgl-interp-merge-branch-subterms
           testbfr thenval elseval interp-st state)))

      (define fgl-rewrite-try-rules3 ((rules1 fgl-rulelist-p)
                                      (rules2 fgl-rulelist-p)
                                      (rules3 fgl-rulelist-p)
                                      (fn pseudo-fnsym-p)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :guard (and (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-objlist))
        ;; :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
        :returns (mv successp
                     (ans fgl-object-p)
                     new-interp-st new-state)
        (b* (((fgl-interp-recursive-call successp ans)
              (fgl-rewrite-try-rules rules1 fn interp-st state))
             ((when successp) (fgl-interp-value successp ans))
             ((fgl-interp-recursive-call successp ans)
              (fgl-rewrite-try-rules rules2 fn interp-st state))
             ((when successp) (fgl-interp-value successp ans)))
          (fgl-rewrite-try-rules rules3 fn interp-st state)))

      (define fgl-interp-merge-branch-subterms ((testbfr interp-st-bfr-p)
                                               (thenval fgl-object-p)
                                               (elseval fgl-object-p)
                                               (interp-st interp-st-bfrs-ok)
                                               state)
        :guard (and (interp-st-bfr-listp (fgl-object-bfrlist thenval))
                    (interp-st-bfr-listp (fgl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       1800 0 0)
        :returns (mv
                  (ans fgl-object-p)
                  new-interp-st new-state)
        (b* (((mv thenfn thenargs) (fgl-object-recognize-merge-fncall thenval))
             ((mv elsefn elseargs) (fgl-object-recognize-merge-fncall elseval))
             ((unless (and** thenfn
                             (eq thenfn elsefn)
                             (eql (len thenargs) (len elseargs))))
              (interp-st-fgl-object-basic-merge testbfr thenval elseval interp-st state))
             ;; BOZO sad:
             (reclimit (interp-st->reclimit interp-st))
             ((when (fgl-interp-check-reclimit interp-st))
              (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.")))


             ((interp-st-bind
               (reclimit (1- reclimit) reclimit)
               (equiv-contexts (fgl-interp-lambda-arglist-equiv-contexts (interp-st->equiv-contexts interp-st))))
              ((fgl-interp-recursive-call args)
               (fgl-interp-merge-branch-args testbfr thenargs elseargs interp-st state)))

             )
          (fgl-interp-fncall thenfn args interp-st state)))

      (define fgl-interp-merge-branch-args ((testbfr interp-st-bfr-p)
                                           (thenargs fgl-objectlist-p)
                                           (elseargs fgl-objectlist-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
        :guard (and (eql (len thenargs) (len elseargs))
                    (interp-st-bfr-listp (fgl-objectlist-bfrlist thenargs))
                    (interp-st-bfr-listp (fgl-objectlist-bfrlist elseargs)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       3000 (len thenargs) 0)
        :returns (mv
                  (args fgl-objectlist-p)
                  new-interp-st new-state)
        (b* (((when (atom thenargs))
              (fgl-interp-value nil))
             ;; (thenstack (interp-st->thenval-stack interp-st))
             ;; (thenval (car thenstack))
             ;; (interp-st (update-interp-st->thenval-stack (cdr thenstack) interp-st))
             ;; (elsestack (interp-st->elseval-stack interp-st))
             ;; (elseval (car elsestack))
             ;; (interp-st (update-interp-st->elseval-stack (cdr elsestack) interp-st))
             (interp-st (interp-st-push-scratch-fgl-objlist (cdr thenargs) interp-st))
             (interp-st (interp-st-push-scratch-fgl-objlist (cdr elseargs) interp-st))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((fgl-interp-recursive-call ans)
              (fgl-interp-merge-branches testbfr (car thenargs) (car elseargs) interp-st state))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv rest-elseargs interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))
             ((mv rest-thenargs interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))

             ((unless (mbt (eql (len (cdr thenargs)) (len rest-thenargs))))
              (fgl-interp-value nil))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-fgl-obj ans interp-st))
             ((fgl-interp-value args)
              (fgl-interp-merge-branch-args testbfr rest-thenargs rest-elseargs interp-st state))
             ((mv arg1 interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
          (fgl-interp-value (cons arg1 args)))))))







(local (defun find-flag-is-hyp (clause)
         (if (atom clause)
             nil
           (let ((lit (car clause)))
             (case-match lit
               (('not ('acl2::flag-is ('quote val))) val)
               (& (find-flag-is-hyp (cdr clause))))))))


(local
 (defsection-progn my-by-hint-cp
   (include-book "centaur/misc/beta-reduce-full" :dir :system)


   ;; (acl2::def-join-thms fgl-ev)

   (defthm beta-reduce-full-correct-fgl-ev
     (implies (pseudo-termp x)
              (equal (fgl-ev (acl2::beta-reduce-full x) a)
                     (fgl-ev x a)))
     :hints (("goal" :use ((:instance
                            (:functional-instance acl2::beta-reduce-full-correct
                             (acl2::beta-eval fgl-ev)
                             (acl2::beta-eval-list fgl-ev-list))
                            (x x) (a a)))
              :in-theory (enable fgl-ev-of-fncall-args
                                 fgl-ev-of-bad-fncall
                                 fgl-ev-of-nonsymbol-atom))))

   (defthm beta-reduce-full-list-correct-fgl-ev
     (implies (pseudo-term-listp x)
              (equal (fgl-ev-list (acl2::beta-reduce-full-list x) a)
                     (fgl-ev-list x a)))
     :hints (("goal" :use ((:instance
                            (:functional-instance acl2::beta-reduce-full-list-correct
                             (acl2::beta-eval fgl-ev)
                             (acl2::beta-eval-list fgl-ev-list))
                            (x x) (a a))))))

   (defthmd fgl-ev-of-disjoin-beta-reduce-full-list
     (implies (pseudo-term-listp x)
              (iff (fgl-ev (disjoin (acl2::beta-reduce-full-list x)) a)
                   (fgl-ev (disjoin x) a)))
     :hints(("Goal" :in-theory (enable acl2::beta-reduce-full-list (:i len))
             :expand ((acl2::beta-reduce-full-list x))
             :induct (len x))))

   (define dumb-negate ((x pseudo-termp))
     :returns (neg-x pseudo-termp)
     (pseudo-term-case x
       :fncall (if (eq x.fn 'not)
                   (car x.args)
                 `(not ,(pseudo-term-fix x)))
       :otherwise `(not ,(pseudo-term-fix x)))
     ///
     (defthm dumb-negate-correct
       (iff (fgl-ev (dumb-negate x) a)
            (not (fgl-ev x a)))))

   (define dumb-conjunction-to-literals ((x pseudo-termp))
     :returns (lits pseudo-term-listp)
     :measure (pseudo-term-count x)
     (pseudo-term-case x
       :fncall (if (and (eq x.fn 'if)
                        (equal (third x.args) ''nil))
                   (cons (dumb-negate (first x.args))
                         (dumb-conjunction-to-literals (second x.args)))
                 (list (dumb-negate (pseudo-term-fix x))))
       :otherwise (list (dumb-negate (pseudo-term-fix x))))
     ///
     (defthm dumb-conjunction-to-literals-correct
       (iff (fgl-ev (disjoin (dumb-conjunction-to-literals x)) a)
            (not (fgl-ev x a)))))


   (define dumb-formula-to-clause ((x pseudo-termp))
     :returns (clause pseudo-term-listp)
     (pseudo-term-case x
       :fncall (if (eq x.fn 'implies)
                   (append (dumb-conjunction-to-literals (car x.args))
                           (list (cadr x.args)))
                 (list (pseudo-term-fix x)))
       :otherwise (list (pseudo-term-fix x)))
     ///
     (defthm dumb-formula-to-clause-correct
       (iff (fgl-ev (disjoin (dumb-formula-to-clause x)) a)
            (fgl-ev x a))))

   (define dumb-negate-each ((x pseudo-term-listp))
     :returns (neg-x pseudo-term-listp)
     (if (atom x)
         nil
       (cons (dumb-negate (car x))
             (dumb-negate-each (cdr x))))
     ///
     (defthm disjoin-of-dumb-negate-each
       (iff (fgl-ev (disjoin (dumb-negate-each x)) a)
            (not (fgl-ev (conjoin x) a))))
     (defthm conjoin-of-dumb-negate-each
       (iff (fgl-ev (conjoin (dumb-negate-each x)) a)
            (not (fgl-ev (disjoin x) a)))))

   (defthm fgl-ev-of-disjoin-pseudo-term-list-fix
     (iff (fgl-ev (disjoin (pseudo-term-list-fix x)) a)
          (fgl-ev (disjoin x) a))
     :hints(("Goal" :induct (len x)
             :in-theory (enable pseudo-term-list-fix len))))

   (define dumb-disjoin-lit-lists ((x pseudo-term-listp)
                              (y pseudo-term-listp))
     :returns (disj pseudo-term-listp)
     (b* ((x (pseudo-term-list-fix x))
          (y (pseudo-term-list-fix y)))
       (if (or (equal x '('t))
               (equal y '('t)))
           '('t)
         (append x y)))
     ///
     (defthm dumb-disjoin-lit-lists-correct
       (iff (fgl-ev (disjoin (dumb-disjoin-lit-lists x y)) a)
            (or (fgl-ev (disjoin x) a)
                (fgl-ev (disjoin y) a)))
       :hints (("goal" :use ((:instance fgl-ev-of-disjoin-pseudo-term-list-fix
                              (x x))
                             (:instance fgl-ev-of-disjoin-pseudo-term-list-fix
                              (x y)))
                :in-theory (disable fgl-ev-of-disjoin-pseudo-term-list-fix)))))



   (defthm fgl-ev-of-conjoin-pseudo-term-list-fix
     (iff (fgl-ev (conjoin (pseudo-term-list-fix x)) a)
          (fgl-ev (conjoin x) a))
     :hints(("Goal" :induct (len x)
             :in-theory (enable pseudo-term-list-fix len))))

   (define dumb-conjoin-lit-lists ((x pseudo-term-listp)
                              (y pseudo-term-listp))
     :returns (disj pseudo-term-listp)
     (b* ((x (pseudo-term-list-fix x))
          (y (pseudo-term-list-fix y)))
       (if (or (equal x '('nil))
               (equal y '('nil)))
           '('nil)
         (append x y)))
     ///
     (defthm dumb-conjoin-lit-lists-correct
       (iff (fgl-ev (conjoin (dumb-conjoin-lit-lists x y)) a)
            (and (fgl-ev (conjoin x) a)
                 (fgl-ev (conjoin y) a)))
       :hints (("goal" :use ((:instance fgl-ev-of-conjoin-pseudo-term-list-fix
                              (x x))
                             (:instance fgl-ev-of-conjoin-pseudo-term-list-fix
                              (x y)))
                :in-theory (disable fgl-ev-of-conjoin-pseudo-term-list-fix)))))



   (defines dumb-flatten-disjunction
     (define dumb-flatten-disjunction ((x pseudo-termp))
       :returns (lits pseudo-term-listp)
       :measure (pseudo-term-count x)
       (pseudo-term-case x
         :fncall (b* (((when (and** (eq x.fn 'not)
                                    (eql (len x.args) 1)))
                       (dumb-negate-each (dumb-flatten-conjunction (first x.args))))
                      ((when (and** (eq x.fn 'implies)
                                    (eql (len x.args) 2)))
                       (dumb-disjoin-lit-lists (dumb-negate-each (dumb-flatten-conjunction (first x.args)))
                                               (dumb-flatten-disjunction (second x.args))))
                      ((unless (and** (eq x.fn 'if)
                                      (eql (len x.args) 3)))
                       (list (pseudo-term-fix x)))
                      ((when (and (equal (second x.args) ''nil)
                                  (equal (third x.args) ''t)))
                       (dumb-negate-each
                        (dumb-flatten-conjunction (first x.args))))
                      ((when (or (equal (first x.args) (second x.args))
                                 (equal (second x.args) ''t)))
                       (dumb-disjoin-lit-lists (dumb-flatten-disjunction (first x.args))
                                               (dumb-flatten-disjunction (third x.args)))))
                   (list (pseudo-term-fix x)))
         :const (if x.val
                    '('t)
                  nil)
         :otherwise (list (pseudo-term-fix x))))

     (define dumb-flatten-conjunction ((x pseudo-termp))
       :returns (lits pseudo-term-listp)
       :measure (pseudo-term-count x)
       :verify-guards nil
       (pseudo-term-case x
         :fncall (b* (((when (and** (eq x.fn 'not)
                                    (eql (len x.args) 1)))
                       (dumb-negate-each (dumb-flatten-disjunction (first x.args))))
                      ((unless (and** (eq x.fn 'if)
                                      (eql (len x.args) 3)))
                       (list (pseudo-term-fix x)))
                      ((when (and (equal (second x.args) ''nil)
                                  (equal (third x.args) ''t)))
                       (dumb-negate-each
                        (dumb-flatten-disjunction (first x.args))))
                      ((when (equal (third x.args) ''nil))
                       (dumb-conjoin-lit-lists (dumb-flatten-conjunction (first x.args))
                                               (dumb-flatten-conjunction (second x.args)))))
                   (list (pseudo-term-fix x)))
         :const (if x.val
                    nil
                  '('nil))
         :otherwise (list (pseudo-term-fix x))))
     ///
     (verify-guards dumb-flatten-disjunction)

     (defret-mutual dumb-flatten-disjunction-correct
       (defret dumb-flatten-disjunction-correct
         (iff (fgl-ev (disjoin (dumb-flatten-disjunction x)) a)
              (fgl-ev x a))
         :fn dumb-flatten-disjunction)
       (defret dumb-flatten-conjunction-correct
         (iff (fgl-ev (conjoin (dumb-flatten-conjunction x)) a)
              (fgl-ev x a))
         :fn dumb-flatten-conjunction))

     (fty::deffixequiv-mutual dumb-flatten-disjunction))

   (define dumb-flatten-clause ((x pseudo-term-listp))
     :returns (new-x pseudo-term-listp)
     (if (atom x)
         nil
       (dumb-disjoin-lit-lists (dumb-flatten-disjunction (car x))
                               (dumb-flatten-clause (cdr x))))
     ///
     (defthm dumb-flatten-clause-correct
       (iff (fgl-ev (disjoin (dumb-flatten-clause x)) a)
            (fgl-ev (disjoin x) a))))

   (define dumb-flatten-clause-proc ((x pseudo-term-listp))
     (list (dumb-flatten-clause x))
     ///
     (defthm dumb-flatten-clause-proc-correct
       (implies (and (pseudo-term-listp x)
                     (alistp a)
                     (fgl-ev (conjoin-clauses (dumb-flatten-clause-proc x)) a))
                (fgl-ev (disjoin x) a))
       :rule-classes :clause-processor))



   (define my-by-hint-cp ((clause pseudo-term-listp)
                          (hint)
                          state)
     :hooks nil
     (b* (((unless (symbolp hint))
           (value (list clause)))
          (thm (meta-extract-formula hint state))
          ((unless (pseudo-termp thm))
           (value (list clause)))
          (thm-clause (dumb-formula-to-clause (acl2::beta-reduce-full thm)))
          (reduced-clause (acl2::beta-reduce-full-list clause)))
       (if (equal reduced-clause thm-clause)
           (value nil)
         (b* ((state (f-put-global 'clause clause state))
              (state (f-put-global 'thm-clause thm-clause state))
              (state (f-put-global 'thm thm state)))
         (value (list clause)))))
     ///
     (defthm my-by-hint-cp-correct
       (implies (and (pseudo-term-listp clause)
                     (alistp a)
                     (fgl-ev-meta-extract-global-facts)
                     (fgl-ev (conjoin-clauses
                              (acl2::clauses-result (my-by-hint-cp clause hint state)))
                             a))
                (fgl-ev (disjoin clause) a))
       :hints (("goal" :use ((:instance fgl-ev-of-disjoin-beta-reduce-full-list
                              (x clause))
                             (:instance dumb-formula-to-clause-correct
                              (x (acl2::beta-reduce-full (meta-extract-formula hint state)))))
                :in-theory (disable ;; FGL-EV-META-EXTRACT-FORMULA
                                    dumb-formula-to-clause-correct
                                    fgl-ev-of-disjoin-beta-reduce-full-list)))
       :rule-classes :clause-processor))))

(local (defun fgl-interp-default-hint
         #!acl2 (fnname id wait-til-stablep world)
         (declare (xargs :mode :program))
         ;; copied mostly from just-expand.lisp, just-expand-mrec-default-hint,
         ;; added resolve-flags-cp and do-not-induct before expanding
         #!acl2
         (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
              (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
              (let* ((fns (acl2::recursivep fnname t world))
                     (expand-hints (just-expand-cp-parse-hints
                                    (just-expand-mrec-expanders fns world)
                                    world)))
                `(:computed-hint-replacement
                  ('(:clause-processor (mark-expands-cp clause '(t t ,expand-hints)))
                   (cmr::call-urewrite-clause-proc)
                   '(:clause-processor fgl::dumb-flatten-clause-proc)
                   '(:clause-processor (cmr::let-abstract-lits-clause-proc clause 'xxx))
                   (and (or (not ',wait-til-stablep) stable-under-simplificationp)
                        (expand-marked)))
                  :in-theory (disable . ,fns)
                  :do-not-induct t
                  :clause-processor (cmr::resolve-flags-cp
                                     clause
                                     ',(cons 'fgl::flag fns)))))))

(defsection stack-isomorphic-of-fgl-interp



  ;; (defret major-stack-scratch-isomorphic-of-syntax-bind
  ;;   (interp-st-scratch-isomorphic new-interp-st interp-st)
  ;;   :hints(("Goal" :in-theory (enable fgl-interp-syntax-bind)))
  ;;   :fn fgl-interp-syntax-bind)

  (defret major-stack-scratch-isomorphic-of-relieve-hyp-synp
    (interp-st-scratch-isomorphic new-interp-st
      interp-st)
    :hints(("Goal" :in-theory (enable fgl-rewrite-relieve-hyp-synp)))
    :fn fgl-rewrite-relieve-hyp-synp)


  (defthmd stack$a-update-scratch-in-terms-of-push-pop
    (implies (syntaxp (quotep n))
             (equal (stack$a-update-scratch n obj stack)
                    (if (zp n)
                        (stack$a-push-scratch obj (stack$a-pop-scratch stack))
                      (stack$a-push-scratch (stack$a-top-scratch stack)
                                            (stack$a-update-scratch
                                             (1- n) obj (stack$a-pop-scratch stack))))))
    :hints(("Goal" :in-theory (enable stack$a-update-scratch
                                      stack$a-push-scratch
                                      stack$a-pop-scratch
                                      stack$a-top-scratch))))

  (encapsulate nil
    (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))
    (with-output
      :off (event)
      :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
      (std::defret-mutual-generate interp-st-scratch-isomorphic-of-<fn>
        :return-concls ((new-interp-st               (interp-st-scratch-isomorphic new-interp-st
                                                                                   (double-rewrite interp-st))))
        :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
                (let ((flag (find-flag-is-hyp clause)))
                  (and flag
                       (prog2$ (cw "flag: ~x0~%" flag)
                               '(:no-op t)))))
        :mutual-recursion fgl-interp))))



(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (std::defret-mutual len-of-fgl-interp-arglist
    (defret len-of-fgl-interp-arglist
      (equal (len arg-objs) (len args))
      :fn fgl-interp-arglist)
    :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
    :mutual-recursion fgl-interp
    :skip-others t))

(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (std::defret-mutual len-of-fgl-interp-arglist
    (defret len-of-fgl-interp-lambda-arglist
      (equal (len arg-objs) (len args))
      :fn fgl-interp-lambda-arglist)
    :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
    :mutual-recursion fgl-interp
    :skip-others t))

(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (std::defret-mutual true-listp-of-fgl-interp-arglist
    (defret true-listp-of-fgl-interp-arglist
      (true-listp arg-objs)
      :fn fgl-interp-arglist
      :rule-classes :type-prescription)
    :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
    :mutual-recursion fgl-interp
    :skip-others t))

(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (std::defret-mutual true-listp-of-fgl-interp-lambda-arglist
    (defret true-listp-of-fgl-interp-lambda-arglist
      (true-listp arg-objs)
      :fn fgl-interp-lambda-arglist
      :rule-classes :type-prescription)
    :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
    :mutual-recursion fgl-interp
    :skip-others t))


(defthm stack$a-pop-scratch-of-stack$a-update-0
  (equal (stack$a-pop-scratch (stack$a-update-scratch 0 obj stack))
         (stack$a-pop-scratch stack))
  :hints(("Goal" :in-theory (enable stack$a-pop-scratch stack$a-update-scratch))))

(defthm stack$a-top-scratch-of-stack$a-update-0
  (equal (stack$a-top-scratch (stack$a-update-scratch 0 obj stack))
         (scratchobj-fix obj))
  :hints(("Goal" :in-theory (enable stack$a-top-scratch stack$a-update-scratch))))

(local (in-theory (disable BFR-LISTP$-WHEN-SUBSETP-EQUAL
                           acl2::subsetp-append1
                           acl2::subsetp-of-cons
                           acl2::subsetp-trans2)))

(local (defthm len-update-nth-when-less
         (implies (< (nfix n) (len x))
                  (equal (len (update-nth n v x))
                         (len x)))))

(local (defthm stack$a-nth-scratch-of-stack$a-update-scratch
         (implies (< (nfix n) (stack$a-scratch-len stack))
                  (equal (stack$a-nth-scratch m (stack$a-update-scratch n val stack))
                         (if (equal (nfix n) (nfix m))
                             (scratchobj-fix val)
                           (stack$a-nth-scratch m stack))))
         :hints(("Goal" :in-theory (e/d (stack$a-nth-scratch
                                         stack$a-scratch-len
                                         stack$a-update-scratch
                                         minor-stack-scratch-len)
                                        (len-update-nth))
                 :expand ((:free (stack) (major-stack-nth-scratch m stack))
                          (:free (stack) (minor-stack-nth-scratch m stack)))))))



(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate interp-st-bfrs-ok-of-<fn>
      :rules
      ((t (:add-bindings
           ((?new-logicman (interp-st->logicman new-interp-st))
            (?logicman (interp-st->logicman interp-st)))))
       ((or (:fnname fgl-rewrite-try-rules)
            (:fnname fgl-rewrite-try-rule)
            (:fnname fgl-rewrite-try-rewrite)
            (:fnname fgl-rewrite-try-meta)
            (:fnname fgl-rewrite-binder-try-rules)
            (:fnname fgl-rewrite-binder-try-rule)
            (:fnname fgl-rewrite-binder-try-rewrite)
            (:fnname fgl-rewrite-binder-try-meta)
            (:fnname fgl-rewrite-try-rules3))
        (:add-hyp (scratchobj-case (stack$a-top-scratch (double-rewrite (interp-st->stack interp-st)))
                    :fgl-objlist))))
      :formal-hyps    ;; generates hypotheses
      (((interp-st-bfr-p x)           (lbfr-p x logicman))
       ((fgl-object-p x)              (lbfr-listp (fgl-object-bfrlist x) logicman))
       ((fgl-objectlist-p x)          (lbfr-listp (fgl-objectlist-bfrlist x) logicman))
       ((fgl-object-bindings-p x)     (lbfr-listp (fgl-object-bindings-bfrlist x) logicman))
       (interp-st                     (interp-st-bfrs-ok interp-st))
       ((constraint-instancelist-p x) (lbfr-listp (constraint-instancelist-bfrlist x) logicman)))
      :return-concls  ;; generates conclusions
      ((xbfr                          (lbfr-p xbfr new-logicman))
       ((fgl-object-p x)              (lbfr-listp (fgl-object-bfrlist x) new-logicman))
       ((fgl-objectlist-p x)          (lbfr-listp (fgl-objectlist-bfrlist x) new-logicman))
       (new-interp-st                 (interp-st-bfrs-ok new-interp-st)))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
              `(:do-not-induct t
                ;; :clause-processor (cmr::resolve-flags-cp clause
                ;;                                         (cons 'acl2::flag
                ;;                                               ',(acl2::fgetprop 'fgl-interp-test 'recursivep nil (w state))))
                )
              (let ((flag (find-flag-is-hyp clause)))
                (and flag
                     (prog2$ (cw "flag: ~x0~%" flag)
                             '(:no-op t)))))
      :mutual-recursion fgl-interp)))




;; This was an attempted hack to get enough lemmas so as not to have to rely on
;; bfr-listp-when-not-member-witness reasoning to relieve the hyps of our
;; induction hyps.  But it doesn't seem to work.  I'm going to leave it here
;; commented out in order to preserve the idea.
(make-event
 (let ((event '(local
                (defsection interp-st-bfrs-ok-lemmas
                  (local
                   (make-event
                    (b* ((state (f-put-global 'interp-st-bfrs-ok-lemma-clauses nil state)))
                      (value '(value-triple :invisible)))))

                  (set-tau-auto-mode nil)
                  (local (defund hyp-marker (x) x))
                  (local (in-theory (disable (:t hyp-marker))))
                  (local (defcong iff iff (hyp-marker x) 1 :hints(("Goal" :in-theory (enable hyp-marker)))))
                  (local (defthm remove-hyp-marker
                           (implies (acl2::rewriting-negative-literal `(hyp-marker ,x))
                                    (iff (hyp-marker x) x))
                           :hints(("Goal" :in-theory (enable hyp-marker)))))

                  (local (in-theory (disable bfr-listp-when-not-member-witness
                                             ;; INTERP-ST-BFRS-OK-UPDATER-INDEPENDENCE
                                             ;; INTERP-ST-BFRS-OK-OF-UPDATE-STACK
                                             )))
                  (local (defstub dummy-concl (x) t))

                  (local
                   (make-event
                    '(:or
                      (with-output
                        :off (event prove)
                        :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
                        (std::defret-mutual-generate interp-st-bfrs-ok-of-<fn>
                          :formal-hyps
                          (((interp-st-bfr-p x)           (hyp-marker (lbfr-p x (interp-st->logicman interp-st))))
                           ((fgl-object-p x)               (hyp-marker (lbfr-listp (fgl-object-bfrlist x) (interp-st->logicman interp-st))))
                           ((fgl-objectlist-p x)           (hyp-marker (lbfr-listp (fgl-objectlist-bfrlist x) (interp-st->logicman interp-st))))
                           ((fgl-object-bindings-p x)     (hyp-marker (lbfr-listp (fgl-object-bindings-bfrlist x) (interp-st->logicman interp-st))))
                           (interp-st                     (hyp-marker (interp-st-bfrs-ok interp-st)))
                           ((constraint-instancelist-p x) (hyp-marker (lbfr-listp (constraint-instancelist-bfrlist x) (interp-st->logicman interp-st)))))

                          :rules
                          ((t (:add-concl ;; (equal (w new-state) (w state))
                               (dummy-concl new-interp-st)))
                           ;; (t (:add-keyword :hints ('(:do-not-induct t)
                           ;;                          (let ((flag (find-flag-is-hyp clause)))
                           ;;                            (and flag
                           ;;                                 (prog2$ (cw "flag: ~x0~%" flag)
                           ;;                                         '(:no-op t)))))))
                           ((or (:fnname fgl-rewrite-try-rules)
                                (:fnname fgl-rewrite-try-rule)
                                (:fnname fgl-rewrite-try-rewrite)
                                (:fnname fgl-rewrite-try-meta)
                                (:fnname fgl-rewrite-binder-try-rules)
                                (:fnname fgl-rewrite-binder-try-rule)
                                (:fnname fgl-rewrite-binder-try-rewrite)
                                (:fnname fgl-rewrite-binder-try-meta)
                                (:fnname fgl-rewrite-try-rules3))
                            (:add-hyp (hyp-marker (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-objlist)))))

                          :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
                                  (let ((flag (find-flag-is-hyp clause)))
                                    (and flag
                                         (prog2$ (cw "flag: ~x0~%" flag)
                                                 '(:no-op t))))
                                  (if stable-under-simplificationp
                                      (let ((state (f-put-global
                                                    'interp-st-bfrs-ok-lemma-clauses
                                                    (cons clause (@ interp-st-bfrs-ok-lemma-clauses))
                                                    state)))
                                        (value '(:by nil)))
                                    (value nil)))
                          :mutual-recursion fgl-interp
                          ;; :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
                          ))
                      (value-triple :clauses-generated))))

                  (local (defun process-bfrs-ok-clause (clause hyps)
                           ;; returns (mv thms hyps)
                           (declare (xargs :mode :program))
                           (if (atom clause)
                               (mv nil hyps)
                             (let ((lit (car clause)))
                               (case-match lit
                                 (('not ('acl2::flag-is &))
                                  (process-bfrs-ok-clause (cdr clause) hyps))
                                 (('equal ('w &) ('w &)) (process-bfrs-ok-clause (cdr clause) hyps))
                                 (('not ('equal ('w &) ('w &))) (process-bfrs-ok-clause (cdr clause) hyps))
                                 (('dummy-concl &) (process-bfrs-ok-clause (cdr clause) hyps))
                                 (('not ('dummy-concl &)) (process-bfrs-ok-clause (cdr clause) hyps))
                                 (('hyp-marker x)
                                  (b* (((mv thms hyps) (process-bfrs-ok-clause (cdr clause) hyps)))
                                    (mv (cons (append hyps (list x)) thms) hyps)))
                                 (& (process-bfrs-ok-clause (cdr clause) (cons (car clause) hyps))))))))

                  (local (defun process-bfrs-ok-clauses (clauses)
                           (declare (xargs :mode :program))
                           (if (atom clauses)
                               nil
                             (b* (((mv thms &) (process-bfrs-ok-clause (car clauses) nil)))
                               (append thms (process-bfrs-ok-clauses (cdr clauses)))))))

                  (local (make-event
                          (b* ((state (f-put-global 'interp-st-bfrs-ok-lemma-thm-clauses
                                                    (acl2::subsumption-replacement-loop
                                                     (acl2::merge-sort-length
                                                      (process-bfrs-ok-clauses (@ interp-st-bfrs-ok-lemma-clauses)))
                                                     nil nil)
                                                    state)))
                            (value '(value-triple :thms-generated)))))

                  (local (in-theory (enable bfr-listp-when-not-member-witness)))

                  (local (defun name-and-record-thms (thms n w)
                           (declare (xargs :mode :program))
                           (if (atom thms)
                               nil
                             (cons `(defthm ,(intern-in-package-of-symbol
                                              (concatenate 'string
                                                           "INTERP-ST-BFRS-OK-LEMMA-" (str::natstr n))
                                              'foo)
                                      ,(acl2::prettyify-clause (car thms) t w))
                                   (name-and-record-thms (cdr thms) (+ 1 n) w)))))

                  (make-event
                   (cons 'progn
                         (name-and-record-thms (@ interp-st-bfrs-ok-lemma-thm-clauses) 0 (w state))))))))
   (declare (ignore event))
   '(value-triple :skipped)))




(defthm pathcond-enabledp-of-interp-st-pathcond-rewind
  (iff (nth *pathcond-enabledp* (pathcond-rewind mode pathcond))
       (nth *pathcond-enabledp* pathcond))
  :hints(("Goal" :in-theory (e/d (pathcond-rewind) (nth-add1 nth update-nth)))))



(local (in-theory (disable nth update-nth)))

(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond-enabledp
      :rules ((t (:add-concl ;; (implies t ;; (not (fgl-interp-real-errorp err))
                                      (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
                                            (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t :expand :lambdas)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '( :expand :lambdas))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))








(def-updater-independence-thm logicman-pathcond-eval-checkpoints!-of-interp-st-logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                (logicman-pathcond-p pathcond (interp-st->logicman old)))
           (equal (logicman-pathcond-eval-checkpoints! env pathcond (interp-st->logicman new))
                  (logicman-pathcond-eval-checkpoints! env pathcond (interp-st->logicman old)))))



(def-updater-independence-thm logicman-pathcond-eval-checkpoints-of-interp-st-logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                (logicman-pathcond-p pathcond (interp-st->logicman old)))
           (equal (logicman-pathcond-eval-checkpoints env pathcond (interp-st->logicman new))
                  (logicman-pathcond-eval-checkpoints env pathcond (interp-st->logicman old)))))



(defret logicman-pathcond-eval-checkpoints!-of-interp-st-pathcond-assume
  (implies (and (not contra)
                (equal (logicman->mode (interp-st->logicman interp-st)) (logicman->mode logicman1)))
           (equal (logicman-pathcond-eval-checkpoints! env (interp-st->pathcond new-interp-st) logicman1)
                  (maybe-cons (nth *pathcond-enabledp* (interp-st->pathcond interp-st))
                              (logicman-pathcond-eval env (interp-st->pathcond new-interp-st) logicman1)
                              (logicman-pathcond-eval-checkpoints! env (interp-st->pathcond interp-st) logicman1))))
  :hints(("Goal" :in-theory (e/d (interp-st-pathcond-assume)
                                 (logicman-pathcond-eval-checkpoints!))))
  :fn interp-st-pathcond-assume)



(def-updater-independence-thm logicman->mode-of-interp-st-logicman-extension
  (implies (logicman-extension-p (interp-st->logicman new)
                                 (interp-st->logicman old))
           (equal (logicman->mode (interp-st->logicman new))
                  (logicman->mode (interp-st->logicman old)))))

(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-logicman->mode
      :rules ((t (:add-concl (equal (logicman->mode (interp-st->logicman new-interp-st))
                                    (logicman->mode (interp-st->logicman interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))




(defret pathcond-rewind-stack-len-of-interp-st-pathcond-assume-maybe
  (implies (and (equal mode (interp-st-bfr-mode interp-st))
                (not contra))
           (equal (pathcond-rewind-stack-len mode (interp-st->pathcond new-interp-st))
                  (maybe-incr (nth *pathcond-enabledp* (interp-st->pathcond interp-st))
                              (pathcond-rewind-stack-len mode (interp-st->pathcond interp-st)))))
  :hints(("Goal" :in-theory (enable interp-st-pathcond-assume)))
  :fn interp-st-pathcond-assume)




(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond-stack-length
      :rules ((t (:add-concl (implies (and ;; (not (fgl-interp-real-errorp err))
                                           (equal mode (logicman->mode (interp-st->logicman interp-st))))
                                      (equal (pathcond-rewind-stack-len
                                              mode
                                              (interp-st->pathcond new-interp-st))
                                             (pathcond-rewind-stack-len
                                              mode (interp-st->pathcond interp-st)))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))


(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond-rewind-ok
      :rules ((t (:add-concl (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
                                      (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
                                           (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints (("goal" :do-not-induct t :in-theory (enable pathcond-rewind-ok)))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))



(local (defret pathcond-rewind-ok-of-interp-st-pathcond-assume
         (implies (and (not contra)
                       (equal bfr-mode (logicman->mode (interp-st->logicman interp-st))))
                  (pathcond-rewind-ok bfr-mode (interp-st->pathcond new-interp-st)))
         :hints(("Goal" :in-theory (enable interp-st-pathcond-assume pathcond-rewind-ok
                                           maybe-incr)))
         :fn interp-st-pathcond-assume))

(local (acl2::use-trivial-ancestors-check))


(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (fgl-interp-real-errorp err))
                  (equal (logicman-pathcond-eval-checkpoints!
                          env
                          (interp-st->pathcond new-interp-st)
                          (interp-st->logicman new-interp-st))
                         (logicman-pathcond-eval-checkpoints!
                          env
                          (interp-st->pathcond interp-st)
                          (interp-st->logicman interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-objlist))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))

(defsection pathcond-eval-preserved

  (local
   (defthm pathcond-eval-equal-when-eval-checkpoints!-equal
     (implies (and (equal evals (logicman-pathcond-eval-checkpoints! env pathcond logicman))
                   (bind-free
                    ;; (prog2$ (cw "Evals: ~x0~%" evals)
                            (case-match evals
                              (('logicman-pathcond-eval-checkpoints! prev-env prev-pathcond prev-logicman)
                               (and (equal prev-env env)
                                    (not (equal pathcond prev-pathcond))
                                    `((prev-pathcond . ,prev-pathcond)
                                      (prev-logicman . ,prev-logicman))))
                              (& nil)))
                   ;; (syntaxp (prog2$ (cw "prev-pathcond: ~x0~%prev-logicman: ~x1~%" prev-pathcond prev-logicman)
                   ;;                  t))
                   (equal evals (logicman-pathcond-eval-checkpoints! env prev-pathcond prev-logicman))
                   (iff* (pathcond-enabledp pathcond) (pathcond-enabledp prev-pathcond)))
              (equal (logicman-pathcond-eval env pathcond logicman)
                     (logicman-pathcond-eval env prev-pathcond prev-logicman)))
     :hints (("Goal" :in-theory (enable logicman-pathcond-eval-checkpoints! iff*)))))

  (defthm logicman-pathcond-eval-of-fgl-primitive-fncall-stub
    (b* (((mv ?successp ?ans ?new-interp-st ?new-state)
          (fgl-primitive-fncall-stub primfn fn args interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval env (interp-st->pathcond new-interp-st)
                                              (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                              (interp-st->logicman interp-st))))))

  (defthm logicman-pathcond-eval-of-fgl-meta-fncall-stub
    (b* (((mv ?successp ?rhs ?bindings ?new-interp-st ?new-state)
          (fgl-meta-fncall-stub metafn fn args interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval env (interp-st->pathcond new-interp-st)
                                              (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                              (interp-st->logicman interp-st))))))

  (defthm logicman-pathcond-eval-of-fgl-binder-fncall-stub
    (b* (((mv ?successp ?rhs ?bindings ?rhs-contexts ?new-interp-st ?new-state)
          (fgl-binder-fncall-stub metafn fn args interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval env (interp-st->pathcond new-interp-st)
                                              (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                              (interp-st->logicman interp-st))))))


  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond-eval
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (fgl-interp-real-errorp err))
                  (equal (logicman-pathcond-eval
                          env
                          (interp-st->pathcond new-interp-st)
                          (interp-st->logicman new-interp-st))
                         (logicman-pathcond-eval
                          env
                          (interp-st->pathcond interp-st)
                          (interp-st->logicman interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (stack$a-top-scratch (double-rewrite (interp-st->stack interp-st))) :fgl-objlist))))
      :hints (("goal" :do-not-induct t))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))

(local (defthm not-member-of-append
         (implies (and (not (member v a))
                       (not (member v b)))
                  (not (member v (append a b))))))

(local (in-theory (disable not
                           ;; acl2::member-of-cons
                           acl2::member-equal-append
                           acl2::member-of-append
                           bfr-listp$-of-append)))

(defsection constraint-eval-tightens

  (local (defret logicman-pathcond-eval-of-assume-tightens
           (implies (not (logicman-pathcond-eval env pathcond logicman))
                    (not (logicman-pathcond-eval env new-pathcond logicman)))
           :hints (("goal" :cases (contradictionp))
                   (and stable-under-simplificationp
                        '(:cases ((pathcond-enabledp pathcond)))))
           :fn logicman-pathcond-assume))

  (local (def-updater-independence-thm logicman-pathcond-eval-of-interp-st-logicman-extension
           (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                         (logicman-pathcond-p pathcond (interp-st->logicman old)))
                    (equal (logicman-pathcond-eval env pathcond (interp-st->logicman new))
                           (logicman-pathcond-eval env pathcond (interp-st->logicman old))))))



  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-constraint-eval-tightens
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (fgl-interp-real-errorp err))
                  (implies (not (logicman-pathcond-eval
                                 env
                                 (interp-st->constraint interp-st)
                                 (interp-st->logicman interp-st)))
                           (not (logicman-pathcond-eval
                                 env
                                 (interp-st->constraint new-interp-st)
                                 (interp-st->logicman new-interp-st)))))
                 (:add-keyword :hints ('(:do-not-induct t :expand ((:free (x) (hide x))))
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-objlist))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp))

  (define interp-st-constraint-ok (interp-st env)
    :verify-guards nil
    (stobj-let ((constraint-pathcond (interp-st->constraint interp-st))
                (logicman (interp-st->logicman interp-st)))
               (ok)
               (logicman-pathcond-eval env constraint-pathcond logicman)
               ok))

  (local (in-theory (enable interp-st-constraint-ok)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-constraint-eval-tightens-rw
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (fgl-interp-real-errorp err))
                  (let ((eval (logicman-pathcond-eval
                                 env
                                 (interp-st->constraint new-interp-st)
                                 (interp-st->logicman new-interp-st))))
                    (iff* eval
                          (and* (logicman-pathcond-eval
                                 env
                                 (interp-st->constraint interp-st)
                                 (interp-st->logicman interp-st))
                                (interp-st-constraint-ok new-interp-st env))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st))) :fgl-objlist))))
      :hints (("goal" :do-not-induct t :expand ((:free (x) (hide x)))
               :in-theory (enable iff* and*)))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))



(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-reclimit
      :rules ((t (:add-concl (acl2::nat-equiv
                              (interp-st->reclimit new-interp-st)
                              (interp-st->reclimit interp-st)))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))

(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-reclimit-natp
      :rules ((t (:add-concl (implies (natp (interp-st->reclimit interp-st))
                                      (natp (interp-st->reclimit new-interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))



(defret return-values-correct-of-interp-st-add-term-bvar-unique
  (equal (list . <values>)
         <call>)
  :hints(("Goal" :in-theory (enable interp-st-add-term-bvar-unique)))
  :fn interp-st-add-term-bvar-unique)

(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-return-values-correct
      :rules (((not (or (:fnname fgl-interp-bindinglist)
                        (:fnname fgl-interp-add-constraints)
                        (:fnname fgl-interp-add-constraints-for-substs)))
               (:add-concl (equal (list . <values>)
                                  <call>))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
              (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))
      :mutual-recursion fgl-interp)))

(local (in-theory (disable w)))

(defsection fgl-interp-preserves-w-state
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-w-state
      :rules ((t (:add-concl (equal (w new-state) (w state)))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))

(defsection fgl-interp-term-guards
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (local (in-theory (disable w)))

  (local (defthm bfr-varname-p-of-get-term->bvar$a
           (b* ((bvar-db (interp-st->bvar-db interp-st))
                (logicman (interp-st->logicman interp-st))
                (bvar (get-term->bvar$a obj bvar-db)))
             (implies (and (interp-st-bfrs-ok interp-st)
                           bvar)
                      (bfr-varname-p bvar logicman)))
           :hints(("Goal" :in-theory (enable interp-st-bfrs-ok bfr-varname-p)))))

  (local
   (defthm len-cinstlist-when-scratchobj-isomorphic-rw
     (implies (and (scratchobj-isomorphic y (double-rewrite x))
                   (syntaxp (not (equal y x)))
                   (scratchobj-case y :cinstlist))
              (equal (len (scratchobj-cinstlist->val x))
                     (len (scratchobj-cinstlist->val y))))))

  (local
   (defthm len-fgl-objlist-when-scratchobj-isomorphic-rw
     (implies (and (scratchobj-isomorphic y (double-rewrite x))
                   (syntaxp (not (equal y x)))
                   (scratchobj-case y :fgl-objlist))
              (equal (len (scratchobj-fgl-objlist->val x))
                     (len (scratchobj-fgl-objlist->val y))))))


  ;; (local (defthm pseudo-fnsym-p-of-rewrite-rule->equiv
  ;;          (implies (pseudo-rewrite-rule-p rule)
  ;;                   (pseudo-fnsym-p (acl2::rewrite-rule->equiv rule)))
  ;;          :hints(("Goal" :in-theory (enable pseudo-rewrite-rule-p
  ;;                                            pseudo-fnsym-p)))))

  ;; ugh
  (local (defthm booleanp-of-interp-st-pathcond-enabledp
           (implies (interp-stp interp-st)
                    (booleanp (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))
           :hints(("Goal" :in-theory (enable interp-stp pathcondp interp-st->pathcond)))
           :rule-classes :type-prescription))

  ;; (local (defthm pseudo-rewrite-rule-listp-of-and*
  ;;          (implies (pseudo-rewrite-rule-listp x)
  ;;                   (pseudo-rewrite-rule-listp (and* cond x)))
  ;;          :hints(("Goal" :in-theory (enable and*)))))

  (local (defthm symbolp-by-pseudo-term-kind
           (implies (and (equal (pseudo-term-kind x) :var)
                         (pseudo-termp x))
                    (symbolp x))
           :hints(("Goal" :in-theory (enable pseudo-term-kind pseudo-termp)))))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (verify-guards fgl-interp-term
      :guard-debug t)))




(define minor-stack-equiv-except-top-debug ((x minor-stack-p)
                                            (y minor-stack-p))
  (b* (((minor-frame x1) (car x))
       ((minor-frame y1) (car y)))
    (and (equal x1.bindings y1.bindings)
         (equal x1.scratch y1.scratch)
         (mbe :logic (and (minor-stack-equiv (cdr x) (cdr y))
                      (iff (consp (cdr x)) (consp (cdr y))))
          :exec (if (atom (cdr x))
                    (atom (cdr y))
                  (and (consp (cdr y))
                       (minor-stack-equiv (cdr x) (cdr y)))))))

  ///
  (defequiv minor-stack-equiv-except-top-debug)




  (defthm minor-stack-equiv-except-top-debug-implies-len-equal
    (implies (minor-stack-equiv-except-top-debug x y)
             (equal (len (minor-stack-fix x)) (len (minor-stack-fix y))))
    :hints(("Goal" :use ((:instance len-of-minor-stack-fix (x (cdr x)))
                         (:instance len-of-minor-stack-fix (x (cdr y)))
                         (:instance len-of-minor-stack-fix (x x))
                         (:instance len-of-minor-stack-fix (x y)))
            :in-theory (e/d (len) (len-of-minor-stack-fix))))
    :rule-classes :congruence)

  (defcong minor-stack-equiv-except-top-debug
    minor-stack-equiv-except-top-debug
    (fgl-minor-stack-concretize stack env logicman) 1
    :hints(("Goal" :in-theory (enable fgl-minor-stack-concretize fgl-minor-frame-concretize)))))



(define stack-equiv-except-top-bindings ((x major-stack-p)
                                         (y major-stack-p))

  (b* (((major-frame x1) (car x))
       ((major-frame y1) (car y)))
    (and ;;(ec-call (fgl-bindings-extension-p x1.bindings y1.bindings))
     ;; (equal x1.debug y1.debug)
     (minor-stack-equiv-except-top-debug x1.minor-stack y1.minor-stack)
     (mbe :logic (and (major-stack-equiv (cdr x) (cdr y))
                      (iff (consp (cdr x)) (consp (cdr y))))
          :exec (if (atom (cdr x))
                    (atom (cdr y))
                  (and (consp (cdr y))
                       (major-stack-equiv (cdr x) (cdr y)))))))
  ///
  (defequiv stack-equiv-except-top-bindings)

  (local (defthm len-equal-when-major-stack-fix
           (implies (and (equal (major-stack-fix x) (major-stack-fix y))
                         (consp x) (consp y))
                    (equal (equal (len x) (len y)) t))
           :hints (("Goal" :use ((:instance len-of-major-stack-fix)
                                 (:instance len-of-major-stack-fix (x y)))
                    :in-theory (disable len-of-major-stack-fix)))))

  (local (defthm equal-+-1
           (equal (equal (+ 1 x) (+ 1 y))
                  (equal (fix x) (fix y)))))

  (defcong stack-equiv-except-top-bindings equal (stack$a-frames x) 1
    :hints(("Goal" :in-theory (enable stack$a-frames len))))

  (defcong stack-equiv-except-top-bindings equal (stack$a-minor-frames x) 1
    :hints(("Goal" :in-theory (e/d (stack$a-minor-frames)
                                   (minor-stack-equiv-except-top-debug-implies-len-equal))
            :use ((:instance minor-stack-equiv-except-top-debug-implies-len-equal
                   (x (major-frame->minor-stack (car x)))
                   (y (major-frame->minor-stack (car x-equiv))))))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (fgl-major-stack-concretize stack env logicman) 1
    :hints(("Goal" :in-theory (enable fgl-major-stack-concretize fgl-major-frame-concretize))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (stack$a-pop-scratch stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch
                                      minor-stack-equiv-except-top-debug))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (stack$a-set-rule debug stack) 2
    :hints(("Goal" :in-theory (enable stack$a-set-rule))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (stack$a-set-phase debug stack) 2
    :hints(("Goal" :in-theory (enable stack$a-set-phase))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (stack$a-pop-minor-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame
                                      minor-stack-equiv-except-top-debug))))

  (defcong stack-equiv-except-top-bindings
    equal
    (stack$a-pop-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-frame
                                      major-stack-fix default-car))))


  (defthm stack-equiv-except-top-bindings-of-add-binding
    (stack-equiv-except-top-bindings
     (fgl-major-stack-concretize
      (stack$a-add-binding var obj stack) env logicman)
     (fgl-major-stack-concretize
      stack env logicman))
    :hints(("Goal" :in-theory (enable stack$a-add-binding
                                      fgl-major-stack-concretize
                                      fgl-major-frame-concretize))))

  (defret stack-equiv-except-top-bindings-of-fgl-rewrite-relieve-hyp-synp
    (implies (equal logicman (interp-st->logicman new-interp-st))
             (stack-equiv-except-top-bindings
              (fgl-major-stack-concretize
               (interp-st->stack new-interp-st)
               env logicman)
              (fgl-major-stack-concretize
               (interp-st->stack interp-st)
               env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable fgl-rewrite-relieve-hyp-synp
                                      stack$a-set-bindings
                                      fgl-major-stack-concretize
                                      fgl-major-frame-concretize)))
    :fn fgl-rewrite-relieve-hyp-synp)

  (defthm stack-equiv-except-top-bindings-of-set-rule
    (stack-equiv-except-top-bindings (stack$a-set-rule rule stack)
                                     stack)
    :hints(("Goal" :in-theory (enable stack$a-set-rule major-stack-fix default-car))))

  (defthm stack-equiv-except-top-bindings-of-set-phase
    (stack-equiv-except-top-bindings (stack$a-set-phase phase stack)
                                     stack)
    :hints(("Goal" :in-theory (enable stack$a-set-phase major-stack-fix default-car))))

  (defthm stack-equiv-except-top-bindings-of-stack$a-set-term-index
    (stack-equiv-except-top-bindings (stack$a-set-term-index val stack)
                                     stack)
    :hints(("Goal" :in-theory (enable stack$a-set-term-index
                                      minor-stack-equiv-except-top-debug
                                      major-stack-fix default-car))))

  (defthm stack-equiv-except-top-bindings-of-stack$a-set-term
    (stack-equiv-except-top-bindings (stack$a-set-term val stack)
                                     stack)
    :hints(("Goal" :in-theory (enable stack$a-set-term
                                      minor-stack-equiv-except-top-debug
                                      major-stack-fix default-car)))))


(define minor-stack-equiv-except-top-bindings ((x minor-stack-p)
                                               (y minor-stack-p))

  (b* (((minor-frame x1) (car x))
       ((minor-frame y1) (car y)))
    (and ;;(ec-call (fgl-bindings-extension-p x1.bindings y1.bindings))
     ;;(equal x1.debug y1.debug)
     (scratchlist-equiv x1.scratch y1.scratch)
     (mbe :logic (and (minor-stack-equiv (cdr x) (cdr y))
                      (iff (consp (cdr x)) (consp (cdr y))))
          :exec (if (atom (cdr x))
                    (atom (cdr y))
                  (and (consp (cdr y))
                       (minor-stack-equiv (cdr x) (cdr y)))))))
  ///
  (defequiv minor-stack-equiv-except-top-bindings)
  (defrefinement minor-stack-equiv-except-top-debug minor-stack-equiv-except-top-bindings
    :hints(("Goal" :in-theory (enable minor-stack-equiv-except-top-debug)))))

(define stack-equiv-except-top-major/minor-bindings ((x major-stack-p)
                                                     (y major-stack-p))

  (b* (((major-frame x1) (car x))
       ((major-frame y1) (car y)))
    (and ;;(ec-call (fgl-bindings-extension-p x1.bindings y1.bindings))
     ;; (equal x1.debug y1.debug)
     (minor-stack-equiv-except-top-bindings x1.minor-stack y1.minor-stack)
     (mbe :logic (and (major-stack-equiv (cdr x) (cdr y))
                      (iff (consp (cdr x)) (consp (cdr y))))
          :exec (if (atom (cdr x))
                    (atom (cdr y))
                  (and (consp (cdr y))
                       (major-stack-equiv (cdr x) (cdr y)))))))
  ///
  (defequiv stack-equiv-except-top-major/minor-bindings)
  (local (in-theory (enable minor-stack-equiv-except-top-bindings)))

  (local (defthm len-equal-when-major-stack-fix
           (implies (and (equal (major-stack-fix x) (major-stack-fix y))
                         (consp x) (consp y))
                    (equal (equal (len x) (len y)) t))
           :hints (("Goal" :use ((:instance len-of-major-stack-fix)
                                 (:instance len-of-major-stack-fix (x y)))
                    :in-theory (disable len-of-major-stack-fix)))))

  (local (defthm equal-+-1
           (equal (equal (+ 1 x) (+ 1 y))
                  (equal (fix x) (fix y)))))

  (defcong stack-equiv-except-top-major/minor-bindings equal (stack$a-frames x) 1
    :hints(("Goal" :in-theory (enable stack$a-frames len))))

  (defcong stack-equiv-except-top-major/minor-bindings equal (stack$a-minor-frames x) 1
    :hints(("Goal" :in-theory (enable stack$a-minor-frames len))))

  (defcong stack-equiv-except-top-major/minor-bindings
    stack-equiv-except-top-major/minor-bindings
    (fgl-major-stack-concretize stack env logicman) 1
    :hints(("Goal" :in-theory (enable fgl-major-stack-concretize fgl-major-frame-concretize fgl-minor-stack-concretize fgl-minor-frame-concretize))))

  (defcong stack-equiv-except-top-major/minor-bindings
    stack-equiv-except-top-major/minor-bindings
    (stack$a-pop-scratch stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defcong stack-equiv-except-top-major/minor-bindings
    equal
    (stack$a-pop-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-frame
                                      major-stack-fix default-car))))

  (defthm stack-equiv-except-top-major/minor-bindings-of-stack$a-add-minor-bindings
    (stack-equiv-except-top-major/minor-bindings
     (stack$a-add-minor-bindings bindings stack)
     stack)
  :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings
                                    major-stack-fix default-car))))

  (defcong stack-equiv-except-top-major/minor-bindings
    stack-equiv-except-top-bindings
    (stack$a-pop-minor-frame stack)
    1
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame
                                      minor-stack-equiv-except-top-debug
                                      stack-equiv-except-top-bindings))))

  (defrefinement stack-equiv-except-top-bindings
    stack-equiv-except-top-major/minor-bindings
    :hints(("Goal" :in-theory (enable stack-equiv-except-top-bindings
                                      minor-stack-equiv-except-top-debug)))))






(defsection fgl-interp-stack-equiv-except-top-bindings
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-stack-equiv-except-top-bindings
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((and (not (:fnname fgl-interp-bindinglist))
                    (not (:fnname fgl-rewrite-binder-fncall))
                    (not (:fnname fgl-rewrite-binder-try-rules))
                    (not (:fnname fgl-rewrite-binder-try-rule))
                    (not (:fnname fgl-rewrite-binder-try-rewrite))
                    (not (:fnname fgl-rewrite-binder-try-meta))
                    (not (:fnname fgl-rewrite-try-rules))
                    (not (:fnname fgl-rewrite-try-rule))
                    (not (:fnname fgl-rewrite-try-rewrite))
                    (not (:fnname fgl-rewrite-try-meta))
                    (not (:fnname fgl-rewrite-apply-rule)))
               (:add-concl (stack-equiv-except-top-bindings
                            (fgl-major-stack-concretize (interp-st->stack new-interp-st)
                                            env
                                            (interp-st->logicman new-interp-st))
                            (fgl-major-stack-concretize (interp-st->stack interp-st)
                                            env
                                            (interp-st->logicman interp-st)))))
              ((:fnname fgl-interp-bindinglist)
               (:add-concl (stack-equiv-except-top-major/minor-bindings
                            (fgl-major-stack-concretize (interp-st->stack new-interp-st)
                                            env
                                            (interp-st->logicman new-interp-st))
                            (fgl-major-stack-concretize (interp-st->stack interp-st)
                                            env
                                            (interp-st->logicman interp-st)))))
              ((or (:fnname fgl-rewrite-binder-fncall)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-apply-rule))
               (:add-concl (equal
                            (fgl-major-stack-concretize (interp-st->stack new-interp-st)
                                            env
                                            (interp-st->logicman new-interp-st))
                            (fgl-major-stack-concretize (interp-st->stack interp-st)
                                            env
                                            (interp-st->logicman interp-st)))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st))) :fgl-objlist))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp))

  (defcong stack-equiv-except-top-bindings equal (stack$a-minor-bindings stack) 1
    :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                      minor-stack-equiv-except-top-debug
                                      stack-equiv-except-top-bindings))))

  (defthm hons-assoc-equal-of-fgl-object-bindings-concretize
    (iff (hons-assoc-equal v (fgl-object-bindings-concretize bindings env logicman))
         (hons-assoc-equal v (fgl-object-bindings-fix bindings)))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
                                      fgl-object-bindings-fix))))

  (local (defthmd stack$a-bindings-of-fgl-major-stack-concretize
           (equal (fgl-object-bindings-concretize (stack$a-bindings stack) env logicman)
                  (stack$a-bindings (fgl-major-stack-concretize stack env logicman)))
           :hints(("Goal" :in-theory (enable stack$a-bindings
                                             fgl-major-stack-concretize
                                             fgl-major-frame-concretize)))))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-stack-bindings-has-key
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules (((or (:fnname fgl-rewrite-binder-fncall)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-apply-rule))
               (:add-concl (iff (hons-assoc-equal v (stack$a-bindings (interp-st->stack new-interp-st)))
                                (hons-assoc-equal v (stack$a-bindings (interp-st->stack interp-st))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st))) :fgl-objlist)))
              (t (:add-keyword :hints ('(:do-not-induct t
                                         :in-theory (e/d (stack$a-bindings-of-fgl-major-stack-concretize)
                                                         (LOOKUP-UNDER-IFF-OF-FGL-OBJECT-BINDINGS-EV
                                                          LOOKUP-OF-FGL-OBJECT-BINDINGS-EV
                                                          hons-assoc-equal-of-fgl-object-bindings-concretize))
                                         :use ((:instance hons-assoc-equal-of-fgl-object-bindings-concretize
                                                (bindings (stack$a-bindings (interp-st->stack new-interp-st)))
                                                (env env)
                                                (logicman (interp-st->logicman new-interp-st)))
                                               (:instance hons-assoc-equal-of-fgl-object-bindings-concretize
                                                (bindings (stack$a-bindings (interp-st->stack interp-st)))
                                                (env env)
                                                (logicman (interp-st->logicman interp-st)))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp
      :no-induction-hint t))

  (local (defthm stack$a-minor-bindings-of-fgl-major-stack-concretize
           (equal (stack$a-minor-bindings (fgl-major-stack-concretize stack env logicman))
                  (fgl-object-bindings-concretize (stack$a-minor-bindings stack) env logicman))
           :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                             fgl-major-stack-concretize
                                             fgl-major-frame-concretize
                                             fgl-minor-stack-concretize
                                             fgl-minor-frame-concretize)))))

  (local (defthm hons-assoc-equal-of-stack$a-minor-bindings-of-concretize
           (iff (hons-assoc-equal v (stack$a-minor-bindings (fgl-major-stack-concretize stack env logicman)))
                (hons-assoc-equal v (stack$a-minor-bindings stack)))))

  (defthm hons-assoc-equal-of-stack$a-minor-bindings-of-fgl-interp-term-top
    (b* (((mv ?ans new-interp-st ?new-state)
          (fgl-interp-term-top x interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (iff (hons-assoc-equal v (stack$a-minor-bindings (interp-st->stack new-interp-st)))
                    (hons-assoc-equal v (stack$a-minor-bindings (interp-st->stack interp-st))))))
    :hints (("goal" :use ((:instance hons-assoc-equal-of-stack$a-minor-bindings-of-concretize
                           (stack (interp-st->stack (mv-nth 1 (fgl-interp-term-top x interp-st state))))
                           (logicman (interp-st->logicman (mv-nth 1 (fgl-interp-term-top x interp-st state)))))
                          (:instance hons-assoc-equal-of-stack$a-minor-bindings-of-concretize
                           (stack (interp-st->stack interp-st))
                           (logicman (interp-st->logicman interp-st))))
             :in-theory (disable hons-assoc-equal-of-stack$a-minor-bindings-of-concretize
                                 stack$a-minor-bindings-of-fgl-major-stack-concretize)))))

(defsection stack-bindings-extension-p
  (define fgl-bindings-extension-p ((x fgl-object-bindings-p)
                                   (y fgl-object-bindings-p))
    (or (fgl-object-bindings-equiv x y)
        (and (consp x)
             (if (mbt (and (consp (car x))
                           (pseudo-var-p (caar x))))
                 (not (hons-assoc-equal (caar x) (cdr x)))
               t)
             (fgl-bindings-extension-p (cdr x) y)))
    ///

    (deffixequiv fgl-bindings-extension-p
      :hints(("Goal" :in-theory (enable fgl-object-bindings-fix))))

    (defthm fgl-bindings-extension-p-transitive
      (implies (and (fgl-bindings-extension-p x y)
                    (fgl-bindings-extension-p y z))
               (fgl-bindings-extension-p x z))
      :hints (("Goal" :induct (fgl-bindings-extension-p x y))))

    (defthm fgl-bindings-extension-p-self
      (fgl-bindings-extension-p x x)
      :hints (("goal" :expand ((fgl-bindings-extension-p x x))))))


  (define stack-bindings-equiv ((x major-stack-p)
                                (y major-stack-p))
    (b* (((major-frame x1) (car x))
         ((major-frame y1) (car y)))
      (fgl-object-bindings-equiv x1.bindings y1.bindings))
    ///
    (defequiv stack-bindings-equiv)

    (defrefinement major-stack-equiv stack-bindings-equiv)

    ;; (defthm stack-bindings-equiv-major-frame->bindings-congruence
    ;;   (implies (stack-bindings-equiv x y)
    ;;            (fgl-object-bindings-equiv (major-frame->bindings (car x))
    ;;                                   (major-frame->bindings (car y))))
    ;;   :rule-classes :congruence)

    (defcong stack-bindings-equiv equal (stack$a-bindings x) 1
      :hints(("Goal" :in-theory (enable stack$a-bindings))))

    (defcong fgl-object-bindings-equiv stack-bindings-equiv (stack$a-set-bindings bindings x) 1
      :hints(("Goal" :in-theory (enable stack$a-set-bindings))))

    (local (defun def-stack-bindings-equiv-identity-fn (op)
             (let ((fn (car op)))
               `(progn (defthm ,(intern-in-package-of-symbol
                                 (concatenate 'string "STACK-BINDINGS-EQUIV-OF-" (symbol-name fn))
                                 fn)
                         (stack-bindings-equiv ,op stack)
                         :hints(("Goal" :in-theory (enable ,fn))))
                       (defcong stack-bindings-equiv stack-bindings-equiv ,op
                         ,(+ 1 (- (len (cdr op))
                                  (len (member 'stack (cdr op))))))))))

    (local (defmacro def-stack-bindings-equiv-identity (op)
             `(make-event (def-stack-bindings-equiv-identity-fn ',op))))

    (def-stack-bindings-equiv-identity (stack$a-push-minor-frame stack))

    (def-stack-bindings-equiv-identity (stack$a-pop-minor-frame stack))

    (def-stack-bindings-equiv-identity (stack$a-set-rule obj stack))
    (def-stack-bindings-equiv-identity (stack$a-set-phase obj stack))

    (def-stack-bindings-equiv-identity (stack$a-set-term-index obj stack))
    (def-stack-bindings-equiv-identity (stack$a-set-term obj stack))

    (def-stack-bindings-equiv-identity (stack$a-set-minor-bindings bindings stack))

    (def-stack-bindings-equiv-identity (stack$a-add-minor-bindings bindings stack))

    (def-stack-bindings-equiv-identity (stack$a-pop-scratch stack))

    (def-stack-bindings-equiv-identity (stack$a-push-scratch obj stack))

    (def-stack-bindings-equiv-identity (stack$a-update-scratch n obj stack)))

  (define stack-bindings-extension-p ((x major-stack-p)
                                      (y major-stack-p))
    (b* (((major-frame x1) (car x))
         ((major-frame y1) (car y)))
      (fgl-bindings-extension-p x1.bindings y1.bindings))
    ///
    (defthmd stack-bindings-extension-p-transitive
      (implies (and (stack-bindings-extension-p x y)
                    (stack-bindings-extension-p y z))
               (stack-bindings-extension-p x z)))

    (defthm stack-bindings-extension-p-self
      (stack-bindings-extension-p x x))

    (def-updater-independence-thm stack-bindings-extension-p-trans-rw
      (implies (and (syntaxp (not (equal old older)))
                    (stack-bindings-extension-p new old)
                    (stack-bindings-extension-p old older))
               (stack-bindings-extension-p new older)))

    (defthm stack-bindings-extension-p-of-stack$a-add-binding
      (implies (not (hons-assoc-equal (pseudo-var-fix var) (stack$a-bindings stack)))
               (stack-bindings-extension-p (stack$a-add-binding var val stack) stack))
      :hints(("Goal" :in-theory (enable stack$a-add-binding
                                        stack$a-bindings
                                        fgl-bindings-extension-p))))

    (defthm stack-bindings-extension-p-of-stack$a-add-binding-concretize
      (implies (not (hons-assoc-equal (pseudo-var-fix var) (stack$a-bindings stack)))
               (stack-bindings-extension-p
                (fgl-major-stack-concretize (stack$a-add-binding var val stack) env logicman)
                (fgl-major-stack-concretize stack env logicman)))
      :hints(("Goal" :in-theory (enable stack$a-add-binding
                                        stack$a-bindings
                                        fgl-bindings-extension-p
                                        fgl-major-stack-concretize
                                        fgl-major-frame-concretize
                                        fgl-object-bindings-concretize))))

    (defthm stack-bindings-extension-p-of-stack$a-add-binding-concretize-trans
      (implies (and (not (hons-assoc-equal (pseudo-var-fix var) (stack$a-bindings stack)))
                    (stack-bindings-extension-p (fgl-major-stack-concretize stack env logicman) older))
               (stack-bindings-extension-p
                (fgl-major-stack-concretize (stack$a-add-binding var val stack) env logicman)
                older))
      :hints(("Goal" :in-theory (disable stack-bindings-extension-p)
              :use ((:instance stack-bindings-extension-p-transitive
                     (x (fgl-major-stack-concretize (stack$a-add-binding var val stack) env logicman))
                     (y (fgl-major-stack-concretize stack env logicman))
                     (z older))))))

    ;; (defthm stack-bindings-extension-p-of-stack$a-add-binding-concretize-equiv
    ;;   (implies (and (stack-bindings-extension-p (fgl-major-stack-concretize stack env logicman) older))
    ;;            (stack-bindings-extension-p
    ;;             (fgl-major-stack-concretize (stack$a-add-binding var val stack) env logicman)
    ;;             older))
    ;;   :hints(("Goal" :in-theory (disable stack-bindings-extension-p)
    ;;           :use ((:instance stack-bindings-extension-p-transitive
    ;;                  (x (fgl-major-stack-concretize (stack$a-add-binding var val stack) env logicman))
    ;;                  (y (fgl-major-stack-concretize stack env logicman))
    ;;                  (z older))))))

    (defcong stack-bindings-equiv equal (stack-bindings-extension-p x y) 1
      :hints(("Goal" :in-theory (enable stack-bindings-equiv))))
    (defcong stack-bindings-equiv equal (stack-bindings-extension-p x y) 2
      :hints(("Goal" :in-theory (enable stack-bindings-equiv))))

    (local (Defthm fgl-bindings-extension-p-of-append
             (implies (and (not (intersectp-equal (alist-keys a) (alist-keys b)))
                           (no-duplicatesp-equal (alist-keys a))
                           (equal bb b))
                      (fgl-bindings-extension-p (Append a bb) b))
             :hints(("Goal" :in-theory (enable fgl-bindings-extension-p append)))))

    (local (defun equal-of-appends-ind (a1 a2)
             (if (atom a1)
                 a2
               (equal-of-appends-ind (cdr a1) (cdr a2)))))

    (local (defthm equal-of-appends
             (implies (equal (len a1) (len a2))
                      (equal (equal (append a1 b1) (append a2 b2))
                             (and (equal (true-list-fix a1) (true-list-fix a2))
                                  (equal b1 b2))))
             :hints(("Goal" :induct (equal-of-appends-ind a1 a2)
                     :in-theory (enable len append)))))

    (local (defthm len-of-fgl-object-bindings-ev
             (equal (len (fgl-object-bindings-concretize x env))
                    (len (fgl-object-bindings-fix x)))
             :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
                                               fgl-object-bindings-fix
                                               len)))))

    (local (defthm alist-keys-of-fgl-object-bindings-ev
             (equal (alist-keys (fgl-object-bindings-concretize x env))
                    (alist-keys (fgl-object-bindings-fix x)))
             :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
                                               fgl-object-bindings-fix
                                               alist-keys)))))

    (local (defthm fgl-object-bindings-p-when-fgl-bfr-object-bindings-p
             (implies (fgl-bfr-object-bindings-p x)
                      (fgl-object-bindings-p x))
             :hints(("Goal" :in-theory (enable fgl-bfr-object-bindings-p)))
             :rule-classes :forward-chaining))

    (local (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-synp-lemma
             (implies (and (equal (fgl-major-stack-concretize (interp-st->stack new-interp-st) env logicman)
                                  (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))))
                      (stack-bindings-extension-p
                       (fgl-major-stack-concretize (interp-st->stack new-interp-st) env
                                                   logicman)
                       (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st))))
             :hints(("Goal" :in-theory (enable fgl-rewrite-relieve-hyp-synp
                                               stack$a-set-bindings
                                               stack$a-bindings
                                               fgl-major-stack-concretize
                                               fgl-major-frame-concretize)))
             :fn fgl-rewrite-relieve-hyp-synp))

    (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-synp
      (implies (and (equal (fgl-major-stack-concretize (interp-st->stack new-interp-st) env logicman)
                           (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st)))
                    (stack-bindings-extension-p
                     (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st))
                     (fgl-major-stack-concretize (interp-st->stack interp-st1) env (interp-st->logicman interp-st1))))
               (stack-bindings-extension-p
                (fgl-major-stack-concretize (interp-st->stack new-interp-st) env
                                logicman)
                (fgl-major-stack-concretize (interp-st->stack interp-st1) env
                                (interp-st->logicman interp-st1))))
      :hints(("Goal" :use stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-synp-lemma
              :in-theory (disable stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-synp-lemma)))
      :fn fgl-rewrite-relieve-hyp-synp)

    (def-updater-independence-thm ev-interp-st-stack-bindings-extension-p-trans-rw
      (implies (and (syntaxp (not (equal old older)))
                    (stack-bindings-extension-p
                     (fgl-major-stack-concretize (interp-st->stack new) env logicman)
                     (fgl-major-stack-concretize (interp-st->stack old) env
                                     (interp-st->logicman old)))
                    (stack-bindings-extension-p
                     (fgl-major-stack-concretize (interp-st->stack old) env
                                     (interp-st->logicman old))
                     older))
               (stack-bindings-extension-p
                (fgl-major-stack-concretize (interp-st->stack new) env logicman) older))
      :hints(("Goal" :in-theory (enable stack-bindings-extension-p-transitive))))))



(defsection fgl-interp-stack-bindings-extension
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (local (acl2::use-trivial-ancestors-check))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-stack-bindings-extended
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules (((and (not (:fnname fgl-rewrite-binder-fncall))
                    (not (:fnname fgl-rewrite-binder-try-rules))
                    (not (:fnname fgl-rewrite-binder-try-rule))
                    (not (:fnname fgl-rewrite-binder-try-rewrite))
                    (not (:fnname fgl-rewrite-binder-try-meta)))
               (:add-concl (stack-bindings-extension-p
                              (fgl-major-stack-concretize (interp-st->stack new-interp-st)
                                              env
                                              (interp-st->logicman new-interp-st))
                              (fgl-major-stack-concretize (interp-st->stack interp-st)
                                              env
                                              (interp-st->logicman interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-objlist))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp))


  (local (defthm stack-bindings-extension-p-when-equal-bindings
           (implies (and (equal (stack$a-bindings y) (stack$A-bindings z))
                         (stack-bindings-extension-p x z))
                    (stack-bindings-extension-p x y))
           :hints(("Goal" :in-theory (enable stack$a-bindings stack-bindings-extension-p)))))

  ;; (local (defthm stack-bindings-equal-forward
  ;;          (implies (equal (stack$a-bindings x) (stack$a-bindings y))
  ;;                   (stack-bindings-equiv x y))
  ;;          :hints(("Goal" :in-theory (enable stack-bindings-equiv stack$a-bindings)))
  ;;          :rule-classes :forward-chaining))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-stack-bindings-extended-rw
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl (implies (and (equal (stack$a-bindings old-stack-ev)
                                                  (stack$a-bindings (fgl-major-stack-concretize
                                                                     (interp-st->stack interp-st)
                                                                     env
                                                                     (interp-st->logicman interp-st)))))
                                      (stack-bindings-extension-p
                                       (fgl-major-stack-concretize (interp-st->stack new-interp-st)
                                                       env
                                                       (interp-st->logicman new-interp-st))
                                       old-stack-ev))))

              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st))) :fgl-objlist))))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))

(defsection fgl-interp-preserves-equiv-contexts
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))



  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-equiv-contexts-preserved
      :rules ((t (:add-concl (equal (interp-st->equiv-contexts new-interp-st)
                                    (interp-st->equiv-contexts interp-st)))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))


(defthm true-listp-of-fgl-ev-list
  (true-listp (fgl-ev-list x a))
  :hints (("goal" :induct (len x) :in-theory (enable len)))
  :rule-classes :type-prescription)

(cmr::defthm-term-vars-flag
  (defthm fgl-ev-of-alist-fix
    (equal (fgl-ev x (acl2::alist-fix a))
           (fgl-ev x a))
    :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
    :flag cmr::term-vars)
  (defthm fgl-ev-list-of-alist-fix
    (equal (fgl-ev-list x (acl2::alist-fix a))
           (fgl-ev-list x a))
    :flag cmr::termlist-vars))

(progn

  (fty::deffixtype alistp :pred alistp :fix acl2::alist-fix :equiv alistp-equiv :define t :forward t)

  (fty::deffixcong alistp-equiv equal (fgl-ev x a) a)
  (fty::deffixcong alistp-equiv equal (fgl-ev-list x a) a)

  (local (defthm alist-fix-of-append
           (equal (acl2::alist-fix (append a b))
                  (append (acl2::alist-fix a) (acl2::alist-fix b)))
           :hints(("Goal" :in-theory (enable append)))))

  (fty::deffixcong alistp-equiv alistp-equiv (append a b) a)
  (fty::deffixcong alistp-equiv alistp-equiv (append a b) b)

  (fty::deffixcong alistp-equiv equal (hons-assoc-equal x a) a))


(define fgl-ev-bindinglist ((x cmr::bindinglist-p)
                            (a alistp))
  :returns (final-alist alistp)
  (b* (((when (atom x)) (acl2::alist-fix a))
       ((cmr::binding x1) (car x))
       (new-bindings (pairlis$ x1.formals (fgl-ev-list x1.args a))))
    (fgl-ev-bindinglist (cdr x) (append new-bindings a)))
  ///
  #!cmr
  (defret lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist
    (equal (fgl::fgl-ev body (fgl::fgl-ev-bindinglist bindings a))
           (fgl::fgl-ev x a))
    :hints (("goal" :use ((:instance (:functional-instance lambda-nest-to-bindinglist-correct
                                      (base-ev fgl::fgl-ev)
                                      (base-ev-list fgl::fgl-ev-list)
                                      (base-ev-bindinglist fgl::fgl-ev-bindinglist))
                           (x x) (a a)))
             :in-theory (enable fgl::fgl-ev-of-bad-fncall
                                fgl::fgl-ev-of-fncall-args
                                fgl::fgl-ev-of-nonsymbol-atom)))
    :fn lambda-nest-to-bindinglist))


(define fgl-ev-bindinglist-minmaj ((x cmr::bindinglist-p)
                                   (minor alistp)
                                   (major alistp))
  :returns (final-alist alistp)
  (b* (((when (atom x)) (acl2::alist-fix minor))
       ((cmr::binding x1) (car x))
       (new-bindings (pairlis$ x1.formals (fgl-ev-list x1.args (append minor major)))))
    (fgl-ev-bindinglist-minmaj (cdr x) (append new-bindings minor) major))
  ///
  (local (defthm alist-fix-of-append
           (Equal (acl2::alist-fix (append a b))
                  (append (Acl2::alist-fix a) (acl2::Alist-fix b)))
           :hints(("Goal" :in-theory (enable acl2::alist-fix append)))))
  (local
   (defthmd fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist-lemma
     (equal (append (fgl-ev-bindinglist-minmaj x minor major) (acl2::alist-fix major))
            (fgl-ev-bindinglist x (append minor major)))
     :hints(("Goal" :in-theory (enable fgl-ev-bindinglist)))))

  ;; (defthm fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist
  ;;   (implies (equal major1 (acl2::alist-fix major))
  ;;            (equal (append (fgl-ev-bindinglist-minmaj x minor major) major1)
  ;;                   (fgl-ev-bindinglist x (append minor major))))
  ;;   :hints(("Goal" :in-theory (enable fgl-ev-bindinglist))))

  (local
   #!cmr
   (defretd lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist-minmaj-lemma
     (equal (fgl::fgl-ev body
                         (append (fgl::fgl-ev-bindinglist-minmaj bindings minor major) (acl2::alist-fix major)))
            (fgl::fgl-ev x (append minor major)))
     :hints(("Goal" :in-theory (e/d ( fgl::fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist-lemma)
                                    (fgl::FGL-EV-ALISTP-EQUIV-CONGRUENCE-ON-A))))
     :fn lambda-nest-to-bindinglist))

  (local (fty::deffixcong alistp-equiv equal (fgl-ev-bindinglist-minmaj x minor major) major))


  #!cmr
  (defret lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist-minmaj
    (implies (fgl::alistp-equiv major1 major)
             (equal (fgl::fgl-ev body
                                 (append (fgl::fgl-ev-bindinglist-minmaj bindings minor major) major1))
                    (fgl::fgl-ev x (append minor major))))
    :hints (("Goal" :use ((:instance lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist-minmaj-lemma))))

    ;; :hints (("goal" :use ((:instance fgl::fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist
    ;;                        (major1 (acl2::alist-fix major1))))
    ;;          :in-theory (disable fgl::fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist
    ;;                              fgl::fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist-lemma)))
    :fn lambda-nest-to-bindinglist))


(cmr::defthm-term-vars-flag
  (defthm fgl-ev-of-true-list-fix-alist
    (equal (fgl-ev x (true-list-fix a))
           (fgl-ev x a))
    :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
    :flag cmr::term-vars)
  (defthm fgl-ev-list-of-true-list-fix-alist
    (equal (fgl-ev-list x (true-list-fix a))
           (fgl-ev-list x a))
    :flag cmr::termlist-vars))




(defthm fgl-object-eval-of-fgl-object-ev
  (equal (fgl-object-eval (fgl-object-concretize x env) env2 logicman2)
         (fgl-object-eval x env))
  :hints(("Goal" :in-theory (enable fgl-object-concretize))))

(defthm fgl-objectlist-eval-of-fgl-objectlist-ev
  (equal (fgl-objectlist-eval (fgl-objectlist-concretize x env) env2 logicman2)
         (fgl-objectlist-eval x env))
  :hints(("Goal" :in-theory (enable fgl-objectlist-concretize
                                    fgl-objectlist-eval))))

(defthm fgl-object-bindings-eval-of-fgl-object-ev
  (equal (fgl-object-bindings-eval (fgl-object-bindings-concretize x env) env2 logicman2)
         (fgl-object-bindings-eval x env))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
                                    fgl-object-bindings-eval))))

(defthm hons-assoc-equal-of-fgl-object-bindings-eval-under-iff
  (iff (hons-assoc-equal k (fgl-object-bindings-eval x env))
       (hons-assoc-equal k (fgl-object-bindings-fix x)))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-eval
                                    fgl-object-bindings-fix))))

(defsection eval-alist-extension-p


  (local (defthm lookup-in-fgl-bindings-extension
           (implies (and (fgl-bindings-extension-p x y)
                         (pseudo-var-p k)
                         (hons-assoc-equal k y))
                    (and (hons-assoc-equal k x)
                         (fgl-object-equiv (cdr (hons-assoc-equal k x))
                                          (cdr (hons-assoc-equal k y)))))
           :hints(("Goal" :in-theory (enable fgl-bindings-extension-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance hons-assoc-equal-of-fgl-object-bindings-fix)
                               (:instance hons-assoc-equal-of-fgl-object-bindings-fix (x y)))
                         :in-theory (disable hons-assoc-equal-of-fgl-object-bindings-fix))))))

  (defthm eval-alist-extension-p-of-eval-when-fgl-bindings-extension-p
    (implies (fgl-bindings-extension-p x y)
             (eval-alist-extension-p
              (fgl-object-bindings-eval x env)
              (fgl-object-bindings-eval y env)))
    :hints(("Goal" :use ((:instance acl2::sub-alistp-when-witness
                          (a (fgl-object-bindings-eval y env)) (b (fgl-object-bindings-eval x env)))))))

  (defthm eval-alist-extension-p-self
    (eval-alist-extension-p x x))

  (defthmd sub-alistp-by-witness
    (implies (acl2::Rewriting-positive-literal `(acl2::sub-alistp ,a ,b))
             (iff (acl2::sub-alistp a b)
                  (let ((x (acl2::not-sub-alistp-witness a b)))
                    (implies (hons-assoc-equal x a)
                             (equal (hons-assoc-equal x a)
                                    (hons-assoc-equal x b))))))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-iff-witness)))))



(local (in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes)))







(defthmd eval-alist-extension-p-transitive-1
  (implies (and (eval-alist-extension-p a b)
                (eval-alist-extension-p b c))
           (eval-alist-extension-p a c))
  :hints(("Goal" :in-theory (e/d (acl2::sub-alistp-trans)
                                 (sub-alistp-by-witness)))))

(defthmd eval-alist-extension-p-transitive-2
  (implies (and (eval-alist-extension-p b c)
                (eval-alist-extension-p a b))
           (eval-alist-extension-p a c))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-1))))


(defthm eval-alist-extension-p-of-append
  (implies (eval-alist-extension-p b c)
           (eval-alist-extension-p (append a b) (append a c)))
  :hints(("Goal" :in-theory (enable acl2::sub-alistp-hons-assoc-equal
                                    sub-alistp-by-witness))))

(defthmd eval-alist-extension-p-transitive-append-1
  (implies (and (eval-alist-extension-p b c)
                (eval-alist-extension-p (append a c) d))
           (eval-alist-extension-p (append a b) d))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-2))))

(defthmd eval-alist-extension-p-transitive-append-2
  (implies (and (eval-alist-extension-p b d)
                (eval-alist-extension-p a (append c b)))
           (eval-alist-extension-p a (append c d)))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-1))))

(defthm equal-of-fgl-ev-context-fix-iff
  (equal (equal (fgl-ev-context-fix '(iff) x)
                (fgl-ev-context-fix '(iff) y))
         (iff* x y))
  :hints(("Goal" :in-theory (e/d (iff*)
                                 (fgl-ev-context-equiv-is-equal-of-fixes))
          :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes
                 (contexts '(iff)))))))


(local (defthm hons-assoc-equal-when-sub-alistp
         (implies (and (acl2::sub-alistp a b)
                       (hons-assoc-equal k a))
                  (equal (hons-assoc-equal k b)
                         (hons-assoc-equal k a)))
         :hints(("Goal" :in-theory (enable acl2::sub-alistp-hons-assoc-equal)))))

(local (in-theory (disable acl2::sub-alistp-hons-assoc-equal)))



(defsection fgl-ev-context-equiv-forall-extensions
  ;; (defun-sk fgl-ev-context-equiv-forall-extensions (contexts
  ;;                                                   obj
  ;;                                                   term
  ;;                                                   eval-alist)
  ;;   (forall (ext)
  ;;           (implies (eval-alist-extension-p ext eval-alist)
  ;;                    (equal (fgl-ev-context-fix contexts
  ;;                                               (fgl-ev term ext))
  ;;                           (fgl-ev-context-fix contexts obj))))
  ;;   :rewrite :direct)

  ;; (in-theory (disable fgl-ev-context-equiv-forall-extensions))

  (acl2::defquantexpr fgl-ev-context-equiv-forall-extensions
    :predicate (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
    :quantifier :forall
    :witnesses ((ext (fgl-ev-context-equiv-forall-extensions-witness
                      contexts obj term eval-alist)))
    :expr (implies (eval-alist-extension-p ext eval-alist)
                   (equal (fgl-ev-context-fix contexts
                                              (fgl-ev term ext))
                          (fgl-ev-context-fix contexts obj)))
    :instance-rulename fgl-ev-context-equiv-forall-extensions-instancing
    :wcp-witness-rulename fgl-ev-context-equiv-forall-extensions-witnessing)

  (in-theory (disable fgl-ev-context-equiv-forall-extensions
                      fgl-ev-context-equiv-forall-extensions-necc))

  (acl2::defexample fgl-ev-context-equiv-forall-extensions-fgl-ev-example
    :pattern (fgl-ev x ext)
    :templates (ext)
    :instance-rules (fgl-ev-context-equiv-forall-extensions-instancing))

  (acl2::defexample fgl-ev-context-equiv-forall-extensions-fgl-ev-list-example
    :pattern (fgl-ev-list x ext)
    :templates (ext)
    :instance-rules (fgl-ev-context-equiv-forall-extensions-instancing))

  (acl2::def-witness-ruleset fgl-ev-context-equiv-forall
    '(fgl-ev-context-equiv-forall-extensions-instancing
      fgl-ev-context-equiv-forall-extensions-witnessing
      fgl-ev-context-equiv-forall-extensions-fgl-ev-example
      fgl-ev-context-equiv-forall-extensions-fgl-ev-list-example))

  (defcong fgl-ev-equiv equal (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist) 3
    :hints (("goal" :cases ((fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)))
            (acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (local (defthm equal-of-or-test-contexts-implies-contexts
           (b* ((contexts1 (fgl-interp-or-test-equiv-contexts contexts)))
             (implies (equal (fgl-ev-context-fix contexts1 x)
                             (fgl-ev-context-fix contexts1 y))
                      (equal (fgl-ev-context-fix contexts x)
                             (fgl-ev-context-fix contexts y))))
           :hints(("Goal" :in-theory (enable fgl-interp-or-test-equiv-contexts)))
           :rule-classes :forward-chaining))

  (local (defthm equal-of-or-test-contexts-implies-contexts-nil
           (b* ((contexts1 (fgl-interp-or-test-equiv-contexts contexts)))
             (implies (equal (fgl-ev-context-fix contexts1 nil)
                             (fgl-ev-context-fix contexts1 x))
                      (equal (fgl-ev-context-fix contexts x)
                             (fgl-ev-context-fix contexts nil))))
           :rule-classes :forward-chaining))

  (local (defthm or-test-contexts-correct-else-true
           (b* ((contexts1 (fgl-interp-or-test-equiv-contexts contexts)))
             (implies (and (syntaxp (not (equal else-eval ''nil)))
                           (equal (fgl-ev-context-fix contexts1 test-eval)
                                  (fgl-ev-context-fix contexts1 nil))
                           test-eval)
                      (equal (fgl-ev-context-fix contexts else-eval)
                             (fgl-ev-context-fix contexts nil))))
           :hints(("Goal" :in-theory (enable fgl-interp-or-test-equiv-contexts)))))

  ;; (local (in-theory (enable fgl-ev-context-equiv-of-fgl-interp-or-test-equiv-contexts-implies-contexts)))

  (local (in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes)))

  (defthm fgl-ev-context-equiv-forall-extensions-rewrite-or
    (implies (and (fgl-ev-context-equiv-forall-extensions
                   (fgl-interp-or-test-equiv-contexts contexts)
                   test-ev
                   test (append minor-bindings major-bindings0))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts
                   else-ev else (append minor-bindings major-bindings1))
                  (equal (fgl-ev-context-fix contexts if-ev)
                         (fgl-ev-context-fix contexts (if* test-ev test-ev else-ev)))
                  (eval-alist-extension-p major-bindings1 major-bindings0)
                  (eval-alist-extension-p major-bindings2 major-bindings1))
             (fgl-ev-context-equiv-forall-extensions
              contexts if-ev
              (pseudo-term-fncall 'if (list test test else))
              (append minor-bindings major-bindings2)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::Witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-rewrite-or-when-test
    (implies (and (fgl-ev-context-equiv-forall-extensions
                   (fgl-interp-or-test-equiv-contexts contexts)
                   test-ev
                   test (append minor-bindings major-bindings0))
                  test-ev
                  (fgl-ev-context-equiv
                   contexts
                   if-ev test-ev)
                  (eval-alist-extension-p major-bindings2 major-bindings0))
             (fgl-ev-context-equiv-forall-extensions
              contexts if-ev
              (pseudo-term-fncall 'if (list test test else))
              (append minor-bindings major-bindings2)))
    :hints (("goal" :in-theory (e/d (eval-alist-extension-p-transitive-append-2)
                                    ( if*)))
            (acl2::Witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-when-equivalent-to-other-obj
    (implies (and (fgl-ev-context-equiv-forall-extensions
                   contexts obj1 term eval-alist)
                  (fgl-ev-context-equiv contexts obj0 obj1))
             (fgl-ev-context-equiv-forall-extensions
              contexts obj0 term eval-alist))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-var-minor-bindings
    (implies (and (pseudo-term-case x :var)
                  (hons-assoc-equal (pseudo-term-var->name x) minor-bindings))
             (fgl-ev-context-equiv-forall-extensions
              contexts
              (cdr (hons-assoc-equal (pseudo-term-var->name x) minor-bindings))
              x
              (append minor-bindings major-bindings)))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions
                                      acl2::sub-alistp-hons-assoc-equal))))

  (defthm fgl-ev-context-equiv-forall-extensions-var-major-bindings
    (implies (and (pseudo-term-case x :var)
                  (not (hons-assoc-equal (pseudo-term-var->name x) minor-bindings))
                  (hons-assoc-equal (pseudo-term-var->name x) major-bindings))
             (fgl-ev-context-equiv-forall-extensions
              contexts
              (cdr (hons-assoc-equal (pseudo-term-var->name x) major-bindings))
              x
              (append minor-bindings major-bindings)))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions
                                      acl2::sub-alistp-hons-assoc-equal))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-if-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
                    (equal x.fn 'if)
                    (fgl-ev-context-equiv-forall-extensions
                     contexts obj (pseudo-term-fncall 'if
                                                      (list (car x.args)
                                                            (cadr x.args)
                                                            (caddr x.args)))
                     alist))
               (fgl-ev-context-equiv-forall-extensions
                contexts obj x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-return-last-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
                    (equal x.fn 'return-last)
                    (fgl-ev-context-equiv-forall-extensions
                     contexts obj (caddr x.args)
                     alist))
               (fgl-ev-context-equiv-forall-extensions
                contexts obj x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (local (defthm lookup-in-fgl-object-bindings-ev
           (iff (hons-assoc-equal k (fgl-object-bindings-concretize x env))
                (hons-assoc-equal k (fgl-object-bindings-fix x)))
           :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
                                             fgl-object-bindings-fix)))))

  (local (defthm lookup-in-minor-stack-of-stack-ev
           (iff (hons-assoc-equal var (stack$a-minor-bindings
                                       (fgl-major-stack-concretize stack env)))
                (hons-assoc-equal var (stack$a-minor-bindings stack)))
           :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                             fgl-major-frame-concretize
                                             fgl-minor-frame-concretize)
                   :expand ((fgl-major-stack-concretize stack env)
                            (fgl-minor-stack-concretize
                             (major-frame->minor-stack (car stack))
                             env))))))

  (defthm stack$a-bindings-of-stack$a-add-binding
    (equal (stack$a-bindings (stack$a-add-binding var val stack))
           (cons (cons (pseudo-var-fix var)
                       (fgl-object-fix val))
                 (stack$a-bindings stack)))
    :hints(("Goal" :in-theory (enable stack$a-bindings
                                      stack$a-add-binding))))


  ;; (defthm fgl-ev-equiv-of-bind-var-call
  ;;   (implies (equal (pseudo-fnsym-fix fn) 'bind-var)
  ;;            (fgl-ev-equiv (pseudo-term-fncall fn args)
  ;;                          (car args)))
  ;;   :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

  (defthm fgl-ev-equiv-of-binder-call
    (implies (equal (pseudo-fnsym-fix fn) 'binder)
             (fgl-ev-equiv (pseudo-term-fncall fn args)
                           (car args)))
    :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

  (defthm fgl-ev-equiv-of-assume-call
    (implies (member (pseudo-fnsym-fix fn) '(assume syntax-interp-fn fgl-interp-obj))
             (fgl-ev-equiv (pseudo-term-fncall fn args)
                           nil))
    :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

  (defthm fgl-ev-equiv-of-narrow-equiv-call
    (implies (member (pseudo-fnsym-fix fn) '(narrow-equiv fgl-time-fn))
             (fgl-ev-equiv (pseudo-term-fncall fn args)
                           (second args)))
    :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

  (defthm fgl-ev-context-equiv-forall-extensions-when-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
             (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions))))

  (fty::deffixcong cmr::equiv-contexts-equiv equal (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
    contexts
    :hints (("goal" :cases
             ((fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist))
             :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                    (contexts contexts)
                    (ext (fgl-ev-context-equiv-forall-extensions-witness
                          (equiv-contexts-fix contexts) obj term eval-alist)))
                   (:instance fgl-ev-context-equiv-forall-extensions-necc
                    (contexts (equiv-contexts-fix contexts))
                    (ext (fgl-ev-context-equiv-forall-extensions-witness
                          contexts obj term eval-alist))))
             :in-theory (e/d (fgl-ev-context-equiv-forall-extensions)
                             (fgl-ev-context-equiv-forall-extensions-necc)))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-bind-free-var2
    (implies (and (pseudo-term-case free-var :var)
                  (not (hons-assoc-equal (pseudo-term-var->name free-var) minor-bindings))
                  ;; (not (hons-assoc-equal (pseudo-term-var->name free-var) major-bindings))
                  )
             (fgl-ev-context-equiv-forall-extensions
              contexts ans free-var
              (append minor-bindings
                      (cons (cons (pseudo-term-var->name free-var) ans)
                            (fgl-object-bindings-eval major-bindings env logicman)))))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-eval
                                      fgl-ev-context-equiv-forall-extensions))))


  (defthm fgl-ev-context-equiv-forall-extensions-when-coarsening
    (implies (and (equiv-contexts-coarsening-p contexts contexts2)
                  (fgl-ev-context-equiv-forall-extensions
                   contexts2 obj term eval-alist))
             (fgl-ev-context-equiv-forall-extensions
              contexts obj term eval-alist))
    :hints (("goal" :expand ((fgl-ev-context-equiv-forall-extensions
                              contexts obj term eval-alist))
             :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)
             :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                    (contexts contexts2)
                    (ext (fgl-ev-context-equiv-forall-extensions-witness
                          contexts obj term eval-alist)))))))

  ;; ugh this is an awful rewrite rule
  (defthm fgl-ev-context-equiv-forall-extensions-of-meta-fncall-stub2
    (b* (((mv ?successp ?rhs ?bindings ?new-interp-st ?new-state)
          (fgl-meta-fncall-stub primfn fn args interp-st state)))
      (implies (and successp
                    (fgl-ev-context-equiv-forall-extensions
                     contexts
                     interp-obj
                     rhs bindings2)
                    (bind-free '((env . env)) (env))
                    (eval-alist-extension-p
                     bindings2
                     (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))
                    (equal contexts (interp-st->equiv-contexts interp-st))
                    (fgl-ev-meta-extract-global-facts :state st)
                    (fgl-formula-checks-stub st)
                    (equal (w st) (w state))
                    (interp-st-bfrs-ok interp-st)
                    (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                    (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                            (interp-st->constraint interp-st)
                                            (interp-st->logicman interp-st))
                    (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                            (interp-st->pathcond interp-st)
                                            (interp-st->logicman interp-st)))
               (equal (fgl-ev-context-fix
                       contexts
                       interp-obj)
                      (fgl-ev-context-fix
                       contexts
                       (fgl-object-eval (g-apply fn args) env (interp-st->logicman interp-st))))))
    :hints (("Goal" :use ((:instance eval-of-fgl-meta-fncall-stub (origfn (pseudo-fnsym-fix fn)))
                          (:instance fgl-ev-context-equiv-forall-extensions-necc
                           (contexts (interp-st->equiv-contexts interp-st))
                           (obj interp-obj)
                           (term (mv-nth 1 (fgl-meta-fncall-stub primfn fn args interp-st state)))
                           (eval-alist bindings2)
                           (ext bindings2))
                          (:instance fgl-ev-context-equiv-forall-extensions-necc
                           (contexts (interp-st->equiv-contexts interp-st))
                           (obj (fgl-object-eval (g-apply fn args) env (interp-st->logicman interp-st)))
                           (term (mv-nth 1 (fgl-meta-fncall-stub primfn fn args interp-st state)))
                           (eval-alist (fgl-object-bindings-eval
                                        (mv-nth 2 (fgl-meta-fncall-stub primfn fn args interp-st state))
                                        env
                                        (interp-st->logicman
                                         (mv-nth 3 (fgl-meta-fncall-stub primfn fn args interp-st state)))))
                           (ext bindings2)))
             :in-theory (e/d (fgl-apply)
                             (eval-of-fgl-meta-fncall-stub
                                 fgl-ev-context-equiv-forall-extensions-necc)))))


  (defthm eval-of-fgl-binder-fncall-stub-tweak
    (b* (((mv ?successp acl2::?rhs ?bindings ?rhs-contexts ?new-interp-st ?new-state)
          (fgl-binder-fncall-stub primfn origfn args interp-st state)))
      (implies
       (and
        successp
        (bind-free '((env . env)) (env))
        (equal contexts
               (interp-st->equiv-contexts interp-st))
        (fgl-ev-context-equiv-forall-extensions
         rhs-contexts rhs-val rhs
         eval-alist)
        (eval-alist-extension-p eval-alist (fgl-object-bindings-eval
                                              bindings env
                                              (interp-st->logicman new-interp-st)))
        (fgl-ev-meta-extract-global-facts :state st)
        (fgl-formula-checks-stub st)
        (equal (w st) (w state))
        (interp-st-bfrs-ok interp-st)
        (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
        (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                (interp-st->constraint interp-st)
                                (interp-st->logicman interp-st))
        (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                (interp-st->pathcond interp-st)
                                (interp-st->logicman interp-st))
        (equal args-eval
               (fgl-objectlist-eval
                args
                env (interp-st->logicman interp-st))))
       (equal
        (fgl-ev-context-fix
         contexts
         (fgl-ev
          (list* (pseudo-fnsym-fix origfn)
                 (pseudo-term-quote rhs-val)
                 (kwote-lst args-eval))
          nil))
        (fgl-ev-context-fix contexts rhs-val))))
    :hints(("Goal" :in-theory (enable pseudo-term-quote)
            :use ((:instance eval-of-fgl-binder-fncall-stub
                   (origfn (pseudo-fnsym-fix origfn)))))))
  )


(defsection fgl-ev-of-extension-when-term-vars-bound
  (local (defthm subsetp-equal-of-append
           (iff (subsetp-equal (append a b) c)
                (And (subsetp-equal a c)
                     (subsetp-equal b c)))
           :hints(("Goal" :in-theory (enable subsetp-equal)))))

  (cmr::defthm-term-vars-flag
    (defthmd fgl-ev-of-extension-when-term-vars-bound
      (implies (and (eval-alist-extension-p b a)
                    (subsetp (term-vars x) (alist-keys a)))
               (equal (fgl-ev x b)
                      (fgl-ev x a)))
      :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)
               :expand ((term-vars x)
                        (:free (x y) (subsetp-equal (list x) y)))))
      :flag cmr::term-vars)
    (defthmd fgl-ev-list-of-extension-when-term-vars-bound
      (implies (and (eval-alist-extension-p b a)
                    (subsetp (termlist-vars x) (alist-keys a)))
               (equal (fgl-ev-list x b)
                      (fgl-ev-list x a)))
      :hints ('(:expand ((termlist-vars x))))
      :flag cmr::termlist-vars)))


(local
 (defsection fgl-ev-context-equiv-when-equiv-rel

   (defthmd fgl-ev-context-equiv-of-equiv-rel
     (implies (and (fgl-ev-theoremp (cmr::equiv-rel-term equiv))
                   (pseudo-fnsym-p equiv)
                   (fgl-ev-context-equiv (list equiv) x y))
              (fgl-ev (list equiv (pseudo-term-quote x) (pseudo-term-quote y)) nil))
     :hints(("Goal" :in-theory (e/d (;; fgl-ev-of-fncall-args
                                     fgl-ev-context-equiv-of-singleton)
                                    (fgl-ev-context-equiv-is-equal-of-fixes)))))



   ))


(local
 (defsection fgl-ev-context-fix-equal-by-eval

   (local (in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes)))

   (local (defthm member-equiv-contexts-implies-not-quote
            (implies (member-equal x (equiv-contexts-fix contexts))
                     (not (equal x 'quote)))
            :hints(("Goal" :in-theory (enable equiv-contexts-fix)))
            :rule-classes :forward-chaining))


   (local (defthm pseudo-fnsym-p-when-equiv-context-p
            (implies (and (symbolp x)
                          (not (equal x 'quote)))
                     (pseudo-fnsym-p x))
            :hints(("Goal" :in-theory (enable pseudo-fnsym-p)))))

   ;; (local (in-theory (disable pseudo-fnsym-p-of-equiv-context-when-atom)))

   ;; (local (defthm fgl-ev-context-equiv-some-by-eval
   ;;          (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
   ;;                                nil)
   ;;                        (member-equal fn (equiv-contexts-fix contexts))
   ;;                        (symbolp fn))
   ;;                   (fgl-ev-context-equiv-some contexts x y))
   ;;          :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-some
   ;;                                            equiv-contexts-fix
   ;;                                            fgl-ev-equiv-context-equiv-base)))))

   (local (defthm fgl-ev-context-equiv-by-eval
            (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
                                  nil)
                          (member-equal fn (equiv-contexts-fix contexts))
                          (symbolp fn))
                     (fgl-ev-context-equiv contexts x y))
            :hints(("Goal" :in-theory (e/d (fgl-ev-context-equiv-when-singleton)
                                           (fgl-ev-context-equiv-is-equal-of-fixes))
                    :use ((:instance fgl-ev-context-equiv-by-singleton
                           (equiv fn) (ctx contexts)))))
            ;; :hints(("Goal" :use ((:instance fgl-ev-context-equiv-suff
            ;;                       (trace (list x y))))
            ;;         :in-theory (e/d (fgl-ev-context-equiv-symm)
            ;;                         (fgl-ev-context-equiv-is-equal-of-fixes))))
            ))

   (defthmd fgl-ev-context-fix-equal-by-eval
     (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
                           nil)
                   (member-equal fn (equiv-contexts-fix contexts))
                   (symbolp fn))
              (equal (fgl-ev-context-fix contexts x)
                     (fgl-ev-context-fix contexts y)))
     :hints(("Goal" :in-theory (e/d (equal-of-fgl-ev-context-fix)
                                    (fgl-ev-context-equiv-is-equal-of-fixes))))
     ;; :hints (("goal" :use fgl-ev-context-equiv-by-eval
     ;;          :in-theory (disable fgl-ev-context-equiv-by-eval)))
     :rule-classes :forward-chaining)

  (defthm fgl-interp-equiv-refinementp-implies-context-fix
    (implies (and (fgl-interp-equiv-refinementp equiv contexts)
                  (pseudo-fnsym-p equiv)
                  (fgl-ev (list equiv (pseudo-term-quote lhs)
                                (pseudo-term-quote rhs))
                          nil))
             (equal (fgl-ev-context-fix contexts lhs)
                    (fgl-ev-context-fix contexts rhs)))
    :hints(("Goal" :in-theory (enable fgl-interp-equiv-refinementp
                                      fgl-ev-context-fix-equal-by-eval))))))


(local (acl2::use-trivial-ancestors-check))

(local (in-theory (disable acl2::rewrite-rule-term)))


(local
 (cmr::defthm-term-vars-flag
   (defthm fgl-ev-of-cons-non-term-var
     (implies (not (member v (cmr::term-vars x)))
              (equal (fgl-ev x (cons (cons v val) env))
                     (fgl-ev x env)))
     :hints ('(:expand ((cmr::term-vars x))
               :in-theory (enable fgl-ev-of-fncall-args
                                  fgl-ev-when-pseudo-term-call)))
     :flag cmr::term-vars)
   (defthm fgl-ev-list-of-cons-non-term-var
     (implies (not (member v (cmr::termlist-vars x)))
              (equal (fgl-ev-list x (cons (cons v val) env))
                     (fgl-ev-list x env)))
     :hints ('(:expand ((cmr::termlist-vars x))))
     :flag cmr::termlist-vars)))


(defthmd eval-alist-extension-p-transitive-append-3
  (implies (and (eval-alist-extension-p a (append c b))
                (eval-alist-extension-p b d))
           (eval-alist-extension-p a (append c d)))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-1))))

(defsection iff-forall-extensions
  (defun-sk iff-forall-extensions (obj term eval-alist)
    (forall (ext)
            (implies (eval-alist-extension-p ext eval-alist)
                     (iff (fgl-ev term ext)
                          obj)))
    :rewrite :direct)

  (acl2::defquantexpr iff-forall-extensions
    :predicate (iff-forall-extensions obj term eval-alist)
    :quantifier :forall
    :witnesses ((ext (iff-forall-extensions-witness
                      obj term eval-alist)))
    :expr (implies (eval-alist-extension-p ext eval-alist)
                   (iff* (fgl-ev term ext)
                         obj))
    :instance-rulename iff-forall-extensions-instancing
    :wcp-witness-rulename iff-forall-extensions-witnessing)



  (acl2::defexample iff-forall-extensions-fgl-ev-example
    :pattern (fgl-ev x ext)
    :templates (ext)
    :instance-rules (iff-forall-extensions-instancing))

  (acl2::defexample iff-forall-extensions-fgl-ev-list-example
    :pattern (fgl-ev-list x ext)
    :templates (ext)
    :instance-rules (iff-forall-extensions-instancing))

  (in-theory (disable iff-forall-extensions
                      iff-forall-extensions-necc))

  (acl2::def-witness-ruleset iff-forall
    '(iff-forall-extensions-instancing
      iff-forall-extensions-witnessing
      iff-forall-extensions-fgl-ev-example
      iff-forall-extensions-fgl-ev-list-example))

  (acl2::def-witness-ruleset context-equiv-forall
    '(iff-forall fgl-ev-context-equiv-forall))

  (defcong iff equal (iff-forall-extensions obj term eval-alist) 1
    :hints (("goal" :cases ((iff-forall-extensions obj term eval-alist)))
            (acl2::witness :ruleset iff-forall)))

  (defcong fgl-ev-iff-equiv equal (iff-forall-extensions obj term eval-alist) 2
    :hints (("goal" :cases ((iff-forall-extensions obj term eval-alist))
             :in-theory (enable iff*))
            (acl2::witness :ruleset iff-forall)
            (and stable-under-simplificationp
                 '(:use ((:instance fgl-ev-iff-equiv-necc
                          (x term) (y term-equiv)
                          (env ext0)))))))

  (defthm fgl-ev-context-equiv-forall-extensions-when-iff
    (iff (fgl-ev-context-equiv-forall-extensions
          '(iff) obj term eval-alist)
         (iff-forall-extensions obj term eval-alist))
    :hints ((acl2::witness :ruleset context-equiv-forall)))

  ;; (local (defthm iff-forall-extensions-when-extension
  ;;          (implies (and (iff-forall-extensions obj term (append minor major0))
  ;;                        (eval-alist-extension-p major1 major0))
  ;;                   (iff-forall-extensions obj term (append minor major1)))
  ;;          :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
  ;;                  (acl2::witness :ruleset iff-forall))))

  ;; (acl2::definstantiate fgl-ev-theoremp-instancing
  ;;   :predicate (fgl-ev-theoremp term)
  ;;   :vars (alist)
  ;;   :expr (fgl-ev term alist)
  ;;   :hints ('(:use ((:instance fgl-ev-falsify (x term) (a alist))))))

  ;; (acl2::defexample fgl-ev-theoremp-fgl-ev-example
  ;;   :pattern (fgl-ev x alist)
  ;;   :templates (alist)
  ;;   :instance-rules (fgl-ev-theoremp-instancing))

  ;; (acl2::defexample fgl-ev-theoremp-fgl-ev-list-example
  ;;   :pattern (fgl-ev-list x alist)
  ;;   :templates (alist)
  ;;   :instance-rules (fgl-ev-theoremp-instancing))

  (local (defthm fgl-ev-of-equal-lemma
           (implies (equal (pseudo-fnsym-fix fn) 'equal)
                    (equal (fgl-ev (list fn x y) a)
                           (equal (fgl-ev x a) (fgl-ev y a))))
           :hints(("Goal" :in-theory (enable pseudo-fnsym-fix)))))




  (local (in-theory (enable fgl-ev-context-fix-equal-by-eval)))

  (local (defthm member-equiv-contexts-implies-not-quote
            (implies (member-equal x (equiv-contexts-fix contexts))
                     (not (equal x 'quote)))
            :hints(("Goal" :in-theory (enable equiv-contexts-fix)))
            :rule-classes :forward-chaining))


  (defthm iff-forall-extensions-relieve-hyps-consp
    (implies (and (Consp hyps)
                  (iff-forall-extensions
                   t (car hyps) (append minor major1))
                  (iff-forall-extensions
                   t (conjoin (cdr hyps)) (append minor major2))
                  (eval-alist-extension-p major2 major1))
             (iff-forall-extensions
              t (conjoin hyps) (append minor major2)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
                                       fgl-ev-conjoin-when-consp))
            (acl2::witness :ruleset iff-forall)))

  (defthm iff-forall-extensions-relieve-hyps-empty
    (implies (not (Consp hyps))
             (iff-forall-extensions
              t (conjoin hyps) eval-alist))
    :hints (("goal"
             :in-theory (enable conjoin iff-forall-extensions))))

  (defthm iff-forall-extensions-relieve-hyp-synp
    (implies (mv-nth 0 (fgl-interp-match-synp hyp))
             (iff-forall-extensions
              t hyp eval-alist))
    :hints(("Goal" :in-theory (enable iff-forall-extensions
                                      fgl-interp-match-synp))))


  (local (defthm iff-forall-extensions-of-if-true-equiv
           (implies (and (iff-forall-extensions t test (append minor-bindings major-bindings1))
                         (fgl-ev-context-equiv-forall-extensions
                          contexts then-res then (append minor-bindings major-bindings2))
                         (equal (fgl-ev-context-fix contexts then-res)
                                (fgl-ev-context-fix contexts res))
                         ;; (fgl-ev-context-equiv-forall-extensions
                         ;;  contexts else-res else (append minor-bindings major-bindings3))
                         (eval-alist-extension-p major-bindings2 major-bindings1)
                         (eval-alist-extension-p major-bindings3 major-bindings2))
                    (fgl-ev-context-equiv-forall-extensions
                     contexts res (pseudo-term-fncall 'if (list test then else))
                     (append minor-bindings major-bindings3)))
           :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
                   (acl2::witness :ruleset context-equiv-forall))))

  (local (defthm iff-forall-extensions-of-if-false-equiv
           (implies (and (iff-forall-extensions nil test (append minor-bindings major-bindings1))
                         ;; (fgl-ev-context-equiv-forall-extensions
                         ;;  contexts then-res then (append minor-bindings major-bindings2))
                         (fgl-ev-context-equiv-forall-extensions
                          contexts else-res else (append minor-bindings major-bindings2))
                         (equal (fgl-ev-context-fix contexts else-res)
                                (fgl-ev-context-fix contexts res))
                         (eval-alist-extension-p major-bindings2 major-bindings1)
                         (eval-alist-extension-p major-bindings3 major-bindings2))
                    (fgl-ev-context-equiv-forall-extensions
                     contexts res (pseudo-term-fncall 'if (list test then else))
                     (append minor-bindings major-bindings3)))
           :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
                   (acl2::witness :ruleset context-equiv-forall))))

  (local (defthm eval-under-iff-when-boolean-fix
           (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
             (implies (and ok
                           (fgl-object-case boolfix :g-concrete))
                      (iff (fgl-object-eval testobj env)
                           (g-concrete->val boolfix))))
           :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-fix fgl-object-eval)))))


  (defthm fgl-ev-context-equiv-forall-extensions-of-if-nonbranching-true
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
                    (fgl-object-case boolfix :g-concrete)
                    (g-concrete->val boolfix)
                    (fgl-ev-context-equiv-forall-extensions
                     (fgl-interp-test-equiv-contexts contexts)
                     (fgl-object-eval testobj env)
                     test (append minor-bindings major-bindings1))
                    (fgl-ev-context-equiv-forall-extensions
                     contexts then-eval then (append minor-bindings major-bindings2))
                    (eval-alist-extension-p major-bindings2 major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts
                then-eval
                (pseudo-term-fncall 'if (list test then else))
                (append minor-bindings major-bindings2))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
                                       fgl-interp-test-equiv-contexts))
            ;; (acl2::witness :ruleset context-equiv-forall)
            ))

  (defthm fgl-ev-context-equiv-forall-extensions-of-if-nonbranching-false
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
                    (fgl-object-case boolfix :g-concrete)
                    (not (g-concrete->val boolfix))
                    (fgl-ev-context-equiv-forall-extensions
                     (fgl-interp-test-equiv-contexts contexts)
                     (fgl-object-eval testobj env)
                     test (append minor-bindings major-bindings1))
                    (fgl-ev-context-equiv-forall-extensions
                     contexts else-eval else (append minor-bindings major-bindings2))
                    (eval-alist-extension-p major-bindings2 major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts
                else-eval
                (pseudo-term-fncall 'if (list test then else))
                (append minor-bindings major-bindings2))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
                                       fgl-interp-test-equiv-contexts))
            ;; (acl2::witness :ruleset context-equiv-forall)
            ))


  (defthm fgl-ev-context-equiv-forall-extensions-of-or-nonbranching-true
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
                    (fgl-object-case boolfix :g-concrete)
                    (g-concrete->val boolfix)
                    (fgl-ev-context-equiv-forall-extensions
                     (fgl-interp-or-test-equiv-contexts contexts)
                     (fgl-object-eval testobj env)
                     test bindings))
               (fgl-ev-context-equiv-forall-extensions
                contexts
                (fgl-object-eval testobj env)
                (pseudo-term-fncall 'if (list test test else))
                bindings)))
    :hints (("goal" :in-theory (enable fgl-interp-or-test-equiv-contexts
                                       ))
            (acl2::witness :ruleset context-equiv-forall)
            ))

  (defthm fgl-ev-context-equiv-forall-extensions-of-or-nonbranching-false
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
                    (fgl-object-case boolfix :g-concrete)
                    (not (g-concrete->val boolfix))
                    (fgl-ev-context-equiv-forall-extensions
                     (fgl-interp-or-test-equiv-contexts contexts)
                     (fgl-object-eval testobj env)
                     test (append minor-bindings major-bindings1))
                    (fgl-ev-context-equiv-forall-extensions
                     contexts else-eval else (append minor-bindings major-bindings2))
                    (eval-alist-extension-p major-bindings2 major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts
                else-eval
                (pseudo-term-fncall 'if (list test then else))
                (append minor-bindings major-bindings2))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
                                       fgl-interp-or-test-equiv-contexts))
            (acl2::witness :ruleset context-equiv-forall)
            ))

  (local (defthm sub-alistp-of-cons-unbound
           (implies (not (hons-assoc-equal var x))
                    (acl2::sub-alistp x (cons (cons var val) x)))
           :hints(("Goal" :in-theory (enable sub-alistp-by-witness)))))

  (local
   (defthmd fgl-ev-context-equiv-of-equiv-rel-equiv-contexts-from-equiv
     (implies (and (fgl-ev-theoremp (cmr::equiv-rel-term equiv))
                   (pseudo-fnsym-p equiv)
                   (fgl-ev-context-equiv (equiv-contexts-from-equiv equiv) x y))
              (fgl-ev (list equiv (pseudo-term-quote x) (pseudo-term-quote y)) nil))
     :hints(("Goal" :in-theory (e/d (;; fgl-ev-of-fncall-args
                                     equiv-contexts-from-equiv
                                     fgl-ev-context-equiv-of-singleton)
                                    (fgl-ev-context-equiv-is-equal-of-fixes))))))

  (defthmd iff-equiv-forall-extensions-equiv-binding-hyp
    (implies (and (fgl-ev-iff-equiv hyp (list equiv (pseudo-term-var var) term))
                  (pseudo-fnsym-p equiv)
                  (pseudo-var-p var)
                  (fgl-ev-theoremp (cmr::equiv-rel-term equiv))
                  (fgl-ev-context-equiv-forall-extensions
                   (equiv-contexts-from-equiv equiv)
                   obj term (append minor major))
                  (not (hons-assoc-equal var minor))
                  (not (hons-assoc-equal var major)))
             (iff-forall-extensions t hyp (append minor (cons (cons var obj) major))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-3
                                       fgl-interp-or-test-equiv-contexts
                                       fgl-ev-of-fncall-args
                                       hons-assoc-equal-when-sub-alistp
                                       fgl-ev-context-equiv-of-equiv-rel-equiv-contexts-from-equiv))
            (acl2::witness :ruleset context-equiv-forall)
            ))

  (defthm iff-equiv-forall-extensions-check-equivbind-hyp
    (b* (((mv var term equiv) (check-equivbind-hyp hyp interp-st state)))
      (implies (and var
                    (fgl-ev-meta-extract-global-facts :state st)
                    (equal (w st) (w state))
                    (fgl-ev-context-equiv-forall-extensions
                     (equiv-contexts-from-equiv equiv)
                     obj term (append minor major))
                    (not (hons-assoc-equal var minor))
                    (not (hons-assoc-equal var major)))
               (iff-forall-extensions t hyp (append minor (cons (cons var obj) major)))))
    :hints (("goal" :use ((:instance iff-equiv-forall-extensions-equiv-binding-hyp
                           (var (mv-nth 0 (check-equivbind-hyp hyp interp-st state)))
                           (term (mv-nth 1 (check-equivbind-hyp hyp interp-st state)))
                           (equiv (mv-nth 2 (check-equivbind-hyp hyp interp-st state)))))))))



(define iff?-forall-extensions ((contexts equiv-contextsp)
                                obj term eval-alist)
  :verify-guards nil
  (if (member-eq 'unequiv (equiv-contexts-fix contexts))
      t
    (iff-forall-extensions obj term eval-alist))
  ///
  (local (defthm iff-forall-extensions-when-extension
           (implies (and (iff-forall-extensions obj term (append minor major0))
                         (eval-alist-extension-p major1 major0))
                    (iff-forall-extensions obj term (append minor major1)))
           :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
                   (acl2::witness :ruleset iff-forall))))

  (defthm iff?-forall-extensions-of-fgl-interp-test
    (implies (and (fgl-ev-context-equiv-forall-extensions
                   (fgl-interp-test-equiv-contexts contexts)
                   x-interp-ev
                   x
                   (append minor-bindings major-bindings1))
                  (iff* x-interp-simp-ev x-interp-ev)
                  (eval-alist-extension-p major-bindings2 major-bindings1))
             (iff?-forall-extensions
              contexts
              x-interp-simp-ev
              x
              (append minor-bindings major-bindings2)))
    :hints(("Goal" :in-theory (enable iff?-forall-extensions
                                      fgl-interp-test-equiv-contexts))))

  (defthm iff?-forall-extensions-of-iff
    (equal (iff?-forall-extensions '(iff) obj term eval-alist)
           (iff-forall-extensions obj term eval-alist)))


  (defthm iff?-forall-extensions-of-if
    (implies (and (iff?-forall-extensions contexts test-res test (append minor-bindings major-bindings1))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts then-res then (append minor-bindings major-bindings2))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts else-res else (append minor-bindings major-bindings3))
                  (equal (fgl-ev-context-fix contexts res)
                         (fgl-ev-context-fix contexts (if* test-res then-res else-res)))
                  (eval-alist-extension-p major-bindings2 major-bindings1)
                  (eval-alist-extension-p major-bindings3 major-bindings2)
                  (eval-alist-extension-p major-bindings4 major-bindings3))
             (fgl-ev-context-equiv-forall-extensions
              contexts res (pseudo-term-fncall 'if (list test then else))
              (append minor-bindings major-bindings4)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-if-false
    (implies (and (iff?-forall-extensions contexts nil test (append minor-bindings major-bindings1))
                  ;; (fgl-ev-context-equiv-forall-extensions
                  ;;  contexts then-res then (append minor-bindings major-bindings2))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts else-res else (append minor-bindings major-bindings3))
                  (eval-alist-extension-p major-bindings3 major-bindings1))
             (fgl-ev-context-equiv-forall-extensions
              contexts else-res (pseudo-term-fncall 'if (list test then else))
              (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-if-true
    (implies (and (iff?-forall-extensions contexts t test (append minor-bindings major-bindings1))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts then-res then (append minor-bindings major-bindings2))
                  ;; (fgl-ev-context-equiv-forall-extensions
                  ;;  contexts else-res else (append minor-bindings major-bindings3))
                  (eval-alist-extension-p major-bindings2 major-bindings1)
                  (eval-alist-extension-p major-bindings3 major-bindings2))
             (fgl-ev-context-equiv-forall-extensions
              contexts then-res (pseudo-term-fncall 'if (list test then else))
              (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-if-true-equiv
    (implies (and (iff?-forall-extensions contexts t test (append minor-bindings major-bindings1))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts then-res then (append minor-bindings major-bindings2))
                  (equal (fgl-ev-context-fix contexts then-res)
                         (fgl-ev-context-fix contexts res))
                  ;; (fgl-ev-context-equiv-forall-extensions
                  ;;  contexts else-res else (append minor-bindings major-bindings3))
                  (eval-alist-extension-p major-bindings2 major-bindings1)
                  (eval-alist-extension-p major-bindings3 major-bindings2))
             (fgl-ev-context-equiv-forall-extensions
              contexts res (pseudo-term-fncall 'if (list test then else))
              (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-if-false-equiv
    (implies (and (iff?-forall-extensions contexts nil test (append minor-bindings major-bindings1))
                  ;; (fgl-ev-context-equiv-forall-extensions
                  ;;  contexts then-res then (append minor-bindings major-bindings2))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts else-res else (append minor-bindings major-bindings2))
                  (equal (fgl-ev-context-fix contexts else-res)
                         (fgl-ev-context-fix contexts res))
                  (eval-alist-extension-p major-bindings2 major-bindings1)
                  (eval-alist-extension-p major-bindings3 major-bindings2))
             (fgl-ev-context-equiv-forall-extensions
              contexts res (pseudo-term-fncall 'if (list test then else))
              (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-implies-fgl-ev-context-equiv-forall-extensions
    (implies (and (iff?-forall-extensions contexts bfr-eval x eval-alist)
                  (member 'iff (equiv-contexts-fix contexts)))
             (fgl-ev-context-equiv-forall-extensions contexts bfr-eval x eval-alist))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall))))





(defsection equal-list-forall-extensions
  (defun-sk equal-list-forall-extensions (obj terms eval-alist)
    (forall (ext)
            (implies (eval-alist-extension-p ext eval-alist)
                     (equal (fgl-ev-list terms ext) obj)))
    :rewrite :direct)

  (acl2::defquantexpr equal-list-forall-extensions
    :predicate (equal-list-forall-extensions obj term eval-alist)
    :quantifier :forall
    :witnesses ((ext (equal-list-forall-extensions-witness
                      obj term eval-alist)))
    :expr (implies (eval-alist-extension-p ext eval-alist)
                   (equal (fgl-ev-list term ext)
                          obj))
    :instance-rulename equal-list-forall-extensions-instancing
    :wcp-witness-rulename equal-list-forall-extensions-witnessing)



  (acl2::defexample equal-list-forall-extensions-fgl-ev-example
    :pattern (fgl-ev x ext)
    :templates (ext)
    :instance-rules (equal-list-forall-extensions-instancing))

  (acl2::defexample equal-list-forall-extensions-fgl-ev-list-example
    :pattern (fgl-ev-list x ext)
    :templates (ext)
    :instance-rules (equal-list-forall-extensions-instancing))

  (in-theory (disable equal-list-forall-extensions
                      equal-list-forall-extensions-necc))

  (acl2::def-witness-ruleset equal-list-forall
    '(equal-list-forall-extensions-instancing
      equal-list-forall-extensions-witnessing
      equal-list-forall-extensions-fgl-ev-example
      equal-list-forall-extensions-fgl-ev-list-example))

  (acl2::def-witness-ruleset context-equiv-forall
    '(iff-forall fgl-ev-context-equiv-forall equal-list-forall))

  (defthm fgl-ev-context-equiv-forall-extensions-of-fncall-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
                    (equal-list-forall-extensions
                     args-obj x.args (append minor major1))
                    (fgl-ev-context-equiv
                     contexts obj (fgl-ev (cons x.fn (kwote-lst args-obj)) nil))
                    (eval-alist-extension-p major2 major1))
               (fgl-ev-context-equiv-forall-extensions
                contexts obj x (append minor major2))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
                                       fgl-ev-of-fncall-args))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm equal-list-forall-extensions-of-args
    (implies (and (consp args)
                  (fgl-ev-context-equiv-forall-extensions
                   nil first (car args) (append minor major0))
                  (equal-list-forall-extensions
                   rest (cdr args) (append minor major1))
                  (eval-alist-extension-p major1 major0)
                  (eval-alist-extension-p major2 major1))
             (equal-list-forall-extensions
              (cons first rest)
              args
              (append minor major2)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

    (defthm equal-list-forall-extensions-of-empty-args
      (implies (not (consp args))
               (equal-list-forall-extensions
                nil args alist))
      :hints(("Goal" :in-theory (enable equal-list-forall-extensions))))
    )



(define equal?-list-forall-extensions  ((contexts equiv-contextsp)
                                        obj terms eval-alist)
  :verify-guards nil
  (if (equal (equiv-contexts-fix contexts) nil)
      (equal-list-forall-extensions obj terms eval-alist)
    t)
  ///

  ;; (local (in-theory (disable equiv-contexts-fix-under-iff)))

  (local (defthm not-equiv-contexts-fix
           (implies (not (consp x))
                    (cmr::equiv-contexts-equiv x nil))
           :rule-classes :forward-chaining))

  (defthm fgl-ev-context-equiv-forall-extensions-of-fncall-term-2
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
                    (equal?-list-forall-extensions
                     (fgl-interp-lambda-arglist-equiv-contexts contexts)
                     args-obj x.args (append minor major1))
                    (fgl-ev-context-equiv
                     contexts obj (fgl-ev (cons x.fn (kwote-lst args-obj)) nil))
                    (eval-alist-extension-p major2 major1))
               (fgl-ev-context-equiv-forall-extensions
                contexts obj x (append minor major2))))
    :hints(("Goal" :in-theory (enable fgl-interp-lambda-arglist-equiv-contexts))))

  (defthm equal?-list-forall-extensions-of-args
    (implies (and (consp args)
                  (fgl-ev-context-equiv-forall-extensions
                   contexts first (car args) (append minor major0))
                  (equal?-list-forall-extensions
                   contexts rest (cdr args) (append minor major1))
                  (eval-alist-extension-p major1 major0)
                  (eval-alist-extension-p major2 major1))
             (equal?-list-forall-extensions
              contexts
              (cons first rest)
              args
              (append minor major2))))

    (defthm equal?-list-forall-extensions-of-empty-args
      (implies (not (consp args))
               (equal?-list-forall-extensions
                contexts nil args alist)))

    (local (defthm sub-alistp-append-when-sub-alistp-append-with-cons
             (implies (and (not (acl2::sub-alistp (append minor major) ext))
                           (not (hons-assoc-equal var major)))
                      (not (acl2::sub-alistp (append minor (cons (cons var val) major)) ext)))
             :hints(("Goal" :in-theory (enable sub-alistp-by-witness)))))

    (defthm fgl-ev-context-equiv-forall-extensions-interp-binder
      (b* (((pseudo-term-fncall form)))
        (implies (and (pseudo-term-case form :fncall)
                      (consp form.args)
                      (pseudo-term-case (car form.args) :var)
                      (equal free-var (pseudo-term-var->name (car form.args)))
                      (equal?-list-forall-extensions
                       (fgl-interp-lambda-arglist-equiv-contexts contexts)
                       arg-objs
                       (cdr form.args)
                       (append minor major1))
                      (not (hons-assoc-equal free-var major1))
                      (not (hons-assoc-equal free-var minor))
                      (equal (fgl-ev-context-fix
                              contexts
                              rhs-obj)
                             (fgl-ev-context-fix
                              contexts
                              (fgl-ev (list* form.fn
                                             (pseudo-term-quote rhs-obj)
                                             (kwote-lst arg-objs))
                                      nil))))
                 (fgl-ev-context-equiv-forall-extensions
                  contexts
                  rhs-obj form (append minor (cons (cons free-var rhs-obj) major1)))))
      :hints(("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
                                        fgl-ev-of-fncall-args
                                        fgl-interp-lambda-arglist-equiv-contexts))
             (acl2::witness :ruleset context-equiv-forall)))
    )







(defsection equal-bindinglist-forall-extensions
  (defun-sk equal-bindinglist-forall-extensions (obj bindings minor-alist major-alist)
    (forall (ext)
            (implies (eval-alist-extension-p ext major-alist)
                     (equal (fgl-ev-bindinglist-minmaj bindings minor-alist ext)
                            obj)))
    :rewrite :direct)


  (acl2::defquantexpr equal-bindinglist-forall-extensions
    :predicate (equal-bindinglist-forall-extensions obj bindings minor-alist major-alist)
    :quantifier :forall
    :witnesses ((ext (equal-bindinglist-forall-extensions-witness
                      obj bindings minor-alist major-alist)))
    :expr (implies (eval-alist-extension-p ext major-alist)
                     (equal (fgl-ev-bindinglist-minmaj bindings minor-alist ext)
                            obj))
    :instance-rulename equal-bindinglist-forall-extensions-instancing
    :wcp-witness-rulename equal-bindinglist-forall-extensions-witnessing)

  (acl2::defexample equal-bindinglist-forall-extensions-fgl-ev-example
    :pattern (fgl-ev x (append minor major))
    :templates (major)
    :instance-rules (equal-bindinglist-forall-extensions-instancing))

  (acl2::defexample equal-bindinglist-forall-extensions-fgl-ev-list-example
    :pattern (fgl-ev-list x (append minor major))
    :templates (major)
    :instance-rules (equal-bindinglist-forall-extensions-instancing))


  (acl2::def-witness-ruleset equal-bindinglist-forall
    '(equal-bindinglist-forall-extensions-instancing
      equal-bindinglist-forall-extensions-witnessing
      equal-bindinglist-forall-extensions-fgl-ev-example
      equal-bindinglist-forall-extensions-fgl-ev-list-example))

  (acl2::def-witness-ruleset context-equiv-forall
    '(iff-forall fgl-ev-context-equiv-forall equal-list-forall equal-bindinglist-forall))

  (in-theory (disable equal-bindinglist-forall-extensions
                      equal-bindinglist-forall-extensions-necc))

  (local (defthm sub-alistp-of-append-after
           (acl2::sub-alistp x (append x y))
           :hints (("goal" :in-theory (enable acl2::sub-alistp-when-witness)))))

  (local (defthm sub-alistp-of-append-after-transitive
           (implies (acl2::sub-alistp x y)
                    (acl2::sub-alistp x (append y z)))
           :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-2)))))

  (local
   (cmr::defthm-term-vars-flag
     (defthmd fgl-ev-of-append-extension
       (implies (eval-alist-extension-p a b)
                (equal (fgl-ev x (append b a))
                       (fgl-ev x a)))
       :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
       :flag cmr::term-vars)
     (defthmd fgl-ev-list-of-append-extension
       (implies (eval-alist-extension-p a b)
                (equal (fgl-ev-list x (append b a))
                       (fgl-ev-list x a)))
       :flag cmr::termlist-vars)))

  (local (defthm fgl-ev-of-append2-extension
           (implies (eval-alist-extension-p ext (append a b))
                    (equal (fgl-ev x (append a b exT))
                           (fgl-ev x ext)))
           :hints (("goal" :use ((:instance fgl-ev-of-append-extension
                                  (a ext) (b (append a b))))))))

  (defthm fgl-ev-context-equiv-forall-extensions-lambda
    (b* (((mv bindings body) (lambda-nest-to-bindinglist x)))
      (implies (and (pseudo-term-case x :lambda)
                    (equal-bindinglist-forall-extensions
                     bindings-obj bindings minor-bindings major-bindings1)
                    (fgl-ev-context-equiv-forall-extensions
                     contexts obj
                     body (append bindings-obj major-bindings2))
                    (eval-alist-extension-p major-bindings2 major-bindings1)
                    (alistp major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts obj x (append minor-bindings major-bindings2))))
    :hints (("goal" :in-theory (e/d (eval-alist-extension-p-transitive-append-2)
                                    (fgl-ev-when-pseudo-term-lambda)))
            (acl2::witness :ruleset fgl-ev-context-equiv-forall-extensions-witnessing)
            (and stable-under-simplificationp
                 '(:use ((:instance equal-bindinglist-forall-extensions-necc
                          (obj bindings-obj)
                          (bindings (mv-nth 0 (lambda-nest-to-bindinglist x)))
                          (minor-alist minor-bindings)
                          (major-alist major-bindings1)
                          (ext (append major-bindings2 ext0)))
                         (:instance fgl-ev-context-equiv-forall-extensions-necc
                          (term (mv-nth 1 (lambda-nest-to-bindinglist x)))
                          (eval-alist (append bindings-obj major-bindings2))
                          (ext (append bindings-obj major-bindings2 ext0))))))))

  (local
   (cmr::defthm-term-vars-flag
     (defthm fgl-ev-of-append-extension-2
       (implies (eval-alist-extension-p a b)
                (equal (fgl-ev x (append p b a))
                       (fgl-ev x (append p a))))
       :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
       :flag cmr::term-vars)
     (defthm fgl-ev-list-of-append-extension-2
       (implies (eval-alist-extension-p a b)
                (equal (fgl-ev-list x (append p b a))
                       (fgl-ev-list x (append p a))))
       :flag cmr::termlist-vars)))


  (defthm equal-bindinglist-forall-extensions-append
    (implies (and (consp bindings)
                  (equal-bindinglist-forall-extensions
                   minor-bindings-obj (cdr bindings)
                   (append (pairlis$ (cmr::binding->formals (car bindings)) actuals-obj) minor-bindings-ev)
                   major-bindings-ev)
                  (equal-list-forall-extensions
                   actuals-obj (cmr::binding->args (car bindings)) (append minor-bindings-ev major-bindings-ev0))
                  (eval-alist-extension-p major-bindings-ev major-bindings-ev0))
             (equal-bindinglist-forall-extensions
              minor-bindings-obj bindings minor-bindings-ev major-bindings-ev))
    :hints ((acl2::witness :ruleset equal-bindinglist-forall-extensions-witnessing)
            (and stable-under-simplificationp
                 '(
                   :use ((:instance equal-bindinglist-forall-extensions-necc
                          (obj minor-bindings-obj)
                          (bindings (cdr bindings))
                          (minor-alist
                           (append (pairlis$ (cmr::binding->formals (car bindings)) actuals-obj) minor-bindings-ev))
                          (major-alist major-bindings-ev)
                          (ext ext0))
                         (:instance equal-list-forall-extensions-necc
                          (obj actuals-obj)
                          (terms (cmr::binding->args (car bindings)))
                          (eval-alist (append minor-bindings-ev major-bindings-ev0))
                          (ext (append minor-bindings-ev major-bindings-ev ext0))))
                   :expand ((fgl-ev-bindinglist-minmaj bindings minor-bindings-ev ext0))))))

  (defthm equal-bindinglist-forall-extensions-atom-bindings
    (implies (and (not (consp bindings))
                  (alistp minor-bindings-obj))
             (equal-bindinglist-forall-extensions
              minor-bindings-obj bindings minor-bindings-obj major-bindings-ev))
    :hints (("goal" :expand ((equal-bindinglist-forall-extensions
                              minor-bindings-obj bindings minor-bindings-obj major-bindings-ev)
                             (:free (maj)
                              (fgl-ev-bindinglist-minmaj
                               bindings minor-bindings-obj
                               maj))))))
  )

(define equal?-bindinglist-forall-extensions ((contexts equiv-contextsp)
                                              obj bindings minor-alist major-alist)
  :verify-guards nil
  (if (equal (equiv-contexts-fix contexts) nil)
      (equal-bindinglist-forall-extensions obj bindings minor-alist major-alist)
    t)
  ///

  (defthm fgl-ev-context-equiv-forall-extensions-lambda-2
    (b* (((mv bindings body) (lambda-nest-to-bindinglist x)))
      (implies (and (pseudo-term-case x :lambda)
                    (equal?-bindinglist-forall-extensions
                    (fgl-interp-lambda-arglist-equiv-contexts contexts)
                    bindings-obj bindings minor-bindings major-bindings1)
                    (fgl-ev-context-equiv-forall-extensions
                     contexts obj
                     body (append bindings-obj major-bindings2))
                    (eval-alist-extension-p major-bindings2 major-bindings1)
                    (alistp major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts obj x (append minor-bindings major-bindings2))))
    :hints(("Goal" :in-theory (enable fgl-interp-lambda-arglist-equiv-contexts))))

  (defthm equal?-bindinglist-forall-extensions-append
    (implies (and (consp bindings)
                  (equal?-bindinglist-forall-extensions
                   contexts
                   minor-bindings-obj (cdr bindings)
                   (append (pairlis$ (cmr::binding->formals (car bindings)) actuals-obj) minor-bindings-ev)
                   major-bindings-ev)
                  (equal?-list-forall-extensions
                   contexts
                   actuals-obj (cmr::binding->args (car bindings)) (append minor-bindings-ev major-bindings-ev0))
                  (eval-alist-extension-p major-bindings-ev major-bindings-ev0))
             (equal?-bindinglist-forall-extensions
              contexts
              minor-bindings-obj bindings minor-bindings-ev major-bindings-ev))
    :hints(("Goal" :in-theory (enable equal?-list-forall-extensions))))

  (defthm equal?-bindinglist-forall-extensions-atom-bindings
    (implies (and (not (consp bindings))
                  (alistp minor-bindings-obj))
             (equal?-bindinglist-forall-extensions
              contexts minor-bindings-obj bindings minor-bindings-obj major-bindings-ev))))


(defsection fgl-interp-preserves-errmsg
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-errmsg
      :rules ((t (:add-concl (let ((errmsg (interp-st->errmsg interp-st)))
                               (implies errmsg
                                        (equal (interp-st->errmsg new-interp-st) errmsg))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))


(defsection bvar-db-ok-of-fgl-interp
  (defun-sk interp-st-bvar-db-ok (interp-st env)
    (forall n
            (b* ((bvar-db (interp-st->bvar-db interp-st))
                 (logicman (interp-st->logicman interp-st)))
              (implies (and (<= (base-bvar$a bvar-db) (nfix n))
                            (< (nfix n) (next-bvar$a bvar-db)))
                       (iff* (fgl-object-eval (get-bvar->term$a n bvar-db) env logicman)
                             (gobj-bfr-eval (bfr-var n) env logicman)))))
    :rewrite :direct)

  (in-theory (disable interp-st-bvar-db-ok))

  (local (defthm bfr-listp-of-append-when-each
           (implies (And (bfr-listp a)
                         (bfr-listp b))
                    (bfr-listp (append a b)))))

  (local (in-theory (disable not-member-of-append)))

  (local (defthmd fgl-object-bfrlist-of-get-bvar->term$a-aux
           (implies (and (not (member v (bvar-db-bfrlist-aux m bvar-db)))
                         (< (nfix n) (nfix m))
                         (<= (base-bvar$a bvar-db) (nfix n)))
                    (not (member v (fgl-object-bfrlist (get-bvar->term$a n bvar-db)))))
           :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)))))

  (local (defthm fgl-object-bfrlist-of-get-bvar->term$a
           (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db)))
                    (not (member v (fgl-object-bfrlist (get-bvar->term$a n bvar-db)))))
           :hints (("goal" :in-theory (enable bvar-db-bfrlist)
                    :use ((:instance fgl-object-bfrlist-of-get-bvar->term$a-aux
                           (m (next-bvar$a bvar-db))))))))

  (local (defthm bfr-listp-of-bvar-db-bfrlist-when-equal
           (implies (and (equal bvar-db (interp-st->bvar-db interp-st))
                         (interp-st-bfrs-ok interp-st))
                    (bfr-listp (bvar-db-bfrlist bvar-db)
                               (logicman->bfrstate (interp-st->logicman interp-st))))))

  (def-updater-independence-thm interp-st-bvar-db-ok-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (interp-st-bfrs-ok old)
                  (equal (interp-st->bvar-db new) (interp-st->bvar-db old)))
             (iff (interp-st-bvar-db-ok new env)
                  (interp-st-bvar-db-ok old env)))
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'interp-st-bvar-db-ok clause))
                        (other (if (eq (cadr lit) 'new) 'old 'new)))
                   `(:expand (,lit)
                     :use ((:instance interp-st-bvar-db-ok-necc
                            (interp-st ,other)
                            (n (interp-st-bvar-db-ok-witness . ,(cdr lit)))))
                     :in-theory (e/d (bfr-varname-p)
                                     (interp-st-bvar-db-ok-necc)))))))



  (local (Defthm gobj-bfr-eval-of-bfr-var
           (implies (bfr-varname-p n)
                    (equal (gobj-bfr-eval (bfr-var n logicman) env logicman)
                           (bfr-lookup n (fgl-env->bfr-vals env))))
           :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

  (defthm interp-st-bvar-db-ok-of-fgl-primitive-fncall-stub
    (b* (((mv ?successp ?ans ?new-interp-st ?new-state)
          (fgl-primitive-fncall-stub primfn origfn args interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (iff (interp-st-bvar-db-ok new-interp-st env)
                    (interp-st-bvar-db-ok interp-st env))))
    :hints (("goal" :in-theory (e/d (interp-st-bfrs-ok
                                     bfr-varname-p
                                     ;; note: bfr-lookup should take bfr-mode, not logicman!
                                     bfr-lookup)
                                    (interp-st-bvar-db-ok-necc))
             :use ((:instance interp-st-bvar-db-ok-necc
                    (interp-st interp-st)
                    (n (interp-st-bvar-db-ok-witness
                        (mv-nth 2 (fgl-primitive-fncall-stub primfn origfn args interp-st state))
                        env)))
                   (:instance interp-st-bvar-db-ok-necc
                    (interp-st (mv-nth 2 (fgl-primitive-fncall-stub primfn origfn args interp-st state)))
                    (n (interp-st-bvar-db-ok-witness interp-st env)))))
            (and stable-under-simplificationp
                 (let* ((lit (assoc 'interp-st-bvar-db-ok clause)))
                   `(:expand (,lit) )))))

  (defret interp-st-bvar-db-ok-of-fgl-rewrite-try-primitive
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-objectlist-bfrlist args) interp-st))
             (iff (interp-st-bvar-db-ok new-interp-st env)
                  (interp-st-bvar-db-ok interp-st env)))
    :hints(("Goal" :in-theory (enable fgl-rewrite-try-primitive)))
    :fn fgl-rewrite-try-primitive)

  (defthm interp-st-bvar-db-ok-of-fgl-meta-fncall-stub
    (b* (((mv ?successp ?rhs ?bindings ?new-interp-st ?new-state)
          (fgl-meta-fncall-stub primfn origfn args interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (iff (interp-st-bvar-db-ok new-interp-st env)
                    (interp-st-bvar-db-ok interp-st env))))
    :hints (("goal" :in-theory (e/d (interp-st-bfrs-ok
                                     bfr-varname-p
                                     ;; note: bfr-lookup should take bfr-mode, not logicman!
                                     bfr-lookup)
                                    (interp-st-bvar-db-ok-necc))
             :use ((:instance interp-st-bvar-db-ok-necc
                    (interp-st interp-st)
                    (n (interp-st-bvar-db-ok-witness
                        (mv-nth 3 (fgl-meta-fncall-stub primfn origfn args interp-st state))
                        env)))
                   (:instance interp-st-bvar-db-ok-necc
                    (interp-st (mv-nth 3 (fgl-meta-fncall-stub primfn origfn args interp-st state)))
                    (n (interp-st-bvar-db-ok-witness interp-st env)))))
            (and stable-under-simplificationp
                 (let* ((lit (assoc 'interp-st-bvar-db-ok clause)))
                   `(:expand (,lit) )))))

  (defthm interp-st-bvar-db-ok-of-fgl-binder-fncall-stub
    (b* (((mv ?successp ?rhs ?bindings ?rhs-contexts ?new-interp-st ?new-state)
          (fgl-binder-fncall-stub primfn fn args interp-st state)))
      (implies (interp-st-bfrs-ok interp-st)
               (iff (interp-st-bvar-db-ok new-interp-st env)
                    (interp-st-bvar-db-ok interp-st env))))
    :hints (("goal" :in-theory (e/d (interp-st-bfrs-ok
                                     bfr-varname-p
                                     ;; note: bfr-lookup should take bfr-mode, not logicman!
                                     bfr-lookup)
                                    (interp-st-bvar-db-ok-necc))
             :use ((:instance interp-st-bvar-db-ok-necc
                    (interp-st interp-st)
                    (n (interp-st-bvar-db-ok-witness
                        (mv-nth 4 (fgl-binder-fncall-stub primfn fn args interp-st state))
                        env)))
                   (:instance interp-st-bvar-db-ok-necc
                    (interp-st (mv-nth 4 (fgl-binder-fncall-stub primfn fn args interp-st state)))
                    (n (interp-st-bvar-db-ok-witness interp-st env)))))
            (and stable-under-simplificationp
                 (let* ((lit (assoc 'interp-st-bvar-db-ok clause)))
                   `(:expand (,lit) )))))

  (defcong logicman-equiv equal (bfr-var n logicman) 2
    :hints(("Goal" :in-theory (enable bfr-var))))


  (defret interp-st-bvar-db-ok-of-interp-st-add-term-bvar
    (implies (and (not (interp-st-bvar-db-ok interp-st env))
                  (interp-st-bfrs-ok interp-st))
             (not (interp-st-bvar-db-ok new-interp-st env)))
    :hints(("Goal" :in-theory (e/d (interp-st-add-term-bvar bfr-varname-p)
                                   (interp-st-bvar-db-ok-necc))
            :expand ((interp-st-bvar-db-ok interp-st env))
            :use ((:instance interp-st-bvar-db-ok-necc
                   (interp-st new-interp-st)
                   (n (interp-st-bvar-db-ok-witness interp-st env))))
            :cases ((bfr-varname-p (interp-st-bvar-db-ok-witness interp-st env)
                                   (interp-st->logicman interp-st)))))
    :otf-flg t
    :fn interp-st-add-term-bvar)

  (defret interp-st-bvar-db-ok-of-interp-st-add-term-bvar-unique
    (implies (and (not (interp-st-bvar-db-ok interp-st env))
                  (interp-st-bfrs-ok interp-st))
             (not (interp-st-bvar-db-ok new-interp-st env)))
    :hints(("Goal" :in-theory (e/d (interp-st-add-term-bvar-unique bfr-varname-p)
                                   (interp-st-bvar-db-ok-necc))
            :expand ((interp-st-bvar-db-ok interp-st env))
            :use ((:instance interp-st-bvar-db-ok-necc
                   (interp-st new-interp-st)
                   (n (interp-st-bvar-db-ok-witness interp-st env))))
            :cases ((bfr-varname-p (interp-st-bvar-db-ok-witness interp-st env)
                                   (interp-st->logicman interp-st)))))
    :otf-flg t
    :fn interp-st-add-term-bvar-unique)

  (local (in-theory (disable not)))

  (local
   (with-output
     :off (event)
     :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
     (std::defret-mutual-generate <fn>-bvar-db-ok-doesnt-get-fixed-somehow

       :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                     ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                     ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                     (interp-st                     (interp-st-bfrs-ok interp-st))
                     ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))

       :rules ((t (:add-concl (implies (not (interp-st-bvar-db-ok interp-st env))
                                       (not (interp-st-bvar-db-ok new-interp-st env))))
                  (:add-keyword :hints ('(:do-not-induct t)
                                        (let ((flag (find-flag-is-hyp clause)))
                                          (and flag
                                               (prog2$ (cw "flag: ~x0~%" flag)
                                                       '(:no-op t)))))))
               ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-objlist))))

       :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
       :mutual-recursion fgl-interp)))


  (define interp-st-bvar-db-ok* (interp-st env)
    :verify-guards nil
    (interp-st-bvar-db-ok interp-st env))

  (local (in-theory (enable interp-st-bvar-db-ok*)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-bvar-db-ok-implies-previous-ok

      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                    ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))

      :rules ((t (:add-concl (iff* (interp-st-bvar-db-ok new-interp-st env)
                                   (and* (interp-st-bvar-db-ok* new-interp-st env)
                                        (interp-st-bvar-db-ok interp-st env))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((or (:fnname fgl-rewrite-try-rules)
                   (:fnname fgl-rewrite-try-rule)
                   (:fnname fgl-rewrite-try-rewrite)
                   (:fnname fgl-rewrite-try-meta)
                   (:fnname fgl-rewrite-binder-try-rules)
                   (:fnname fgl-rewrite-binder-try-rule)
                   (:fnname fgl-rewrite-binder-try-rewrite)
                   (:fnname fgl-rewrite-binder-try-meta)
                   (:fnname fgl-rewrite-try-rules3))
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st))) :fgl-objlist))))

      :hints (("goal" :do-not-induct t
               :in-theory (enable and*)))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))

(def-updater-independence-thm interp-st-bvar-db-ok-of-update
  (implies (and (equal (interp-st-get :logicman new)
                       (interp-st-get :logicman old))
                (equal (interp-st-get :bvar-db new)
                       (interp-st-get :bvar-db old)))
           (equal (interp-st-bvar-db-ok new env) (interp-st-bvar-db-ok old env)))
  :hints (("goal" :Cases ((interp-st-bvar-db-ok new env))
           :expand ((interp-st-bvar-db-ok new env)
                    (interp-st-bvar-db-ok old env))
           :use ((:instance interp-st-bvar-db-ok-necc
                  (interp-st new)
                  (n (interp-st-bvar-db-ok-witness old env)))
                 (:instance interp-st-bvar-db-ok-necc
                  (interp-st old)
                  (n (interp-st-bvar-db-ok-witness new env)))))))


(defret interp-st-bvar-db-ok-of-add-term-bvar-implies
  (implies (and (interp-st-bvar-db-ok new-interp-st env)
                (equal logicman (interp-st->logicman new-interp-st)))
           (iff* (gobj-bfr-eval bfr env logicman)
                 (fgl-object-eval x env logicman)))
  :fn interp-st-add-term-bvar
  :hints(("Goal" :in-theory (enable interp-st-add-term-bvar)
          :use ((:instance interp-st-bvar-db-ok-necc
                 (interp-st new-interp-st)
                 (n (next-bvar (interp-st->bvar-db interp-st))))))))

(defret interp-st-bvar-db-ok-of-add-term-bvar-unique-implies
  (implies (and (interp-st-bvar-db-ok new-interp-st env)
                (equal logicman  (interp-st->logicman new-interp-st)))
           (iff* (gobj-bfr-eval bfr env logicman)
                 (fgl-object-eval x env logicman)))
  :fn interp-st-add-term-bvar-unique
  :hints(("Goal" :in-theory (enable interp-st-add-term-bvar-unique)
          :use ((:instance interp-st-bvar-db-ok-necc
                 (interp-st new-interp-st)
                 (n (next-bvar (interp-st->bvar-db interp-st))))
                (:instance interp-st-bvar-db-ok-necc
                 (interp-st new-interp-st)
                 (n (get-term->bvar x (interp-st->bvar-db interp-st))))))))

(defthm interp-st-bvar-db-ok-necc-reverse
  (implies (interp-st-bvar-db-ok interp-st env)
           (b* ((bvar-db (interp-st->bvar-db interp-st))
                (logicman (interp-st->logicman interp-st)))
             (implies (and (<= (base-bvar$a bvar-db) (nfix n))
                           (< (nfix n) (next-bvar$a bvar-db)))
                      (iff* (gobj-bfr-eval (bfr-var n) env logicman)
                            (fgl-object-eval (get-bvar->term$a n bvar-db) env logicman))))))



(defthm iff-forall-extensions-of-meta-extract-formula
  (implies (and (fgl-ev-meta-extract-global-facts :state state0)
                (equal (w state) (w state0)))
           (iff (iff-forall-extensions
                 obj (meta-extract-formula name state) eval-alist)
                obj))
  :hints ((and stable-under-simplificationp
               (if (assoc 'iff-forall-extensions clause)
                   '(:expand ((:free (obj term eval-alist)
                               (iff-forall-extensions obj term eval-alist))))
                 '(:use ((:instance iff-forall-extensions-necc
                          (obj nil)
                          (term (meta-extract-formula name state))
                          (ext eval-alist))
                         ))))))


(in-theory (disable interp-st-bvar-db-ok-necc))





(defret logicman-pathcond-eval-preserved-by-logicman-pathcond-assume
  (implies (and (logicman-pathcond-eval env pathcond)
                (bfr-eval x env)
                (not contradictionp))
           (logicman-pathcond-eval env new-pathcond logicman))
  :hints (("goal" :cases ((pathcond-enabledp pathcond))))
  :fn logicman-pathcond-assume)

(local (acl2::use-trivial-ancestors-check))


(acl2::set-case-split-limitations '(500 100000))

;; (local (in-theory (disable bfr-listp-when-not-member-witness)))

(defthm stack$a-minor-bindings-of-push-scratch
  (equal (stack$a-minor-bindings (stack$a-push-scratch obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                    stack$a-push-scratch))))



(defsection check-equiv-replacement-correct
  (local (std::set-define-current-function check-equiv-replacement))
  (local (in-theory (enable check-equiv-replacement)))


  (local (in-theory (disable kwote-lst)))

  (local (in-theory (enable fgl-ev-context-fix-equal-by-eval)))

  (local (in-theory (enable fgl-apply fgl-objectlist-eval)))
  (defret check-equiv-replacement-correct
    (implies (and ok
                  (xor negp (fgl-object-eval equiv-term env)))
             (equal (fgl-ev-context-fix contexts (fgl-object-eval equiv env))
                    (fgl-ev-context-fix contexts (fgl-object-eval x env)))))

  (defretd check-equiv-replacement-iff-equiv-correct
    (implies iff-equiv-p
             (equal (fgl-ev-context-fix contexts (fgl-object-eval x env))
                    (fgl-ev-context-fix contexts (and (fgl-object-eval equiv-term env) t)))))
  )

(defsection try-equivalences-correct
  (local (std::set-define-current-function try-equivalences))
  (local (in-theory (enable try-equivalences
                            check-equiv-replacement-iff-equiv-correct)))

  (defthm try-equivalences-of-pathcond-fix
    (equal (try-equivalences x bvars contexts (pathcond-fix pathcond) bvar-db logicman state)
           (try-equivalences x bvars contexts pathcond bvar-db logicman state)))

  ;; (local (in-theory (e/d (eval-equal-bit-of-logicman-pathcond-implies)
  ;;                        (eval-when-logicman-pathcond-implies))))

  (local (defthm bfr-eval-of-fgl-env->bfr-vars
           (equal (bfr-eval bfr (fgl-env->bfr-vals env))
                  (gobj-bfr-eval bfr env))
           :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

  (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

  ;; (local (in-theory (enable interp-st-bvar-db-ok-necc)))

  (defret try-equivalences-correct
    :pre-bind ((logicman (interp-st->logicman interp-st))
               (bvar-db (interp-st->bvar-db interp-st))
               (pathcond (interp-st->pathcond interp-st)))
    (implies (and ok
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (interp-st-bvar-db-ok interp-st env)
                  (interp-st-bfrs-ok interp-st)
                  (bvar-list-okp bvars (interp-st->bvar-db interp-st)))
             (equal (fgl-ev-context-fix
                     contexts
                     (fgl-object-eval new-x env))
                    (fgl-ev-context-fix
                     contexts
                     (fgl-object-eval x env))))
    :hints (("goal" :induct (len bvars)
             :in-theory (enable (:i len))
             :expand ((:free (logicman pathcond bvar-db) <call>)))
            (and stable-under-simplificationp
                 '(:use ((:instance eval-when-logicman-pathcond-implies
                          (x (bfr-var (nfix (car bvars)) (interp-st->logicman interp-st)))
                          (pathcond (interp-st->pathcond interp-st))
                          (logicman (interp-st->logicman interp-st))
                          (env (fgl-env->bfr-vals env))))
                   :in-theory (e/d (bool->bit)
                                   (eval-when-logicman-pathcond-implies))
                   :do-not-induct t)))))


(defsection try-equivalences-loop-correct
  (local (std::set-define-current-function try-equivalences-loop))
  (local (in-theory (enable try-equivalences-loop)))



  (defthm try-equivalences-loop-of-pathcond-fix
    (equal (try-equivalences-loop x contexts clk (pathcond-fix pathcond) bvar-db logicman state)
           (try-equivalences-loop x contexts clk pathcond bvar-db logicman state)))


  (defret try-equivalences-loop-correct
    :pre-bind ((logicman (interp-st->logicman interp-st))
               (bvar-db (interp-st->bvar-db interp-st))
               (pathcond (interp-st->pathcond interp-st)))
    (implies (and (not error)
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (interp-st-bvar-db-ok interp-st env)
                  (interp-st-bfrs-ok interp-st))
             (equal (fgl-ev-context-fix
                     contexts
                     (fgl-object-eval replacement env))
                    (fgl-ev-context-fix
                     contexts
                     (fgl-object-eval x env))))))




(defthm stack$a-minor-bindings-of-stack$a-set-term
  (equal (stack$a-minor-bindings (stack$a-set-term obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-term))))

(defthm stack$a-minor-bindings-of-stack$a-set-term-index
  (equal (stack$a-minor-bindings (stack$a-set-term-index obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-term-index))))

(defthm stack$a-minor-bindings-of-stack$a-push-frame
  (equal (stack$a-minor-bindings (stack$a-push-frame stack))
         nil)
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-push-frame))))

(defthm stack$a-minor-bindings-of-stack$a-set-rule
  (equal (stack$a-minor-bindings (stack$a-set-rule obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-rule))))

(defthm stack$a-minor-bindings-of-stack$a-set-phase
  (equal (stack$a-minor-bindings (stack$a-set-phase obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-phase))))

(defthm stack$a-minor-bindings-of-stack$a-set-bindings
  (equal (stack$a-minor-bindings (stack$a-set-bindings bindings stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-bindings))))

(defthm stack$a-minor-bindings-of-stack$a-set-minor-bindings
  (equal (stack$a-minor-bindings (stack$a-set-minor-bindings bindings stack))
         (fgl-object-bindings-fix bindings))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-minor-bindings))))

(defthm stack$a-minor-bindings-of-stack$a-add-minor-bindings
  (equal (stack$a-minor-bindings (stack$a-add-minor-bindings bindings stack))
         (append (fgl-object-bindings-fix bindings) (stack$a-minor-bindings stack)))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-add-minor-bindings))))

;; (defthm stack$a-bindings-of-stack$a-add-minor-bindings
;;   (equal (stack$a-bindings (stack$a-add-minor-bindings bindings stack))
;;          (stack$a-bindings stack))
;;   :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-add-minor-bindings))))

(defthm stack$a-bindings-of-stack$a-set-bindings
  (equal (stack$a-bindings (stack$a-set-bindings bindings stack))
         (fgl-object-bindings-fix bindings))
  :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-set-bindings))))

(defthm fgl-object-bindings-eval-of-append
  (equal (fgl-object-bindings-eval (append a b) env)
         (append (fgl-object-bindings-eval a env)
                 (fgl-object-bindings-eval b env)))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-eval))))

(defthm fgl-object-bindings-eval-of-pairlis$
  (implies (pseudo-var-list-p keys)
           (equal (fgl-object-bindings-eval (pairlis$ keys vals) env)
                  (pairlis$ keys (fgl-objectlist-eval vals env))))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-eval pairlis$ fgl-objectlist-eval default-car))))


(defthm fgl-object-bindings-eval-of-nil
  (equal (fgl-object-bindings-eval nil env) nil)
  :hints(("Goal" :in-theory (enable fgl-object-bindings-eval))))






(def-updater-independence-thm eval-alist-extension-p-of-interp-st-update
  (implies (and (stack-bindings-extension-p
                 (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
                 (fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old)))
                (eval-alist-extension-p
                 (fgl-object-bindings-eval
                  (stack$a-bindings
                   (fgl-major-stack-concretize
                    (interp-st->stack old) env (interp-st->logicman old)))
                  nil nil)
                 other))
           (eval-alist-extension-p
            (fgl-object-bindings-eval
             (stack$a-bindings
              (fgl-major-stack-concretize
               (interp-st->stack new) env (interp-st->logicman new)))
             nil nil)
            other))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-2
                                    stack$a-bindings
                                    stack-bindings-extension-p))))

(defun find-unused-label (basename num wrld)
  (declare (xargs :mode :program))
  (let ((sym (intern-in-package-of-symbol
              (concatenate 'string (symbol-name basename) (str::natstr num))
              basename)))
    (if (fgetprop sym 'acl2::label nil wrld)
        (find-unused-label basename (1+ num) wrld)
      sym)))

(defun defsection-unique-fn (name defsection-args wrld)
  (declare (xargs :mode :program))
  (b* ((label (find-unused-label
               (intern-in-package-of-symbol
                (concatenate 'string (symbol-name name) "-TRY") name)
               0 wrld)))
    `(defsection ,name
       (deflabel ,label)
       . ,defsection-args)))

(defmacro defsection-unique (name &rest args)
  `(make-event
    (defsection-unique-fn ',name ',args (w state))))

(local (defthm if*-of-not
         (equal (if* (not x) y z)
                (if* x z y))))


;; this dumb thing is important for urewrite-clause-proc in combination with my-by-hint-cp
(defthm if-t-nil
  (iff (if x t nil) x))

(local (defun quick-and-dirty-srs-off (cl1 ac)
         (declare (ignore cl1 ac)
                  (xargs :mode :logic :guard t))
         nil))

(local (defattach-system acl2::quick-and-dirty-srs quick-and-dirty-srs-off))


(define fgl-ev-list-context-fix ((contexts equiv-contextsp)
                                 x)
  (if (atom x)
      nil
    (cons (fgl-ev-context-fix contexts (car x))
          (fgl-ev-list-context-fix contexts (cdr x))))
  ///
  (local (defthm fgl-ev-list-context-fix-cases
           (equal (fgl-ev-list-context-fix (fgl-interp-lambda-arglist-equiv-contexts contexts) x)
                  (if (member 'unequiv (equiv-contexts-fix contexts))
                      (acl2::repeat (len x) (fgl-ev-context-fix '(unequiv) nil))
                    (true-list-fix x)))
           :hints(("Goal" :in-theory (enable len acl2::repeat true-list-fix
                                             fgl-interp-lambda-arglist-equiv-contexts)))))

  (local (defthm fgl-ev-list-context-fix-of-nil
           (equal (fgl-ev-list-context-fix nil x)
                  (true-list-fix x))))

  (local (in-theory (disable kwote-lst)))

  (local (defthm true-list-equiv-when-equal-true-list-fix
           (implies (equal (true-list-fix x) (true-list-fix y))
                    (acl2::list-equiv x y))
           :rule-classes :forward-chaining))

  (local (fty::deffixcong acl2::list-equiv equal (kwote-lst x) x
           :hints(("Goal" :in-theory (enable kwote-lst)))))

  (defun empty-mfc-ancestors (mfc state)
    (declare (xargs :stobjs state)
             (ignore state))
    (not (mfc-ancestors mfc)))

  (defthm fgl-interp-lambda-arglist-equiv-contexts-correct
    (implies (and
              (equal (fgl-ev-list-context-fix (fgl-interp-lambda-arglist-equiv-contexts contexts) args1)
                     (fgl-ev-list-context-fix (fgl-interp-lambda-arglist-equiv-contexts contexts) args2))
              (pseudo-fnsym-p fn)
              (syntaxp (empty-mfc-ancestors mfc state))
              (equal ans (fgl-ev-context-fix contexts (fgl-ev (cons fn (kwote-lst args2)) nil)))
              (syntaxp (case-match ans
                         (('fgl-ev-context-fix & ('fgl-ev . &)) nil)
                         (& t))))
             (equal (fgl-ev-context-fix contexts (fgl-ev (cons fn (kwote-lst args1)) nil))
                    ans))
    :hints(("Goal" :in-theory (enable fgl-interp-lambda-arglist-equiv-contexts))))

  (defthm fgl-ev-list-context-fix-of-cons
    (equal (fgl-ev-list-context-fix contexts (cons a b))
           (cons (fgl-ev-context-fix contexts a)
                 (fgl-ev-list-context-fix contexts b))))

  (defthm fgl-ev-list-context-fix-of-empty
    (equal (fgl-ev-list-context-fix contexts nil) nil))

  (defthm fgl-ev-list-context-fix-of-if*-cons
    (implies (consp c)
             (equal (fgl-ev-list-context-fix contexts (if* test (cons a b) c))
                    (cons (fgl-ev-context-fix contexts (if* test a (car c)))
                          (fgl-ev-list-context-fix contexts (if* test b (cdr c)))))))

  (defthm fgl-ev-list-context-fix-of-if*-cons-2
    (implies (consp c)
             (equal (fgl-ev-list-context-fix contexts (if* test c (cons a b)))
                    (cons (fgl-ev-context-fix contexts (if* test (car c) a))
                          (fgl-ev-list-context-fix contexts (if* test (cdr c) b)))))))


(local (defthm fgl-ev-when-iff-forall-extensions
         (implies (and (iff-forall-extensions t (conjoin hyps) al)
                       (eval-alist-extension-p al2 al))
                  (fgl-ev (conjoin hyps) al2))
         :hints (("goal" :in-theory (enable iff-forall-extensions-necc)))))

(local (defthm equal-of-context-fix-when-fgl-ev-forall-extensions
         (implies (fgl-ev-context-equiv-forall-extensions
                   rhs-equiv rhs-obj rhs eval-alist)
                  (equal (equal (fgl-ev-context-fix
                                 rhs-equiv rhs-obj)
                                (fgl-ev-context-fix
                                 rhs-equiv (fgl-ev rhs eval-alist)))
                         t))
         :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions-necc)))))

(local (defthm fgl-ev-context-fix-of-rewrite-rule-rhs
         (b* (((fgl-rule-rewrite rule))
              ((cmr::rewrite rw) rule.rule))
           (implies (and (fgl-ev (fgl-rule-term rule)
                                 (fgl-ev-falsify (fgl-rule-term rule)))
                         (equal (fgl-rule-kind rule) :rewrite)
                         (fgl-ev (conjoin rw.hyps) al)
                         (fgl-interp-equiv-refinementp rw.equiv contexts))
                    (equal (fgl-ev-context-fix
                            contexts
                            (fgl-ev rw.rhs al))
                           (fgl-ev-context-fix
                            contexts
                            (fgl-ev rw.lhs al)))))
         :hints (("goal" :use ((:instance fgl-ev-falsify
                                (x (fgl-rule-term rule))
                                (a al))))
                 (and stable-under-simplificationp
                      '(:expand ((fgl-rule-term rule))
                        :in-theory (enable fgl-ev-of-fncall-args))))))




(local (defthm fgl-ev-context-fix-of-binder-rewrite-rule-rhs
         (b* (((fgl-binder-rule-brewrite rule)))
           (implies (and (fgl-good-fgl-binder-rule-p rule)
                         (equal (fgl-binder-rule-kind rule) :brewrite)
                         (fgl-ev (conjoin rule.hyps) al)
                         (fgl-interp-equiv-refinementp rule.equiv contexts)
                         (equal (fgl-ev-context-fix
                                 (list rule.r-equiv)
                                 (fgl-ev rule.rhs al))
                                (fgl-ev-context-fix
                                 (list rule.r-equiv)
                                 rhs-obj))
                         (equal args-eval (fgl-ev-list rule.lhs-args al)))
                    (equal (fgl-ev-context-fix
                            contexts
                            (fgl-ev (cons rule.lhs-fn
                                          (cons (pseudo-term-quote
                                                 rhs-obj)
                                                (kwote-lst args-eval)))
                                    nil))
                           (fgl-ev-context-fix
                            contexts
                            rhs-obj))))
         :hints (("goal" :use ((:instance binder-rule-term-when-fgl-good-fgl-binder-rule-p
                                (x rule)
                                (a (cons (cons (fgl-binder-rule-free-var rule)
                                               rhs-obj)
                                         al)))
                               (:instance binder-rule-equiv-term-when-fgl-good-fgl-binder-rule-p
                                (x rule)
                                (a (fgl-ev-falsify (fgl-binder-rule-equiv-term rule)))))
                  :in-theory (disable binder-rule-term-when-fgl-good-fgl-binder-rule-p
                                      binder-rule-equiv-term-when-fgl-good-fgl-binder-rule-p))
                 (and stable-under-simplificationp
                      '(:expand ((fgl-binder-rule-term rule)
                                 (fgl-binder-rule-equiv-term rule))
                        :in-theory (enable fgl-ev-of-fncall-args
                                           fgl-ev-context-equiv-of-equiv-rel))))))

(local (defthmd pseudo-term-kind-of-cons
         (implies (pseudo-fnsym-p fn)
                  (equal (pseudo-term-kind (cons fn args))
                         :fncall))
         :hints(("Goal" :in-theory (enable pseudo-term-kind
                                           pseudo-term-fix)))))

(local (defthmd pseudo-term-call->args-of-cons
         (implies (pseudo-fnsym-p fn)
                  (equal (pseudo-term-call->args (cons fn args))
                         (pseudo-term-list-fix args)))
         :hints(("Goal" :in-theory (enable pseudo-term-call->args
                                           pseudo-term-fix
                                           pseudo-term-kind-of-cons)))))

(local (defret fgl-ev-of-fgl-unify-term/gobj-fn/args-pat-of-extension
         (implies (and flag
                       (bind-free '((env . env)
                                    (logicman . (interp-st->logicman interp-st))) (logicman env))
                       (equal bfrstate (logicman->bfrstate))
                       (eval-alist-extension-p ev-al
                                               (fgl-object-bindings-eval new-alist env))
                       (pseudo-fnsym-p pat-fn))
                  (equal (fgl-ev (cons pat-fn pat-args) ev-al)
                         (fgl-ev (pseudo-term-fncall x-fn
                                                     (kwote-lst (fgl-objectlist-eval x-args env)))
                                 nil)))
         :hints (("goal" :use ((:instance fgl-unify-term/gobj-fn/args-correct)
                               (:instance fgl-ev-of-extension-when-term-vars-bound
                                (x (cons pat-fn pat-args))
                                (b ev-al)
                                (a (fgl-object-bindings-eval new-alist env))))
                  :expand ((term-vars (cons pat-fn pat-args)))
                  :in-theory (e/d (pseudo-term-kind-of-cons
                                   pseudo-term-call->args-of-cons)
                                  (fgl-ev-of-extension-when-term-vars-bound
                                   fgl-ev-when-pseudo-term-fncall))))
         :fn fgl-unify-term/gobj-fn/args))


(local (defret fgl-ev-list-of-fgl-unify-term/gobj-list-pat-of-extension
         (implies (and flag
                       (bind-free '((env . env)
                                    (logicman . (interp-st->logicman interp-st))) (logicman env))
                       (equal bfrstate (logicman->bfrstate))
                       (eval-alist-extension-p ev-al
                                               (fgl-object-bindings-eval new-alist env)))
                  (equal (fgl-ev-list pat ev-al)
                         (fgl-objectlist-eval x env)))
         :hints (("goal" :use ((:instance fgl-unify-term/gobj-list-correct)
                               (:instance fgl-ev-list-of-extension-when-term-vars-bound
                                (x pat)
                                (b ev-al)
                                (a (fgl-object-bindings-eval new-alist env))))
                  :in-theory (e/d ()
                                  (fgl-ev-list-of-extension-when-term-vars-bound))))
         :fn fgl-unify-term/gobj-list))


(local (defthm fgl-ev-context-equiv-forall-extensions-of-const
         (implies (pseudo-term-case term :const)
                  (iff (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
                       (equal (fgl-ev-context-fix contexts obj)
                              (fgl-ev-context-fix contexts (pseudo-term-const->val term)))))
         :hints (("goal" :in-theory (e/d (fgl-ev-context-equiv-forall-extensions)
                                         (fgl-ev-context-equiv-forall-extensions-necc))
                  :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                         (ext eval-alist)))))))


(local (defthm fgl-ev-context-equiv-forall-extensions-of-boolean-fncall
         (implies (and (iff* bfr-eval (fgl-object-eval res-obj env))
                       (booleanp bfr-eval)
                       (fgl-ev-meta-extract-global-facts)
                       (equal w (w state)))
                  (equal (interp-st-boolean-fncall-p res-obj ist w)
                         (and* (hide (interp-st-boolean-fncall-p res-obj ist w))
                               (equal bfr-eval (fgl-object-eval res-obj env)))))
         :hints (("goal" :expand ((:free (x) (hide x)))
                  :in-theory (enable and* iff*)
                  :use ((:instance interp-st-boolean-fncall-p-correct
                         (x res-obj) (interp-st ist)))))))



(local (defthm len-of-fgl-ev-list
         (equal (len (fgl-ev-list x env))
                (len x))
         :hints(("Goal" :in-theory (enable len)))))


(defsection fgl-ev-argcontexts-equiv-forall-extensions
  (defun-sk fgl-ev-argcontexts-equiv-forall-extensions (contexts objs terms eval-alist)
    (forall (ext)
            (implies (eval-alist-extension-p ext eval-alist)
                     (fgl-ev-argcontexts-equiv contexts (fgl-ev-list terms ext) objs)))
    :rewrite :direct)

  (in-theory (disable fgl-ev-argcontexts-equiv-forall-extensions
                      fgl-ev-argcontexts-equiv-forall-extensions-necc))


  (defthm fgl-interp-term-argcontexts-equiv-lemma
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
                    (fgl-ev-argcontexts-equiv-forall-extensions
                     argcontexts
                     objs x.args (append minor-bindings major-bindings1))
                    (fgl-ev-argcontext-congruence-correct-p
                     contexts x.fn argcontexts (len x.args))
                    (equal (len objs) (len x.args))
                    (equal (fgl-ev-context-fix contexts
                                               (fgl-ev (cons x.fn (kwote-lst objs)) nil))
                           (fgl-ev-context-fix contexts result-obj))
                    (eval-alist-extension-p major-bindings2 major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts result-obj x (append minor-bindings major-bindings2))))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall-extensions-witnessing)
            (and stable-under-simplificationp
                 '(:use ((:instance fgl-ev-argcontext-congruence-correct-p-necc
                          (ctx contexts)
                          (arg-ctxs argcontexts)
                          (fn (pseudo-term-fncall->fn x))
                          (arity (len (pseudo-term-call->args x)))
                          (args2 objs)
                          (args1 (fgl-ev-list (pseudo-term-call->args x)
                                              ext0)))
                         (:instance fgl-ev-argcontexts-equiv-forall-extensions-necc
                          (contexts argcontexts)
                          (terms (pseudo-term-call->args x))
                          (eval-alist (append minor-bindings major-bindings1))
                          (ext ext0)))
                   :in-theory (e/d (fgl-ev-of-fncall-args
                                    eval-alist-extension-p-transitive-append-2)
                                   (fgl-ev-argcontext-congruence-correct-p-necc))))))

  (local (defthm eval-alist-extension-p-append-cons
           (implies (and (eval-alist-extension-p maj2 maj1)
                         (not (hons-assoc-equal var maj2))
                         (eval-alist-extension-p ext (append min (cons (cons var val) maj2))))
                    (eval-alist-extension-p ext (append min maj1)))
           :hints(("Goal" :in-theory (enable sub-alistp-by-witness)))))

  (defthm fgl-interp-binder-fncall-argcontexts-equiv-lemma
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
                    (consp x.args)
                    (pseudo-term-case (car x.args) :var)
                    (fgl-ev-argcontexts-equiv-forall-extensions
                     (equiv-argcontexts-rest argcontexts)
                     objs (cdr x.args) (append minor-bindings major-bindings1))
                    (fgl-ev-argcontext-congruence-correct-p
                     contexts x.fn argcontexts (len x.args))
                    (equal (len objs) (len (cdr x.args)))
                    (not (hons-assoc-equal (pseudo-term-var->name (car x.args)) minor-bindings))
                    (not (hons-assoc-equal (pseudo-term-var->name (car x.args)) major-bindings2))
                    (equal (fgl-ev-context-fix contexts
                                               (fgl-ev (cons x.fn (cons (pseudo-term-quote result-obj)
                                                                        (kwote-lst objs))) nil))
                           (fgl-ev-context-fix contexts result-obj))
                    (eval-alist-extension-p major-bindings2 major-bindings1))
               (fgl-ev-context-equiv-forall-extensions
                contexts result-obj x (append minor-bindings
                                              (cons (cons (pseudo-term-var->name (car x.args))
                                                          result-obj)
                                                    major-bindings2)))))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall-extensions-witnessing)
            (and stable-under-simplificationp
                 '(:use ((:instance fgl-ev-argcontext-congruence-correct-p-necc
                          (ctx contexts)
                          (arg-ctxs argcontexts)
                          (fn (pseudo-term-fncall->fn x))
                          (arity (len (pseudo-term-call->args x)))
                          (args2 (cons result-obj objs))
                          (args1 (fgl-ev-list (pseudo-term-call->args x)
                                              ext0)))
                         (:instance fgl-ev-argcontexts-equiv-forall-extensions-necc
                          (contexts (equiv-argcontexts-rest argcontexts))
                          (terms (cdr (pseudo-term-call->args x)))
                          (eval-alist (append minor-bindings major-bindings1))
                          (ext ext0))
                         )
                   :in-theory (e/d (fgl-ev-of-fncall-args
                                    len
                                    eval-alist-extension-p-transitive-append-2)
                                   (fgl-ev-argcontext-congruence-correct-p-necc))
                   :do-not-induct t)))
    :otf-flg t)

  (defthm fgl-interp-arglist-argcontexts-equiv-lemma
    (implies (and (fgl-ev-context-equiv-forall-extensions
                   (equiv-argcontexts-first argcontexts)
                   obj1 (car args)
                   (append minor-bindings major-bindings1))
                  (fgl-ev-argcontexts-equiv-forall-extensions
                   (equiv-argcontexts-rest argcontexts)
                   rest-objs (cdr args)
                   (append minor-bindings major-bindings2))
                  (consp args)
                  (eval-alist-extension-p major-bindings2 major-bindings1))
             (fgl-ev-argcontexts-equiv-forall-extensions
              argcontexts
              (cons obj1 rest-objs)
              args (append minor-bindings major-bindings2)))
    :hints (("goal" :expand ((fgl-ev-argcontexts-equiv-forall-extensions
                              argcontexts
                              (cons obj1 rest-objs)
                              args (append minor-bindings major-bindings2)))
             :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                    (contexts (equiv-argcontexts-first argcontexts))
                    (obj obj1) (term (car args))
                    (eval-alist (append minor-bindings major-bindings1))
                    (ext (fgl-ev-argcontexts-equiv-forall-extensions-witness
                          argcontexts
                          (cons obj1 rest-objs)
                          args (append minor-bindings major-bindings2))))
                   (:instance fgl-ev-argcontexts-equiv-forall-extensions-necc
                    (contexts (equiv-argcontexts-rest argcontexts))
                    (objs rest-objs) (terms (cdr args))
                    (eval-alist (append minor-bindings major-bindings2))
                    (ext (fgl-ev-argcontexts-equiv-forall-extensions-witness
                          argcontexts
                          (cons obj1 rest-objs)
                          args (append minor-bindings major-bindings2)))))
             :in-theory (enable eval-alist-extension-p-transitive-append-2))))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-empty
    (implies (not (consp args))
             (fgl-ev-argcontexts-equiv-forall-extensions argcontexts nil args eval-alist))
    :hints(("Goal" :in-theory (enable fgl-ev-argcontexts-equiv-forall-extensions)))))

(local (defthm len-of-fgl-objectlist-eval
         (equal (len (fgl-objectlist-eval x env))
                (len x))
         :hints(("Goal" :in-theory (enable len fgl-objectlist-eval)))))


(local (defthm fgl-ev-context-equiv-forall-extensions-of-extension
         (implies (and (fgl-ev-context-equiv-forall-extensions contexts obj x env1)
                       (eval-alist-extension-p env2 env1))
                  (fgl-ev-context-equiv-forall-extensions contexts obj x env2))
         :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-2))
                 (acl2::witness :ruleset context-equiv-forall))))


(local
 (defsection-unique fgl-interp-correct

   (defret interp-st->errmsg-equal-unreachable-of-<fn>-special
      (implies (and (not (equal (interp-st->errmsg interp-st) :unreachable))
                    (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
                    (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                            (interp-st->logicman interp-st))
                    (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                            (interp-st->logicman interp-st))
                    (interp-st-bfrs-ok interp-st))
               (not (equal (interp-st->errmsg new-interp-st)
                           :unreachable)))
      :fn fgl-rewrite-try-primitive)


   (defthm interp-st->errmsg-equal-unreachable-of-fgl-meta-fncall-stub-special
     (b* (((mv ?successp ?rhs ?bindings ?new-interp-st ?new-state)
           (fgl-meta-fncall-stub metafn origfn args interp-st state)))
       (implies (and (not (equal (interp-st->errmsg interp-st) :unreachable))
                     (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
                     (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                             (interp-st->logicman interp-st))
                     (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                             (interp-st->logicman interp-st))
                     (interp-st-bfrs-ok interp-st))
                (not (equal (interp-st->errmsg new-interp-st)
                            :unreachable)))))

   (defthm interp-st->errmsg-equal-unreachable-of-fgl-binder-fncall-stub-special
     (b* (((mv ?successp ?rhs ?bindings ?rhs-contexts ?new-interp-st ?new-state)
           (fgl-binder-fncall-stub metafn origfn args interp-st state)))
       (implies (and (not (equal (interp-st->errmsg interp-st) :unreachable))
                     (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
                     (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                             (interp-st->logicman interp-st))
                     (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                             (interp-st->logicman interp-st))
                     (interp-st-bfrs-ok interp-st))
                (not (equal (interp-st->errmsg new-interp-st)
                            :unreachable)))))

   (defthm interp-st->errmsg-equal-unreachable-of-fgl-primitive-fncall-stub-special
     (b* (((mv ?successp ?ans ?new-interp-st ?new-state)
           (fgl-primitive-fncall-stub primfn origfn args interp-st state)))
       (implies (and (not (equal (interp-st->errmsg interp-st) :unreachable))
                     (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
                     (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                             (interp-st->logicman interp-st))
                     (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                             (interp-st->logicman interp-st))
                     (interp-st-bfrs-ok interp-st))
                (not (equal (interp-st->errmsg new-interp-st)
                            :unreachable)))))





   (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

   (local (defthm fgl-rule-term-of-car-theoremp-when-fgl-good-fgl-rules-p
            (implies (and (fgl-good-fgl-rules-p rules)
                          (consp rules))
                     (fgl-ev-theoremp (fgl-rule-term (car rules))))
            :hints(("Goal" :in-theory (enable fgl-good-fgl-rules-p
                                              fgl-good-fgl-rule-p)))))

   (local (defthm fgl-good-fgl-rules-p-of-cdr
            (implies (fgl-good-fgl-rules-p x)
                     (fgl-good-fgl-rules-p (cdr x)))
            :hints(("Goal" :in-theory (enable fgl-good-fgl-rules-p)))))

   (local (defthm fgl-good-binder-rule-p-of-car-when-fgl-good-fgl-binder-rules-p
            (implies (and (fgl-good-fgl-binder-rules-p rules)
                          (consp rules))
                     (fgl-good-fgl-binder-rule-p (car rules)))
            :hints(("Goal" :in-theory (enable fgl-good-fgl-binder-rules-p)))))

   (local (defthm fgl-good-fgl-binder-rules-p-of-cdr
            (implies (fgl-good-fgl-binder-rules-p x)
                     (fgl-good-fgl-binder-rules-p (cdr x)))
            :hints(("Goal" :in-theory (enable fgl-good-fgl-binder-rules-p)))))

   (local (defthm bfr-listp-of-append-when-each
            (implies (And (bfr-listp a)
                          (bfr-listp b))
                     (bfr-listp (append a b)))))

   (local (in-theory (disable not-member-of-append)))

   (local (defthm if*-same
            (equal (if* test x x) x)
            :hints(("Goal" :in-theory (enable if*)))))

   (local (defthm fgl-object-eval-rewrite-with-fgl-object-concretize
            (implies (and (equal ev (double-rewrite (fgl-object-concretize x env)))
                          (syntaxp ;; (prog2$ (cw "~x0~%ev: ~x1~%"
                           ;;             'fgl-object-eval-rewrite-with-fgl-object-ev
                           ;;             ev)
                           (and (not (equal ev x))
                                (case-match ev
                                  (('fgl-object-concretize-fn xans & &)
                                   (not (equal xans x)))
                                  (& t))))
                          (equal eval (fgl-object-eval ev nil nil))
                          (syntaxp ;; (prog2$ (cw "eval: ~x0~%" eval)
                           (case-match eval
                             (('fgl-object-eval-fn ('fgl-object-concretize-fn xans & &) & &)
                              (not (equal xans x)))
                             (('fgl-object-eval-fn xans & &)
                              (not (equal xans x)))
                             (& t))))
                     (equal (fgl-object-eval x env) eval))))

   (local (defthm fgl-objectlist-eval-rewrite-with-fgl-objectlist-concretize
            (implies (and (equal ev (double-rewrite (fgl-objectlist-concretize x env)))
                          (syntaxp (and (not (equal ev x))
                                        (case-match ev
                                          (('fgl-objectlist-concretize-fn xans & &)
                                           (not (equal xans x)))
                                          (& t))))
                          (equal eval (fgl-objectlist-eval ev nil nil))
                          (syntaxp (case-match eval
                                     (('fgl-objectlist-eval-fn ('fgl-objectlist-concretize-fn xans & &) & &)
                                      (not (equal xans x)))
                                     (('fgl-objectlist-eval-fn xans & &)
                                      (not (equal xans x)))
                                     (& t))))
                     (equal (fgl-objectlist-eval x env) eval))))

   (local (defthm fgl-object-bindings-eval-rewrite-with-fgl-object-bindings-concretize
            (implies (and (equal ev (double-rewrite (fgl-object-bindings-concretize x env)))
                          (syntaxp (and (not (equal ev x))
                                        (case-match ev
                                          (('fgl-object-bindings-concretize-fn xans & &)
                                           (not (equal xans x)))
                                          (& t))))
                          (equal eval (fgl-object-bindings-eval ev nil nil))
                          (syntaxp (case-match eval
                                     (('fgl-object-bindings-eval-fn ('fgl-object-bindings-concretize-fn xans & &) & &)
                                      (not (equal xans x)))
                                     (('fgl-object-bindings-eval-fn xans & &)
                                      (not (equal xans x)))
                                     (& t))))
                     (equal (fgl-object-bindings-eval x env) eval))))

   (local (defthm fgl-objectlist-eval-when-consp
            (implies (consp x)
                     (Equal (fgl-objectlist-eval x env)
                            (cons (fgl-object-eval (car x) env)
                                  (fgl-objectlist-eval (cdr x) env))))
            :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
            :rule-classes ((:rewrite :backchain-limit-lst 0))))

   (local (defthm fgl-object-alist-eval-under-iff
            (iff (fgl-object-alist-eval x env)
                 (fgl-object-alist-fix x))
            :hints(("Goal" :induct (len x)
                    :in-theory (enable (:i len))
                    :expand  ((fgl-object-alist-eval x env)
                              (fgl-object-alist-fix x)))
                   '(:do-not '(preprocess)))))

   (local (defthm fgl-objectlist-eval-of-atom
            (implies (not (Consp x))
                     (equal (fgl-objectlist-eval x env logicman) nil))
            :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
            :rule-classes ((:rewrite :backchain-limit-lst 0))))


   (local (defthm len-when-not-consp
            (implies (not (consp x))
                     (equal (len x) 0))
            :hints(("Goal" :in-theory (enable len)))
            :rule-classes ((:rewrite :backchain-limit-lst 0))))

   (local (defthm len-equal-0
            (equal (equal (len x) 0)
                   (not (consp x)))
            :hints(("Goal" :in-theory (enable len)))))

   (local
    (defthm len-cinstlist-when-scratchobj-isomorphic-rw
      (implies (and (scratchobj-isomorphic y (double-rewrite x))
                    (syntaxp (not (equal y x)))
                    (scratchobj-case y :cinstlist))
               (equal (len (scratchobj-cinstlist->val x))
                      (len (scratchobj-cinstlist->val y))))))

   (local
    (defthm len-fgl-objlist-when-scratchobj-isomorphic-rw
      (implies (and (scratchobj-isomorphic y (double-rewrite x))
                    (syntaxp (not (equal y x)))
                    (scratchobj-case y :fgl-objlist))
               (equal (len (scratchobj-fgl-objlist->val x))
                      (len (scratchobj-fgl-objlist->val y))))))


   (local (defthm fgl-object-ev-of-scratchobj-fgl-obj->val
            (implies (double-rewrite (scratchobj-case x :fgl-obj))
                     (equal (fgl-object-concretize (scratchobj-fgl-obj->val x) env)
                            (scratchobj-fgl-obj->val (fgl-scratchobj-concretize x env))))
            :hints(("Goal" :in-theory (enable fgl-scratchobj-concretize)))))

   (local (defthm fgl-objectlist-ev-of-scratchobj-fgl-objlist->val
            (implies (double-rewrite (scratchobj-case x :fgl-objlist))
                     (equal (fgl-objectlist-concretize (scratchobj-fgl-objlist->val x) env)
                            (scratchobj-fgl-objlist->val (fgl-scratchobj-concretize x env))))
            :hints(("Goal" :in-theory (enable fgl-scratchobj-concretize)))))


   (local (defthm fgl-object-eval-of-alist-lookup
            (implies (pseudo-var-p x)
                     (equal (fgl-object-eval
                             (cdr (hons-assoc-equal x alist)) env)
                            (cdr (hons-assoc-equal x (fgl-object-bindings-eval alist env)))))
            :hints(("Goal" :in-theory (enable fgl-object-bindings-eval)))))

   (local (in-theory (disable lookup-in-fgl-object-bindings-eval)))

   (local (defthm fgl-object-bindings-eval-of-acons
            (implies (pseudo-var-p var)
                     (equal (fgl-object-bindings-eval (cons (cons var val) rest) env)
                            (cons (cons var (fgl-object-eval val env))
                                  (fgl-object-bindings-eval rest env))))
            :hints(("Goal" :in-theory (enable fgl-object-bindings-eval)))))

   (local (defthm fgl-scratchobj-concretize-of-stack$a-top-scratch
            (equal (fgl-scratchobj-concretize (stack$a-top-scratch stack) env)
                   (double-rewrite (stack$a-top-scratch (fgl-major-stack-concretize stack env))))
            :hints(("Goal" :in-theory (enable stack$a-top-scratch
                                              fgl-major-frame-concretize
                                              fgl-minor-frame-concretize)
                    :expand ((fgl-major-stack-concretize stack env)
                             (fgl-minor-stack-concretize
                              (major-frame->minor-stack (Car stack)) env)
                             (fgl-scratchlist-concretize
                              (minor-frame->scratch
                               (car (major-frame->minor-stack (Car stack))))
                              env)
                             (fgl-scratchobj-concretize '(:fgl-obj) env)
                             (fgl-object-concretize nil env))))))

   (local (in-theory (disable stack$a-open-nth-scratch)))

   (local (defthm stack$a-open-nth-scratch2
            (implies (and (syntaxp (quotep n))
                          (< (nfix n) (double-rewrite (stack$a-scratch-len stack))))
                     (equal (stack$a-nth-scratch n stack)
                            (if (zp n)
                                (stack$a-top-scratch stack)
                              (stack$a-nth-scratch (1- n)
                                                   (stack$a-pop-scratch stack)))))
            :hints (("goal" :use stack$a-open-nth-scratch))))

   (local (defthm fgl-object-bindings-concretize-of-stack$a-minor-bindings
            (equal (fgl-object-bindings-concretize (stack$a-minor-bindings stack) env)
                   (double-rewrite (stack$a-minor-bindings (fgl-major-stack-concretize stack env))))
            :hints(("Goal" :in-theory (enable fgl-major-frame-concretize
                                              fgl-minor-frame-concretize
                                              stack$a-minor-bindings)
                    :expand ((fgl-major-stack-concretize stack env)
                             (fgl-minor-stack-concretize
                              (major-frame->minor-stack (Car stack)) env))
                    :do-not-induct t))))

   (local (defthm lookup-present-of-stack$a-minor-bindings-of-major-stack-ev
            (iff (hons-assoc-equal k (stack$a-minor-bindings (fgl-major-stack-concretize stack env)))
                 (hons-assoc-equal k (stack$a-minor-bindings stack)))
            :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                              fgl-major-frame-concretize
                                              fgl-minor-frame-concretize)
                    :expand ((fgl-major-stack-concretize stack env)
                             (fgl-minor-stack-concretize
                              (major-frame->minor-stack (Car stack)) env))))))

   (local (defthm lookup-present-of-stack$a-bindings-of-major-stack-ev
            (iff (hons-assoc-equal k (stack$a-bindings (fgl-major-stack-concretize stack env)))
                 (hons-assoc-equal k (stack$a-bindings stack)))
            :hints(("Goal" :in-theory (enable stack$a-bindings
                                              fgl-major-frame-concretize)
                    :expand ((fgl-major-stack-concretize stack env))))))

   (local (defthm fgl-object-bindings-concretize-of-stack$a-bindings
            (equal (fgl-object-bindings-concretize (stack$a-bindings stack) env)
                   (double-rewrite (stack$a-bindings (fgl-major-stack-concretize stack env))))
            :hints(("Goal" :in-theory (enable fgl-major-frame-concretize
                                              stack$a-bindings)
                    :expand ((fgl-major-stack-concretize stack env))
                    :do-not-induct t))))

   (local (def-updater-independence-thm lookup-present-in-stack-bindings-when-major-stack-equiv-of-concretize
            (implies (and (bind-free '((env . env)))
                          (equal (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
                                 (fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old))))
                     (iff (hons-assoc-equal k (stack$a-bindings (interp-st->stack new)))
                          (hons-assoc-equal k (stack$a-bindings (interp-st->stack old)))))
            :hints (("goal" :use ((:instance lookup-present-of-stack$a-bindings-of-major-stack-ev
                                   (stack (interp-st->stack new))
                                   (logicman (interp-st->logicman new)))
                                  (:instance lookup-present-of-stack$a-bindings-of-major-stack-ev
                                   (stack (interp-st->stack old))
                                   (logicman (interp-st->logicman old))))
                     :in-theory (disable lookup-present-of-stack$a-bindings-of-major-stack-ev)))))

   (local (def-updater-independence-thm lookup-present-in-stack-minor-bindings-when-stack-equiv-except-top-bindings-of-concretize
            (implies (and (bind-free '((env . env)))
                          (stack-equiv-except-top-bindings
                           (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
                           (fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old))))
                     (iff (hons-assoc-equal k (stack$a-minor-bindings (interp-st->stack new)))
                          (hons-assoc-equal k (stack$a-minor-bindings (interp-st->stack old)))))
            :hints (("goal" :use ((:instance lookup-present-of-stack$a-minor-bindings-of-major-stack-ev
                                   (stack (interp-st->stack new))
                                   (logicman (interp-st->logicman new)))
                                  (:instance lookup-present-of-stack$a-minor-bindings-of-major-stack-ev
                                   (stack (interp-st->stack old))
                                   (logicman (interp-st->logicman old))))
                     :in-theory (disable lookup-present-of-stack$a-minor-bindings-of-major-stack-ev)))))

   (defcong stack-equiv-except-top-bindings equal (stack$a-top-scratch stack) 1
     :hints(("Goal" :in-theory (enable stack$a-top-scratch
                                       stack-equiv-except-top-bindings
                                       minor-stack-equiv-except-top-debug))))


   (defcong stack-equiv-except-top-bindings equal (stack$a-minor-bindings stack) 1
     :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                       stack-equiv-except-top-bindings))))

   (local (Defthm gobj-bfr-eval-of-scratchobj-bfr->val
            (implies (double-rewrite (scratchobj-case obj :bfr))
                     (equal (gobj-bfr-eval (scratchobj-bfr->val obj) env)
                            (scratchobj-bfr->val (fgl-scratchobj-concretize obj env))))
            :hints(("Goal" :in-theory (enable fgl-scratchobj-concretize)))))

   (local (Defthm bfr-eval-of-scratchobj-bfr->val
            (implies (double-rewrite (scratchobj-case obj :bfr))
                     (equal (bfr-eval (scratchobj-bfr->val obj) (fgl-env->bfr-vals env))
                            (scratchobj-bfr->val (fgl-scratchobj-concretize obj env))))
            :hints(("Goal" :in-theory (enable fgl-scratchobj-concretize gobj-bfr-eval)))))



   (defthm gobj-bfr-eval-of-boolean
     (implies (booleanp x)
              (equal (gobj-bfr-eval x env) x))
     :hints(("Goal" :in-theory (enable gobj-bfr-eval bfr-eval bfr-fix booleanp bfr->aignet-lit)))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (local (defthm bfr-eval-of-fgl-env->bfr-vars
            (equal (bfr-eval bfr (fgl-env->bfr-vals env))
                   (gobj-bfr-eval bfr env))
            :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

   (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval
                              if* cons-equal)))

   (local (in-theory (enable fgl-apply)))

   (local (defthm not-not-under-iff*
            (iff* (not (not x)) x)
            :hints(("Goal" :in-theory (enable not)))))

   (local (defthm if*-of-known
            (and (implies test
                          (equal (if* test a b) a))
                 (equal (if* nil a b) b))
            :hints(("Goal" :in-theory (enable if*)))))



   (local (defthm fgl-object-eval-when-g-ite-if*
            (implies (fgl-object-case x :g-ite)
                     (equal (fgl-object-eval x env)
                            (if* (fgl-object-eval (g-ite->test x) env)
                                 (fgl-object-eval (g-ite->then x) env)
                                 (fgl-object-eval (g-ite->else x) env))))
            :hints(("Goal" :in-theory (enable if*)))))

   (defcong iff equal (if* a b c) 1
     :hints(("Goal" :in-theory (enable if*))))

   (defcong iff iff (if* a b c) 2
     :hints(("Goal" :in-theory (enable if*))))

   (defcong iff iff (if* a b c) 3
     :hints(("Goal" :in-theory (enable if*))))

   (local (in-theory (disable fgl-object-eval-when-g-ite)))

   (local (def-updater-independence-thm logicman-pathcond-eval-of-interp-st-logicman-extension
            (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                          (logicman-pathcond-p pathcond (interp-st->logicman old)))
                     (equal (logicman-pathcond-eval env pathcond (interp-st->logicman new))
                            (logicman-pathcond-eval env pathcond (interp-st->logicman old))))))

   (defthm stack$a-bindings-of-stack$a-pop-scratch
     (equal (stack$a-bindings (stack$a-pop-scratch stack))
            (stack$a-bindings stack))
     :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-pop-scratch))))


   (local (in-theory (disable not)))

   (defconst *fgl-interp-correct-body*
     '(std::defret-generate <fn>-correct
        :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                      ((fgl-object-p x)               (interp-st-bfr-listp (fgl-object-bfrlist x)))
                      ((fgl-objectlist-p x)           (interp-st-bfr-listp (fgl-objectlist-bfrlist x)))
                    ((fgl-object-bindings-p x)      (interp-st-bfr-listp (fgl-object-bindings-bfrlist x)))
                      (interp-st                     (interp-st-bfrs-ok interp-st))
                      ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
                      (state                         (and (fgl-ev-meta-extract-global-facts :state st)
                                                          (equal (w st) (w state))
                                                          (fgl-formula-checks-stub st)
                                                          )))
        :rules ((t (:add-hyp (and (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                          (interp-st->constraint interp-st)
                                                          (interp-st->logicman interp-st))
                                  (interp-st-bvar-db-ok new-interp-st env)))

                   (:add-bindings
                    ((new-logicman (interp-st->logicman new-interp-st))
                     (logicman (interp-st->logicman interp-st))
                     (new-stack (interp-st->stack new-interp-st))
                     (stack (interp-st->stack interp-st))
                     (major-alist (fgl-object-bindings-eval (stack$a-bindings new-stack) env new-logicman))
                     (minor-alist (fgl-object-bindings-eval (stack$a-minor-bindings stack) env logicman))
                     (?eval-alist (append minor-alist major-alist)))))

                ((or (:fnname fgl-rewrite-try-rules)
                     (:fnname fgl-rewrite-try-rule)
                     (:fnname fgl-rewrite-try-rewrite)
                     (:fnname fgl-rewrite-try-meta)
                     (:fnname fgl-rewrite-binder-try-rules)
                     (:fnname fgl-rewrite-binder-try-rule)
                     (:fnname fgl-rewrite-binder-try-rewrite)
                     (:fnname fgl-rewrite-binder-try-meta)
                     (:fnname fgl-rewrite-try-rules3))
                 (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-objlist))
                 (:add-bindings
                  ((args (interp-st-top-scratch-fgl-objlist interp-st))
                   (?call (g-apply fn args)))))

                ((:fnname fgl-interp-add-constraints-for-substs)
                 (:push-hyp (and (not (pathcond-enabledp (interp-st->pathcond interp-st)))
                                 (equal (interp-st->equiv-contexts interp-st) '(iff)))))


                (t (:add-concl (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                       (interp-st->constraint new-interp-st)
                                                       new-logicman)))
                (t
                 (:push-hyp
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          logicman)))

                ;; ((:fnname fgl-interp-add-constraints-for-substs)
                ;;  (:pop-hyp))
                (t (:push-hyp (not (interp-st->errmsg interp-st))))


                (t (:add-concl ;; (implies (and (not (interp-st->errmsg interp-st))
                    ;;               (logicman-pathcond-eval (fgl-env->bfr-vals env)
                    ;;                                       (interp-st->pathcond interp-st)
                    ;;                                       logicman))
                    (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

                (t (:pop-hyp)
                   (:push-hyp
                    (not (interp-st->errmsg new-interp-st))))



                ((:fnname fgl-interp-test)
                 (:add-concl
                  ;; (iff* (gobj-bfr-eval xbfr env new-logicman)
                  ;;       (fgl-ev x eval-alist))
                  (iff?-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (gobj-bfr-eval xbfr env new-logicman) x eval-alist)))

                ((or (:fnname fgl-interp-term-equivs)
                     (:fnname fgl-interp-term-top)
                     (:fnname fgl-interp-term)
                     (:fnname fgl-interp-time$)
                     (:fnname fgl-interp-return-last)
                     ;; (:fnname fgl-interp-prog2)
                     (:fnname fgl-interp-narrow-equiv))
                 (:add-concl
                  (fgl-ev-context-equiv-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-eval xobj env new-logicman)
                   x eval-alist)))

                ((:fnname fgl-interp-fncall-special)
                 (:add-concl
                  (implies successp
                           (fgl-ev-context-equiv-forall-extensions
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (pseudo-term-fncall fn args) eval-alist))))

                ((:fnname fgl-interp-sat-check)
                 (:add-concl
                  (fgl-ev-context-equiv-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-eval xobj env new-logicman)
                   `(if ,x 't 'nil) eval-alist)))

                ((or (:fnname fgl-interp-assume)
                     (:fnname fgl-interp-fgl-interp-obj))
                 (:add-concl
                  (fgl-ev-context-equiv-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-eval ans env new-logicman)
                   nil eval-alist)))

                ;; ((:fnname fgl-interp-bind-var)
                ;;  (:add-concl
                ;;   (fgl-ev-context-equiv-forall-extensions
                ;;    (interp-st->equiv-contexts interp-st)
                ;;    (fgl-object-eval xobj env new-logicman)
                ;;    free-var eval-alist)))

                ((:fnname fgl-interp-binder)
                 (:add-concl
                  (fgl-ev-context-equiv-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-eval xobj env new-logicman)
                   form eval-alist)))


                ((:fnname fgl-interp-arglist)
                 (:add-concl
                  (fgl-ev-argcontexts-equiv-forall-extensions
                   argcontexts
                   (fgl-objectlist-eval arg-objs env new-logicman)
                   args eval-alist)))

                ((:fnname fgl-interp-lambda-arglist)
                 (:add-concl
                  (equal?-list-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-objectlist-eval arg-objs env new-logicman)
                   args eval-alist)))
                ((:fnname fgl-interp-bindinglist)
                 (:add-concl
                  (equal?-bindinglist-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-bindings-eval (stack$a-minor-bindings new-stack) env new-logicman)
                   bindings minor-alist major-alist)))

                ((or (:fnname fgl-interp-fncall)
                     (:fnname fgl-interp-fncall-casesplit))
                 (:add-concl
                  (equal (fgl-ev-context-fix
                          (interp-st->equiv-contexts interp-st)
                          (fgl-object-eval ans env new-logicman))
                         (fgl-ev-context-fix
                          (interp-st->equiv-contexts interp-st)
                          (fgl-ev (cons (pseudo-fnsym-fix fn)
                                        (kwote-lst
                                         (fgl-objectlist-eval args env logicman)))
                                  nil)))))
                ((:fnname fgl-interp-fncall-casesplit-branches)
                 (:add-concl
                  (equal (fgl-ev-context-fix
                          (interp-st->equiv-contexts interp-st)
                          (fgl-object-eval ans env new-logicman))
                         (fgl-ev-context-fix
                          (interp-st->equiv-contexts interp-st)
                          (fgl-ev (cons (pseudo-fnsym-fix fn)
                                        (kwote-lst
                                         (fgl-objectlist-eval (if* (gobj-bfr-eval testbfr env logicman)
                                                                   then-args
                                                                   else-args)
                                                              env logicman)))
                                  nil)))))

                ((:fnname fgl-maybe-interp-fncall-casesplit)
                 (:add-concl
                  (implies (gobj-bfr-eval test env logicman)
                           (and (equal (fgl-ev-context-fix
                                        (interp-st->equiv-contexts interp-st)
                                        (fgl-object-eval ans env new-logicman))
                                       (fgl-ev-context-fix
                                        (interp-st->equiv-contexts interp-st)
                                        (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                      (kwote-lst
                                                       (fgl-objectlist-eval args env logicman)))
                                                nil)))
                                (not unreachable)))))

                ((:fnname fgl-rewrite-fncall)
                 (:add-concl
                  (implies successp
                           (equal (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-object-eval ans env new-logicman))
                                  (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                 (kwote-lst
                                                  (fgl-objectlist-eval args env logicman)))
                                           nil))))))

                ((:fnname fgl-rewrite-binder-fncall)
                 (:add-concl
                  (implies successp
                           (equal (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-object-eval ans env new-logicman))
                                  (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                 (kwote-lst
                                                  (cons (fgl-object-eval ans env new-logicman)
                                                        (fgl-objectlist-eval args env logicman))))
                                           nil))))))

                ((:fnname fgl-rewrite-try-rule)
                 (:add-concl
                  (implies (and successp
                                (fgl-ev-theoremp (fgl-rule-term rule)))
                           (fgl-ev-context-equiv
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (fgl-object-eval call env logicman)))))

                ((:fnname fgl-rewrite-binder-try-rule)
                 (:add-concl
                  (implies (and successp
                                (fgl-good-fgl-binder-rule-p rule))
                           (fgl-ev-context-equiv
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (fgl-ev (cons (pseudo-fnsym-fix fn)
                                          (kwote-lst
                                           (cons (fgl-object-eval ans env new-logicman)
                                                 (fgl-objectlist-eval args env logicman))))
                                    nil)))))

                ((:fnname fgl-rewrite-apply-rule)
                 (:add-concl
                  (b* ((new-ev-al (fgl-object-bindings-eval new-bindings env new-logicman))
                       (ev-al (fgl-object-bindings-eval bindings env logicman)))
                    (implies successp
                             (and (eval-alist-extension-p
                                   new-ev-al ev-al)
                                  (fgl-ev (conjoin hyps) new-ev-al)
                                  (equal
                                   (fgl-ev-context-fix rhs-equiv
                                                       (fgl-object-eval ans env new-logicman))
                                   (fgl-ev-context-fix rhs-equiv
                                                       (fgl-ev rhs new-ev-al))))))
                  ))

                ((:fnname fgl-rewrite-try-rewrite)
                 (:add-concl
                  (implies (and successp
                                (fgl-rule-case rule :rewrite)
                                (fgl-ev-theoremp (fgl-rule-term rule)))
                           (fgl-ev-context-equiv
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (fgl-object-eval call env logicman)))))

                ((:fnname fgl-rewrite-binder-try-rewrite)
                 (:add-concl
                  (implies (and successp
                                (fgl-binder-rule-case rule :brewrite)
                                (fgl-good-fgl-binder-rule-p rule))
                           (fgl-ev-context-equiv
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (fgl-ev (cons (pseudo-fnsym-fix fn)
                                          (kwote-lst
                                           (cons (fgl-object-eval ans env new-logicman)
                                                 (fgl-objectlist-eval args env logicman))))
                                    nil)))))

                ((:fnname fgl-rewrite-try-meta)
                 (:add-concl
                  (implies (and successp)
                           (fgl-ev-context-equiv
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (fgl-object-eval call env logicman)))))

                ((:fnname fgl-rewrite-binder-try-meta)
                 (:add-concl
                  (implies (and successp)
                           (fgl-ev-context-equiv
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (fgl-ev (cons (pseudo-fnsym-fix fn)
                                          (kwote-lst
                                           (cons (fgl-object-eval ans env new-logicman)
                                                 (fgl-objectlist-eval args env logicman))))
                                    nil)))))

                ((:fnname fgl-rewrite-try-rules)
                 (:add-concl
                  (implies (and successp
                                (fgl-good-fgl-rules-p rules))
                           (equal (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-object-eval ans env new-logicman))
                                  (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-object-eval
                                    call
                                    env logicman))))))

                ((:fnname fgl-rewrite-binder-try-rules)
                 (:add-concl
                  (implies (and successp
                                (fgl-good-fgl-binder-rules-p rules))
                           (equal (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-object-eval ans env new-logicman))
                                  (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-ev (cons (pseudo-fnsym-fix fn)
                                          (kwote-lst
                                           (cons (fgl-object-eval ans env new-logicman)
                                                 (fgl-objectlist-eval
                                                  (interp-st-top-scratch-fgl-objlist interp-st)
                                                  env logicman))))
                                    nil))))))

                ((:fnname fgl-rewrite-try-rules3)
                 (:add-concl
                  (implies (and successp
                                (fgl-good-fgl-rules-p rules1)
                                (fgl-good-fgl-rules-p rules2)
                                (fgl-good-fgl-rules-p rules3))
                           (equal (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-object-eval ans env new-logicman))
                                  (fgl-ev-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                 (kwote-lst
                                                  (fgl-objectlist-eval
                                                   (interp-st-top-scratch-fgl-objlist interp-st)
                                                   env logicman)))
                                           nil))))))

                ((:fnname fgl-rewrite-relieve-hyps)
                 (:add-concl
                  (implies (and (not failed-hyp)
                                (equal (interp-st->equiv-contexts interp-st) '(iff)))
                           (iff-forall-extensions
                            t (conjoin hyps) eval-alist))))
                ((:fnname fgl-rewrite-relieve-hyp)
                 (:add-concl
                  (implies (and successp
                                (equal (interp-st->equiv-contexts interp-st) '(iff)))
                           (iff-forall-extensions
                            t hyp eval-alist))))
                ((:fnname fgl-interp-binding-hyp)
                 (:add-concl
                  (implies okp
                           (iff-forall-extensions
                            t hyp eval-alist))))
                ((or (:fnname fgl-interp-if/or)
                     (:fnname fgl-interp-if)
                     (:fnname fgl-interp-if-nonbranching))
                 (:add-concl
                  (fgl-ev-context-equiv-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-eval ans env new-logicman)
                   (pseudo-term-fncall 'if (list test then else))
                   eval-alist)))
                ((or (:fnname fgl-interp-or)
                     (:fnname fgl-interp-or-nonbranching))
                 (:add-concl
                  (fgl-ev-context-equiv-forall-extensions
                   (interp-st->equiv-contexts interp-st)
                   (fgl-object-eval ans env new-logicman)
                   (pseudo-term-fncall 'if (list test test else))
                   eval-alist)))
                ((:fnname fgl-maybe-interp)
                 (:add-concl
                  (implies (gobj-bfr-eval test env logicman)
                           (and (fgl-ev-context-equiv-forall-extensions
                                 (interp-st->equiv-contexts interp-st)
                                 (fgl-object-eval ans env new-logicman)
                                 x
                                 eval-alist)
                                (not unreachable)))))
                ((:fnname fgl-interp-maybe-simplify-if-test)
                 (:add-concl
                  (implies (gobj-bfr-eval test env logicman)
                           (and (iff* (gobj-bfr-eval xbfr env new-logicman)
                                      (fgl-object-eval xobj env logicman))
                                (not unreachable)))))
                ((:fnname fgl-interp-simplify-if-test)
                 (:add-concl
                  (iff* (gobj-bfr-eval xbfr env new-logicman)
                        (fgl-object-eval xobj env logicman))))
                ((:fnname fgl-interp-simplify-if-test-ite)
                 (:add-concl
                  (implies (fgl-object-case xobj :g-ite)
                           (iff* (gobj-bfr-eval xbfr env new-logicman)
                                 (fgl-object-eval xobj env logicman)))))
                ((:fnname fgl-interp-simplify-if-test-fncall)
                 (:add-concl
                  (implies (fgl-object-case xobj :g-apply)
                           (iff* (gobj-bfr-eval xbfr env new-logicman)
                                 (fgl-object-eval xobj env logicman)))))
                ((or (:fnname fgl-interp-merge-branches)
                     (:fnname fgl-interp-merge-branches-rewrite)
                     (:fnname fgl-interp-merge-branch-subterms))
                 (:add-concl
                  (equal (fgl-ev-context-fix
                          (interp-st->equiv-contexts interp-st)
                          (fgl-object-eval ans env new-logicman))
                         (fgl-ev-context-fix
                          (interp-st->equiv-contexts interp-st)
                          (if* (gobj-bfr-eval testbfr env logicman)
                               (fgl-object-eval thenval env logicman)
                               (fgl-object-eval elseval env logicman)))))
                 (:add-keyword :hints ((and stable-under-simplificationp
                                            '(:in-theory (enable if*))))))
                ((:fnname fgl-interp-merge-branch-args)
                 (:add-concl
                  (implies (equal (len thenargs) (len elseargs))
                           (equal (fgl-ev-list-context-fix (interp-st->equiv-contexts interp-st)
                                                           (fgl-objectlist-eval args env new-logicman))
                                  (fgl-ev-list-context-fix
                                   (interp-st->equiv-contexts interp-st)
                                   (if* (gobj-bfr-eval testbfr env logicman)
                                        (fgl-objectlist-eval thenargs env logicman)
                                        (fgl-objectlist-eval elseargs env logicman))))))))))

   ;; (make-event
   ;;  `(with-output
   ;;            :off (event)
   ;;            :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
   ;;            (std::defret-mutual-generate
   ;;              ,*fgl-interp-correct-body*
   ;;              :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
   ;;                      ;; '(:expand (:lambdas))
   ;;                      (b* ((flag (find-flag-is-hyp clause))
   ;;                           ((unless flag) (value nil))
   ;;                           (state (f-put-global 'fgl-interp-term-subgoals
   ;;                                                (cons clause (@ fgl-interp-term-subgoals))
   ;;                                                state)))
   ;;                        (value '(:by nil))))
   ;;              ;; (prog2$ (cw "flag: ~x0~%" flag)
   ;;              ;;         '(:do-not '(generalize) :do-not-induct t))))
   ;;              ;; (and stable-under-simplificationp
   ;;              ;;              '(:in-theory (enable bfr-listp-when-not-member-witness)))

   ;;              :mutual-recursion fgl-interp)))
   (make-event
    (if (and ;; nil
             (boundp-global 'fgl-interp-term-subgoals state)
             (@ fgl-interp-term-subgoals))
        '(value-triple :skipping-subgoal-generation)
      '(progn
         (make-event
          (b* ((state (f-put-global 'fgl-interp-term-subgoals nil state)))
            (value '(value-triple :invisible))))
         (make-event
          `(:or
            (with-output
              :off (event prove)
              :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
              (std::defret-mutual-generate
                ,*fgl-interp-correct-body*
                :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
                        ;; '(:expand (:lambdas))
                        (b* ((flag (find-flag-is-hyp clause))
                             ((unless flag) (value nil))
                             (state (f-put-global 'fgl-interp-term-subgoals
                                                  (cons clause (@ fgl-interp-term-subgoals))
                                                  state)))
                          (cw "~x0~%" flag)
                          (value '(:by nil))))
                ;; (prog2$ (cw "flag: ~x0~%" flag)
                ;;         '(:do-not '(generalize) :do-not-induct t))))
                ;; (and stable-under-simplificationp
                ;;              '(:in-theory (enable bfr-listp-when-not-member-witness)))

                :mutual-recursion fgl-interp))
            (value-triple :goals-saved))))))


   ;; (local
   ;;  (defun prettyify-clause-list (clauses let*-abstractionp wrld)
   ;;    (declare (xargs :mode :program))
   ;;    (if (atom clauses)
   ;;        nil
   ;;      (cons (prettyify-clause (car clauses) let*-abstractionp wrld)
   ;;            (prettyify-clause-list (cdr clauses) let*-abstractionp wrld)))))

   (local (defun fgl-interp-clause-to-defthm (clause base-name let*-absp flag-index-alist hints wrld)
            (declare (xargs :mode :program))
            (b* ((flag (find-flag-is-hyp clause))
                 (goal (acl2::prettyify-clause clause let*-absp wrld))
                 ((unless flag)
                  (er hard? 'fgl-interp-clause-to-defthm
                      "Didn't find a flag for this clause: ~x0" goal)
                  (mv nil flag-index-alist))
                 (index (+ 1 (nfix (cdr (assoc flag flag-index-alist)))))
                 (flag-index-alist (cons (cons flag index) flag-index-alist))
                 (thmname (intern-in-package-of-symbol
                           (concatenate 'string
                                        (symbol-name base-name)
                                        "-" (symbol-name flag) "-LEMMA" (str::natstr index))
                           base-name)))
              (mv `(progn (defthm ,thmname
                            ,goal
                            :hints ,hints
                            :rule-classes nil)
                          (table fgl-interp-clauses-table ',clause ',thmname))
                  flag-index-alist))))

   (local
    (defun fgl-interp-clauses-to-defthms (clauses base-name let*-absp flag-index-alist hints wrld)
      (declare (xargs :mode :program))
      (b* (((when (atom clauses))
            nil)
           ((mv thm flag-index-alist)
            (fgl-interp-clause-to-defthm (car clauses) base-name let*-absp flag-index-alist hints wrld)))
        (cons thm
              (fgl-interp-clauses-to-defthms (cdr clauses) base-name let*-absp flag-index-alist hints wrld)))))

   (set-ignore-ok t)

   ;; (set-default-hints
   ;;  '((and stable-under-simplificationp
   ;;         '(:in-theory (enable if*)
   ;;           :do-not-induct t))))

   (with-output
     :off (event)
     :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
     (make-event
      `(acl2::run-events-stop-on-failure
        ,(fgl-interp-clauses-to-defthms
          (@ fgl-interp-term-subgoals)
          'fgl-interp-correct
          t nil
          '(("goal" :do-not-induct t :do-not '(generalize))
            (and stable-under-simplificationp
                 (cond ((member-eq (find-flag-is-hyp clause)
                                   '(fgl-interp-merge-branches
                                     fgl-interp-merge-branch-subterms
                                     fgl-interp-fncall-casesplit
                                     fgl-interp-fncall-casesplit-branches))
                        '(:in-theory (enable if*)))
                       ;; ((member-eq (find-flag-is-hyp clause)
                       ;;             '(fgl-maybe-interp-fncall-casesplit))
                       ;;  '(:in-theory (enable implies*)))
                       )))
          (w state)))))

   ;; (i-am-here)
   ))



(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (make-event
   `(std::defret-mutual-generate
      ,*fgl-interp-correct-body*
    :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
            ;; '(:expand (:lambdas))
            (b* ((flag (find-flag-is-hyp clause))
                 ((unless flag) (value nil))
                 (thm (cdr (assoc-equal clause (table-alist 'fgl-interp-clauses-table (w state)))))
                 ((unless thm)
                  (cw "Couldn't find theorem for clause: ~x0~%"
                      (acl2::prettyify-clause clause t (w state)))
                  (value '(:error t))))
              (value `(:clause-processor (my-by-hint-cp clause ',thm state)))))
    ;; (prog2$ (cw "flag: ~x0~%" flag)
    ;;         '(:do-not '(generalize) :do-not-induct t))))
    ;; (and stable-under-simplificationp
    ;;              '(:in-theory (enable bfr-listp-when-not-member-witness)))

    :mutual-recursion fgl-interp)))
