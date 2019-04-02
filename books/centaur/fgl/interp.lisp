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
(include-book "rewrite-tables")
(include-book "system/f-put-global" :dir :system)
(include-book "std/util/defret-mutual-generate" :dir :system)
(include-book "glcp-unify-thms")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/meta/resolve-flag-cp" :dir :system))

(local (std::add-default-post-define-hook :fix))

(def-updater-independence-thm bfr-listp$-of-interp-st->logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new)
                                      (interp-st->logicman old))
                (lbfr-listp x (interp-st->logicman old)))
           (lbfr-listp x (interp-st->logicman new))))

(def-updater-independence-thm logicman-pathcond-p-of-interp-st->logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new)
                                      (interp-st->logicman old))
                (logicman-pathcond-p x (interp-st->logicman old)))
           (logicman-pathcond-p x (interp-st->logicman new))))

;; (def-updater-independence-thm logicman-extension-p-transitive-interp-st
;;   (implies (and (logicman-extension-p (interp-st->logicman new)
;;                                       (interp-st->logicman old))
;;                 (equal (interp-st->logicman )
;;            (logicman-extension-p (interp-st->logicman new) prev)))



(define interp-st-bfrs-ok (interp-st)
  (b* ((constraint-db (interp-st->constraint-db interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (bvar-db (interp-st->bvar-db interp-st))
                (stack (interp-st->stack interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (ok)
               (b* ((bfrstate (logicman->bfrstate)))
                 (and (bfr-listp (major-stack-bfrlist (stack-extract stack)))
                      (bfr-listp (constraint-db-bfrlist constraint-db))
                      (ec-call (logicman-pathcond-p-fn pathcond logicman))
                      (ec-call (logicman-pathcond-p-fn constraint-pathcond logicman))
                      (not (consp (bvar-db-bfrlist bvar-db)))
                      (equal (next-bvar bvar-db) (bfr-nvars logicman))))
               ok))
  ///
  (defthm interp-st-bfrs-ok-implies
    (implies (interp-st-bfrs-ok interp-st)
             (let* ((logicman (interp-st->logicman interp-st))
                    (bfrstate (logicman->bfrstate)))
               (and (bfr-listp (major-stack-bfrlist (interp-st->stack interp-st)))
                    (bfr-listp (constraint-db-bfrlist (interp-st->constraint-db interp-st)))
                    (logicman-pathcond-p (interp-st->pathcond interp-st))
                    (logicman-pathcond-p (interp-st->constraint interp-st))
                    (not (bvar-db-bfrlist (interp-st->bvar-db interp-st)))
                    (interp-st-nvars-ok interp-st)
                    (equal (next-bvar$a (interp-st->bvar-db interp-st))
                           (bfr-nvars (interp-st->logicman interp-st))))))
    :hints(("Goal" :in-theory (enable interp-st-nvars-ok))))

  (acl2::def-updater-independence-thm interp-st-bfrs-ok-updater-independence
    (implies (and (equal (interp-st-get :logicman new)
                         (interp-st-get :logicman old))
                  (equal (interp-st-get :stack new)
                         (interp-st-get :stack old))
                  (equal (interp-st-get :constraint-db new)
                         (interp-st-get :constraint-db old))
                  (equal (interp-st-get :pathcond new)
                         (interp-st-get :pathcond old))
                  (equal (interp-st-get :constraint new)
                         (interp-st-get :constraint old))
                  (equal (interp-st-get :bvar-db new)
                         (interp-st-get :bvar-db old)))
             (equal (interp-st-bfrs-ok new)
                    (interp-st-bfrs-ok old))))


  (defthm interp-st-bfrs-ok-of-logicman-extension
    (implies (and (interp-st-bfrs-ok interp-st)
                  (logicman-extension-p new-logicman (interp-st->logicman interp-st))
                  (equal (bfr-nvars new-logicman) (bfr-nvars (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->logicman new-logicman interp-st))))

  (defthm interp-st-bfrs-ok-of-update-stack
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (major-stack-bfrlist new-stack) (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->stack new-stack interp-st))))

  (defthm interp-st-bfrs-ok-of-update-constraint-db
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (constraint-db-bfrlist new-constraint-db) (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->constraint-db new-constraint-db interp-st))))

  (defthm interp-st-bfrs-ok-of-update-pathcond
    (implies (And (interp-st-bfrs-ok interp-st)
                  (logicman-pathcond-p-fn new-pathcond (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok (update-interp-st->pathcond new-pathcond interp-st))))

  (defthm interp-st-bfrs-ok-of-update-constraint
    (implies (And (interp-st-bfrs-ok interp-st)
                  (logicman-pathcond-p-fn new-constraint (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok (update-interp-st->constraint new-constraint interp-st))))

  (defthm interp-st-bfrs-ok-of-update-bvar-db
    (implies (And (interp-st-bfrs-ok interp-st)
                  (not (bvar-db-bfrlist new-bvar-db))
                  (equal (next-bvar new-bvar-db) (bfr-nvars (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->bvar-db new-bvar-db interp-st))))

  (defthm interp-st-bfrs-ok-of-interp-st-add-term-bvar
    (implies (and (interp-st-bfrs-ok interp-st)
                  (not (consp (gl-object-bfrlist x))))
             (interp-st-bfrs-ok (mv-nth 1 (interp-st-add-term-bvar x interp-st state))))
    ;; :hints (("goal" :use ((:instance logicman-extension-p-of-interp-st-add-term-bvar))
    ;;          :in-theory (disable logicman-extension-p-of-interp-st-add-term-bvar)))
    )

  (defthm interp-st-bfrs-ok-of-interp-st-add-term-bvar-unique
    (implies (and (interp-st-bfrs-ok interp-st)
                  (not (consp (gl-object-bfrlist x))))
             (interp-st-bfrs-ok (mv-nth 1 (interp-st-add-term-bvar-unique x interp-st state))))
    ;; :hints (("goal" :use ((:instance logicman-extension-p-of-interp-st-add-term-bvar-unique))
    ;;          :in-theory (disable logicman-extension-p-of-interp-st-add-term-bvar-unique)))
    )

)




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


(define gl-interp-store-debug-info (msg obj interp-st)
  :returns new-interp-st
  (b* (((when (interp-st->errmsg interp-st))
        interp-st)
       (interp-st (update-interp-st->errmsg msg interp-st))
       (stack-obj (stobj-let ((stack (interp-st->stack interp-st)))
                             (obj)
                             (stack-extract stack)
                             obj))
       (interp-st (update-interp-st->debug-info (list obj stack-obj) interp-st)))
    interp-st)
  ///

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-of-<fn>
    (implies msg
             (interp-st->errmsg new-interp-st)))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (and (not (equal msg x))
                  (not (equal (interp-st->errmsg interp-st) x)))
             (not (equal (interp-st->errmsg new-interp-st) x)))))

(local (in-theory (disable w)))

(defmacro gl-interp-error (&key msg debug-obj (nvals '1))
  `(b* ((msg ,msg)
        (debug-obj ,debug-obj)
        (interp-st (gl-interp-store-debug-info msg debug-obj interp-st)))
     ,(if (eql nvals 0)
          'interp-st
        `(mv ,@(acl2::repeat nvals nil) interp-st))))
  



(define interp-st-set-error (msg interp-st)
  :returns new-interp-st
  (if (interp-st->errmsg interp-st)
      interp-st
    (update-interp-st->errmsg msg interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-of-<fn>
    (implies msg
             (interp-st->errmsg new-interp-st)))

  (defret errmsg-differs-of-<fn>
    (implies (and msg2 (not (equal msg2 msg)))
             (equal (equal (interp-st->errmsg new-interp-st) msg2)
                    (equal (interp-st->errmsg interp-st) msg2)))))

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

;; (define glcp-interp-error (msg &key (interp-st 'interp-st)
;;                                (state 'state))
;;   :returns (mv errmsg
;;                result
;;                new-interp-st
;;                new-state)
;;   (mv msg nil interp-st state))

;; (defmacro glcp-value (obj)
;;   `(mv nil ,obj interp-st state))


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
   (dont-rewrite-under-if-test booleanp)
   (dont-primitive-exec booleanp)))

(define gl-function-mode-fix! (x)
  :guard-hints(("Goal" :in-theory (enable gl-function-mode-fix)))
  :enabled t
  (mbe :logic (gl-function-mode-fix x)
       :exec (loghead 5 (ifix x))))

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


(acl2::def-meta-extract fgl-ev fgl-ev-list)

(define fncall-try-concrete-eval ((fn pseudo-fn-p)
                                  (args gl-objectlist-p)
                                  (dont-concrete-exec)
                                  state)
  :returns (mv ok (ans gl-object-p))
  (b* (((gl-function-mode mode))
       ((when (or dont-concrete-exec
                  (not (g-concretelist-p args))))
        (mv nil nil))
       ((mv err ans)
        (magic-ev-fncall (pseudo-fn-fix fn) (g-concretelist-vals args) state t nil)))
    (mv (not err) (g-concrete ans)))
  ///
  (defret gl-object-bfrlist-of-<fn>
    (equal (gl-object-bfrlist ans) nil))

  (local (defthm fgl-objectlist-eval-when-concretelist-p
           (implies (g-concretelist-p x)
                    (equal (fgl-objectlist-eval x env)
                           (g-concretelist-vals x)))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval fgl-object-eval g-concretelist-p
                                             g-concretelist-vals)))))

  (defret eval-of-<fn>
    (implies (and ok
                  (fgl-ev-meta-extract-global-facts))
             (equal (fgl-object-eval ans env)
                    (fgl-ev (cons (pseudo-fn-fix fn) (kwote-lst (fgl-objectlist-eval args env)))
                            nil)))))


(define interp-st-restore-reclimit ((reclimit natp)
                                    interp-st)
  :guard (acl2::nat-equiv reclimit (interp-st->reclimit interp-st))
  :inline t
  :enabled t
  (mbe :logic (update-interp-st->reclimit (lnfix reclimit) interp-st)
       :exec interp-st))

(def-b*-binder gl-interp-recursive-call
  :body
  `(b* ((interp-recursive-call-reclimit (lnfix (interp-st->reclimit interp-st)))
        (,(if (consp (cdr args)) `(mv . ,args) (car args)) . ,forms)
        (interp-st (interp-st-restore-reclimit interp-recursive-call-reclimit interp-st)))
     ,rest-expr))


(define gl-interp-time$-arg ((arg gl-object-p) (x pseudo-termp))
  (b* ((arg (gl-object-case arg :g-concrete (and (true-listp arg.val) arg.val) :otherwise nil))
       (term-descrip (pseudo-term-case x :fncall x.fn :otherwise (pseudo-term-fix x))))
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




(define gl-interp-match-synp ((x pseudo-termp))
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
  (defret gl-interp-match-synp-implies-eval
    (implies synp-type
             (equal (fgl-ev x a) t))))



(define gl-interp-syntax-bind ((synp-arg pseudo-termp)
                               (x pseudo-termp)
                               interp-st
                               state)
  :returns (mv (ans gl-object-p)
               new-interp-st)
  :prepwork ((local (defthm symbol-alistp-when-gl-object-alist-p
                      (implies (gl-object-alist-p x)
                               (symbol-alistp x))
                      :hints(("Goal" :in-theory (enable gl-object-alist-p))))))
  (b* (((mv synp-ok synp-term untrans) (match-syntax-bind-synp synp-arg))
       ((unless (and synp-ok (pseudo-term-case x :var)))
        ;; We could go ahead and simulate x anyway but this does seem like an error.
        (gl-interp-error :msg (gl-msg "Bad syntax-bind form: args ~x0, ~x1."
                                      (pseudo-term-fix synp-arg)
                                      (pseudo-term-fix x))))
       (varname (acl2::pseudo-term-var->name x))
       (bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st)))
       ;; Consider allowing already-bound variables to be bound in the new
       ;; bindings, and just omitting them from the final bindings.  Might be
       ;; convenient in case we want to bind a variable in different places for
       ;; different cases.  
       ((when (assoc-eq varname bindings))
        (gl-interp-error
         :msg (gl-msg "Syntax-bind error: ~x0 was supposed to be bound in a ~
                       syntax-bind form but was already bound" varname)))
       ((mv ok val) (acl2::magic-ev synp-term bindings state t t))
       ((unless ok)
        (gl-interp-error
         :msg (gl-msg "Syntax-bind error: ~x0 failed to evaluate -- translated: ~x1" untrans synp-term)))
       ((unless (gl-bfr-object-p val (interp-st-bfr-state)))
        (gl-interp-error
         :msg (gl-msg "Syntax-bind error: ~x0 evaluted to an illformed symbolic object, saved in ~x1."
                      untrans '(@ gl-interp-error-debug-obj))
         :debug-obj val))
       ;; BOZO We might actually want to bind this to a non-concrete value
       (interp-st (interp-st-add-binding varname val interp-st)))
    (mv val interp-st))
  ///
  (local (defthm bfrlist-of-interp-st-add-binding
           (implies (and (not (member v (major-stack-bfrlist stack)))
                         (not (member v (gl-object-bfrlist val))))
                    (not (member v (major-stack-bfrlist (stack$a-add-binding var val stack)))))
           :hints (("goal" :expand ((major-stack-bfrlist stack))
                    :in-theory (enable stack$a-add-binding major-frame-bfrlist
                                       major-stack-bfrlist)))))

  (local (in-theory (disable stack$a-add-binding)))
  (local (in-theory (enable bfr-listp-when-not-member-witness)))

  (local (Defthm gl-bfr-object-p-is-gl-object-p-and-bfr-listp
           (equal (gl-bfr-object-p x)
                  (and (gl-object-p x)
                       (bfr-listp (gl-object-bfrlist x))))))
  
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (and (interp-st-bfrs-ok new-interp-st)
                  (lbfr-listp (gl-object-bfrlist ans)
                              (interp-st->logicman interp-st)))))

  (defret interp-st-get-of-<fn>
    (implies (And (not (equal (interp-st-field-fix key) :stack))
                  (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info)))
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
             (not (equal (interp-st->errmsg new-interp-st) :unreachable)))))


(define gl-interp-or-test-equiv-contexts ((contexts equiv-contextsp))
  :returns (new-contexts equiv-contextsp)
  (and (equal (equiv-contexts-fix contexts) '(iff)) '(iff)))

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
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st))
              (constraint-pathcond (interp-st->constraint interp-st)))
             (contra pathcond constraint-pathcond)
             ;; this is a bit weak... would be better to check against
             ;; both constraint and pathcond at once somehow
             (b* (((mv constraint-implies constraint-pathcond)
                   (logicman-pathcond-implies test constraint-pathcond))
                  ((when (eql constraint-implies 0))
                   (mv t pathcond constraint-pathcond))
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

(define gl-apply-match-not ((x gl-object-p))
  :guard (gl-object-case x :g-apply)
  :returns (mv ok
               (negated-arg gl-object-p))
  (b* (((unless (mbt (gl-object-case x :g-apply))) (mv nil nil))
       ((g-apply x))
       (fn x.fn)
       (args x.args)
       ((when (eq fn 'not))
        (cond ((eql (len args) 1)
               (mv t (gl-object-fix (car args))))
              (t (mv nil nil))))
       ((when (eq fn 'equal))
        (b* (((unless (eql (len args) 2))
              (mv nil nil))
             ((list arg1 arg2) args)
             ((when (gl-object-case arg1
                      :g-concrete (eq arg1.val nil)
                      :otherwise nil))
              (mv t (gl-object-fix arg2)))
             ((when (gl-object-case arg2
                      :g-concrete (eq arg2.val nil)
                      :otherwise nil))
              (mv t (gl-object-fix arg1))))
          (mv nil nil))))
    (mv nil nil))
  ///
  

  (defret gl-apply-match-not-correct
    (implies ok
             (iff (fgl-object-eval negated-arg env logicman)
                  (not (fgl-object-eval x env logicman))))
    :hints(("Goal" :expand ((fgl-objectlist-eval (g-apply->args x) env)
                            (fgl-objectlist-eval (cdr (g-apply->args x)) env)
                            (fgl-objectlist-eval (cddr (g-apply->args x)) env))
            :in-theory (enable fgl-apply))))

  (defret gl-object-count-of-g-apply-match-not
    (implies ok
             (< (gl-object-count negated-arg) (gl-object-count x)))
    :hints(("Goal" :expand ((gl-object-count x)
                            (gl-objectlist-count (g-apply->args x))
                            (gl-objectlist-count (cdr (g-apply->args x)))
                            (gl-objectlist-count (cddr (g-apply->args x))))))
    :rule-classes :linear)

  (defret bfrlist-of-gl-apply-match-not
    (implies (not (member v (gl-object-bfrlist x)))
             (not (member v (gl-object-bfrlist negated-arg))))))
  

(local
 (defthm pseudo-var-list-p-of-append
   (implies (and (pseudo-var-list-p x)
                 (pseudo-var-list-p y))
            (pseudo-var-list-p (append x y)))))

(local (in-theory (disable pseudo-termp acl2::magic-ev)))

(define gl-rewrite-relieve-hyp-synp ((synp-type symbolp)
                                     (form pseudo-termp)
                                     (vars)
                                     (untrans-form)
                                     interp-st
                                     state)
  :returns (mv successp
               new-interp-st)
  :prepwork ((local (defthm alist-keys-of-gl-object-alist
                      (implies (gl-object-alist-p x)
                               (and (pseudo-var-list-p (alist-keys x))
                                    (symbol-listp (alist-keys x))))
                      :hints(("Goal" :in-theory (enable alist-keys)))))
             (local (defthm symbol-alistp-when-gl-object-alist-p
                      (implies (gl-object-alist-p x)
                               (symbol-alistp x))))
             
             (local (Defthm gl-bfr-object-alist-p-is-gl-object-alist-p-and-bfr-listp
                      (equal (gl-bfr-object-alist-p x)
                             (and (gl-object-alist-p x)
                                  (bfr-listp (gl-object-alist-bfrlist x))))
                      :hints(("Goal" :in-theory (enable gl-bfr-object-alist-p-implies-gl-object-alist-p)))))

             (local (defthm symbol-listp-when-pseudo-var-list-p
                      (implies (pseudo-var-list-p x)
                               (symbol-listp x)))))
  :hooks ((:fix :omit (synp-type)))
  (b* ((bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st)))
       (form (pseudo-term-fix form))
       ((mv ok val) (acl2::magic-ev form bindings state t t))
       ((unless ok)
        (gl-interp-error
         :msg (gl-msg "Synp error: ~x0 failed to evaluate -- translated: ~x1" untrans-form form)))
       ((when (eq synp-type 'syntaxp))
        (mv val interp-st))
       ;; bind-free...
       ((unless val)
        ;; No error -- bind-free evaluated to NIL which means just don't do the rewrite.
        (mv nil interp-st))
       ((unless (gl-bfr-object-alist-p val (interp-st-bfr-state)))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to a non-GL object alist: ~x1" untrans-form val)))
       (newly-bound-vars (alist-keys val))
       ((when (and (symbol-listp vars)
                   (not (subsetp-eq vars newly-bound-vars))))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to an alist not ~
                     containing the required vars ~x1: ~x2" untrans-form val vars)))
       ;; Consider allowing already-bound variables to be bound in the new
       ;; bindings, and just omitting them from the final bindings.  Might be
       ;; convenient in case we want to bind a variable in different places for
       ;; different cases.  
       ((when (intersectp-eq (alist-keys bindings) newly-bound-vars))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to an alist containing already-bound vars: ~x1" untrans-form val)))
       ((unless (no-duplicatesp-eq newly-bound-vars))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to an alist containing duplicate vars: ~x1" untrans-form val)))
       
       (interp-st (interp-st-set-bindings (append val (interp-st-bindings interp-st)) interp-st)))
    (mv t interp-st))
  ///
  (local
   (defthm major-stack-bfrlist-of-stack$a-set-bindings
     (implies (and (not (member v (major-stack-bfrlist stack)))
                   (not (member v (gl-object-alist-bfrlist bindings))))
              (not (member v (major-stack-bfrlist (stack$a-set-bindings bindings stack)))))
     :hints(("Goal" :in-theory (enable stack$a-set-bindings
                                       major-stack-bfrlist
                                       major-frame-bfrlist
                                       minor-frame-bfrlist
                                       minor-stack-bfrlist)
             :do-not-induct t))))

  (local
   (defthm gl-object-alist-bfrlist-of-stack$a-bindings-bindings
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (gl-object-alist-bfrlist (stack$a-bindings stack)))))
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
    (implies (and (not (equal (interp-st-field-fix key) :stack))
                  (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret multivalues-of-<fn>
    (equal (list . <values>)
           <call>))

  (defret <fn>-preserves-errmsg
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable)))))



;; Used in merge-branches to recognize a branch on which we can unify some
;; function.  BOZO We might want to try more than one function for some objects
;; -- e.g. for :g-integer we could do both int and intcons, for concrete values
;; that are conses we could do both concrete and bool, etc.  Ideally we'd try
;; all the functions that the argument could unify with.
(define gl-fncall-object->fn ((x gl-object-p))
  :returns (fn pseudo-fnsym-p) ;; nil if didn't match
  (gl-object-case x
    :g-boolean 'bool
    :g-integer 'int
    :g-concrete 'concrete
    :g-apply x.fn
    :g-cons 'cons
    :otherwise nil))


(defthm fgl-ev-list-of-kwote-lst
  (equal (fgl-ev-list (kwote-lst x) a)
         (true-list-fix x)))

(defthm not-quote-when-pseudo-fnsym-p
  (implies (pseudo-fnsym-p x)
           (not (equal x 'quote))))

(define gl-object-recognize-merge-fncall ((x gl-object-p))
  ;; Note: This is used when we want to merge two calls of the same function,
  ;; e.g.  (if test (foo x y) (foo w z)).  We don't want to match a g-boolean
  ;; to (bool x), for example, because that would lead to an infinite loop where we
  ;; match (if test (g-boolean b) (g-boolean c)) as
  ;; (if test (bool (g-boolean b)) (bool (g-boolean c)))
  ;; then merge the args, i.e. (list (g-boolean b)) (list (g-boolean c))
  ;; in which when we merge the first arg we get back to
  ;; (if test (g-boolean b) (g-boolean c)) and get stuck in an infinite loop.
  :returns (mv (fn pseudo-fnsym-p :rule-classes (:rewrite (:type-prescription :typed-term fn)))
               (args gl-objectlist-p))
  (gl-object-case x
    ;; :g-boolean (mv 'bool (list (gl-object-fix x)))
    ;; :g-integer (mv 'int (list (gl-object-fix x)))
    ;; :g-concrete (mv 'concrete (list (gl-object-fix x)))
    :g-apply (mv x.fn x.args)
    :g-cons (mv 'cons (list x.car x.cdr))
    :otherwise (mv nil nil))
  ///

  ;; (defret eval-when-gl-object-recognize-merge-fncall
  ;;   (implies fn
  ;;            (equal (fgl-ev (cons fn
  ;;                                        (kwote-lst (fgl-objectlist-eval args env)))
  ;;                                  a)
  ;;                   (fgl-object-eval x env)))
  ;;   :hints(("Goal" :in-theory (enable fgl-apply fgl-objectlist-eval
  ;;                                     fgl-ev-of-fncall-args))))

  (defret eval-when-gl-object-recognize-merge-fncall2
    (implies (and fn
                  (equal fn1 fn))
             (equal (fgl-ev (cons fn1
                                         (kwote-lst (fgl-objectlist-eval args env)))
                                   a)
                    (fgl-object-eval x env)))
    :hints(("Goal" :in-theory (enable fgl-apply fgl-objectlist-eval
                                      fgl-ev-of-fncall-args))))

  (defret gl-objectlist-count-of-recognize-merge-fncall
    (implies fn
             (<= (gl-objectlist-count args) (gl-object-count x)))
    :hints(("Goal" :in-theory (enable gl-objectlist-count))
           (and stable-under-simplificationp
                '(:expand ((gl-object-count x)))))
    :rule-classes :linear)

  ;; (defret gl-bfr-objectlist-p-of-<fn>
  ;;   (implies (gl-bfr-object-p x)
  ;;            (gl-bfr-objectlist-p args)))

  (defret bfr-listp-gl-objectlist-bfrlist-of-<fn>
    (implies (bfr-listp (gl-object-bfrlist x))
             (bfr-listp (gl-objectlist-bfrlist args)))
    :hints (("goal" :Expand ((gl-object-bfrlist x))))))

;; (define gl-object-recognize-fncall ((x gl-object-p))
;;   :prepwork ((local (in-theory (enable gl-fncall-object->fn))))
;;   :returns (mv (fn (equal fn (gl-fncall-object->fn x)))
;;                (args gl-objectlist-p))
;;   (gl-object-case x
;;     :g-boolean (mv 'bool (list (gl-object-fix x)))
;;     :g-integer (mv 'int (list (gl-object-fix x)))
;;     :g-concrete (mv 'concrete (list (gl-object-fix x)))
;;     :g-apply (mv x.fn x.args)
;;     :g-cons (mv 'cons (list x.car x.cdr))
;;     :otherwise (mv nil nil))
;;   ///
;;   (defret eval-when-gl-object-recognize-fncall
;;     (implies (gl-fncall-object->fn x)
;;              (equal (fgl-object-eval x env)
;;                     (fgl-apply (gl-fncall-object->fn x)
;;                                 (fgl-objectlist-eval args env))))
;;     :hints(("Goal" :in-theory (enable fgl-apply fgl-objectlist-eval)))))

;; (defthm-fgl-object-eval-flag
;;   (defthm fgl-object-eval-of-gl-bfr-object-fix
;;     (equal (fgl-object-eval (gl-bfr-object-fix x (logicman->bfrstate logicman))
;;                                 env logicman)
;;            (fgl-object-eval x env logicman))
;;     :hints ('(:expand ((fgl-object-eval x env logicman)
;;                        (gl-bfr-object-fix x (logicman->bfrstate logicman)))))
;;     :flag fgl-object-eval)
;;   (defthm fgl-objectlist-eval-of-gl-bfr-object-fix
;;     (equal (fgl-objectlist-eval (gl-bfr-objectlist-fix x (logicman->bfrstate logicman))
;;                                 env logicman)
;;            (fgl-objectlist-eval x env logicman))
;;     :hints ('(:expand ((fgl-objectlist-eval x env logicman)
;;                        (gl-bfr-objectlist-fix x (logicman->bfrstate logicman)))))
;;     :flag fgl-objectlist-eval))

;; BOZO move



(define gl-object-basic-merge ((test lbfr-p)
                               (then gl-object-p)
                               (else gl-object-p)
                               &optional
                               (logicman 'logicman))
  :returns (mv (obj gl-object-p)
               new-logicman)
  :guard-hints (("goal" :in-theory (enable bfr-ite-bss-fn)))
  :guard (and (gl-bfr-object-p then (logicman->bfrstate))
              (gl-bfr-object-p else (logicman->bfrstate)))
  (b* ((bfrstate (logicman->bfrstate)))
    (gl-object-case then
      :g-boolean (gl-object-case else
                   :g-boolean (b* (((mv bfr logicman) (bfr-ite (bfr-fix test)
                                                               (bfr-fix then.bool)
                                                               (bfr-fix else.bool))))
                                (mv (g-boolean bfr) logicman))
                   :otherwise (mv (gl-bfr-object-fix (g-ite (g-boolean test) then else)) logicman))
      :g-integer (gl-object-case else
                   :g-integer (b* (((mv bits logicman) (bfr-ite-bss (bfr-fix test)
                                                                    (bfr-list-fix then.bits)
                                                                    (bfr-list-fix else.bits)
                                                                    logicman)))
                                (mv (g-integer bits) logicman))
                   :otherwise (mv (gl-bfr-object-fix (g-ite (g-boolean test) then else)) logicman))
      :otherwise (mv (gl-bfr-object-fix (g-ite (g-boolean test) then else)) logicman)))
  ///
  ;; (defret gl-bfr-object-p-of-<fn>
  ;;   (gl-bfr-object-p obj (logicman->bfrstate new-logicman)))

  (defret eval-of-gl-object-basic-merge
    (equal (fgl-object-eval obj env new-logicman)
           (if (gobj-bfr-eval test env)
               (fgl-object-eval then env logicman)
             (fgl-object-eval else env logicman)))
    :hints(("Goal" 
            :in-theory (enable gobj-bfr-eval gobj-bfr-list-eval-is-bfr-list-eval))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman))
  
  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (bfr-nvars logicman)))
  
  (local (defthm gl-bfr-objectlist-of-gl-bfr-object-fix
           (bfr-listp (gl-object-bfrlist (gl-bfr-object-fix x bfrstate)) bfrstate)
           :hints (("goal" :use ((:instance gl-bfr-object-p-when-gl-object-p
                                  (x (gl-bfr-object-fix x bfrstate))))))))

  (defret bfr-listp-of-gl-object-basic-merge
    ;; (implies (and (lbfr-p test)
    ;;               (lbfr-listp (gl-object-bfrlist thenval))
    ;;               (lbfr-listp (gl-object-bfrlist elseval)))
             (bfr-listp (gl-object-bfrlist obj) (logicman->bfrstate new-logicman))))


(define gl-int-primitive ((args gl-objectlist-p) interp-st state)
  (declare (ignorable state))
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-integer (mv t (gl-object-fix x) interp-st)
          :otherwise (mv nil nil interp-st)))
    (mv nil nil interp-st))
  ///
  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons 'int
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

(define gl-endint-primitive ((args gl-objectlist-p) interp-st state)
  (declare (ignorable state))
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-boolean (mv t (g-integer (list x.bool)) interp-st)
          :otherwise (mv nil nil interp-st)))
    (mv nil nil interp-st))
  ///
  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons 'endint
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-eval
                                      gobj-bfr-list-eval
                                      bools->int)))))

(define gl-intcons-primitive ((args gl-objectlist-p) interp-st state)
  (declare (ignorable state))
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st
              )
  (if (eql (len args) 2)
      (b* (((list car cdr) args))
        (gl-object-case car
          :g-boolean (gl-object-case cdr
                       :g-integer (mv t (g-integer (cons car.bool
                                                         (if (atom cdr.bits)
                                                             '(nil)
                                                           cdr.bits)))
                                      interp-st)
                       :otherwise (mv nil nil interp-st))
          :otherwise (mv nil nil interp-st)))
    (mv nil nil interp-st))
  ///
  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons 'intcons
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-eval bools->int gobj-bfr-list-eval )))))

(define gl-intcar-primitive ((args gl-objectlist-p) interp-st state)
  (declare (ignorable state))
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st
              )
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-integer (mv t (g-boolean (car x.bits)) interp-st)
          :otherwise (mv nil nil interp-st)))
    (mv nil nil interp-st))
  ///
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (defthm len-equal-1
           (equal (equal (len x) 1)
                  (and (consp x)
                       (atom (cdr x))))))
  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons 'intcar
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-eval
                                      gobj-bfr-list-eval
                                      intcar bools->int len)
            :expand ((:free (logicman)
                      (gobj-bfr-list-eval (g-integer->bits (car args))
                                          env)))))))

(define gl-intcdr-primitive ((args gl-objectlist-p) interp-st state)
  (declare (ignorable state))
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st
              )
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-integer (mv t (g-integer (scdr x.bits)) interp-st)
          :otherwise (mv nil nil interp-st)))
    (mv nil nil interp-st))
  ///
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (defthm len-equal-1
           (equal (equal (len x) 1)
                  (and (consp x)
                       (atom (cdr x))))))
  (local (defthm scdr-of-gobj-bfr-list-eval
           (equal (scdr (gobj-bfr-list-eval x env))
                  (gobj-bfr-list-eval (scdr x) env))
           :hints(("Goal" :in-theory (enable scdr gobj-bfr-list-eval)))))
  (local (defthm cdr-of-gobj-bfr-list-eval
           (equal (cdr (gobj-bfr-list-eval x env))
                  (gobj-bfr-list-eval (cdr x) env))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
  (local (defthm car-of-gobj-bfr-list-eval
           (equal (car (gobj-bfr-list-eval x env))
                  (gobj-bfr-eval (car x) env))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
  (local (defthm s-endp-of-gobj-bfr-list-eval
           (equal (s-endp (gobj-bfr-list-eval x env))
                  (s-endp x))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval s-endp)))))
  (local (defthm gobj-bfr-list-eval-scdr-when-s-endp
           (implies (s-endp x)
                    (equal (gobj-bfr-list-eval (scdr x) env)
                           (gobj-bfr-list-eval x env)))
           :hints(("Goal" :in-theory (enable scdr s-endp)))))
  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons 'intcdr
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-eval
                                      gobj-bfr-list-eval
                                      intcdr bools->int))
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit))))))

(define gl-bool-primitive ((args gl-objectlist-p) interp-st state)
  (declare (ignorable state))
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st
              )
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-boolean (mv t (gl-object-fix x) interp-st)
          :otherwise (mv nil nil interp-st)))
    (mv nil nil interp-st))
  ///
  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons 'bool
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-eval gobj-bfr-list-eval )))))

(define gl-primitive-fncall ((fn pseudo-fnsym-p)
                             (args gl-objectlist-p)
                             (dont)
                             interp-st
                             state)
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st)
  (if dont
      (mv nil nil interp-st)
    (case (pseudo-fnsym-fix fn)
      (int (gl-int-primitive args interp-st state))
      ((intcons intcons*) (gl-intcons-primitive args interp-st state))
      (endint (gl-endint-primitive args interp-st state))
      (intcar (gl-intcar-primitive args interp-st state))
      (intcdr (gl-intcdr-primitive args interp-st state))
      (bool (gl-bool-primitive args interp-st state))
      (otherwise (mv nil nil interp-st))))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  ;; (lbfr-listp (gl-objectlist-bfrlist args)
                  ;;             (interp-st->logicman interp-st))
                  )
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable gl-int-primitive
                                      gl-intcons-primitive
                                      gl-endint-primitive
                                      gl-intcar-primitive
                                      gl-intcdr-primitive
                                      gl-bool-primitive))))

  (defret bfr-listp-of-<fn>
    (implies (and ;;(interp-st-bfrs-ok interp-st)
              (lbfr-listp (gl-objectlist-bfrlist args)
                          (interp-st->logicman interp-st))
                  )
             (lbfr-listp (gl-object-bfrlist ans)
                         (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable gl-int-primitive
                                      gl-intcons-primitive
                                      gl-endint-primitive
                                      gl-intcar-primitive
                                      gl-intcdr-primitive
                                      gl-bool-primitive
                                      gl-objectlist-bfrlist
                                      bfr-listp-when-not-member-witness))))

  (defret interp-st-get-of-gl-primitive-fncall
    (implies (not (equal (interp-st-field-fix key) :logicman))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))
    :hints(("Goal" :in-theory (enable gl-int-primitive
                                      gl-intcons-primitive
                                      gl-endint-primitive
                                      gl-intcar-primitive
                                      gl-intcdr-primitive
                                      gl-bool-primitive))))

  (defret logicman-extension-of-<fn>
    (implies (equal old (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old))
    :hints(("Goal" :in-theory (enable gl-int-primitive
                                      gl-intcons-primitive
                                      gl-endint-primitive
                                      gl-intcar-primitive
                                      gl-intcdr-primitive
                                      gl-bool-primitive))))

  (local (in-theory (disable intcar)))

  (defret eval-of-<fn>
    (implies successp
             (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                    (fgl-ev (cons (pseudo-fnsym-fix fn)
                                  (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                            nil)))))
                                      
      



;; (define glcp-unify-term/gobj-list-prefix ((pat pseudo-term-listp)
;;                                         (x gl-objectlist-p)
;;                                         (alist gl-object-alist-p))
;;   ;; Same as glcp-unify-term/gobj-list but doesn't complain about extra or missing elements of x.
;;   ;; Equivalent to (glcp-unify-term/gobj-list pat (take (len pat) x) alist).
;;   (b* (((when (atom pat)) (mv t (gl-object-alist-fix alist)))
;;        ((mv ok alist) (glcp-unify-term/gobj (car pat) (car x) alist))
;;        ((unless ok) (mv nil nil)))
;;     (glcp-unify-term/gobj-list-prefix (cdr pat) (cdr x) alist))
;;   ///
;;   (defthm glcp-unify-term/gobj-list-prefix-elim
;;     (equal (glcp-unify-term/gobj-list-prefix pat x alist)
;;            (glcp-unify-term/gobj-list pat (take (len pat) x) alist))
;;     :hints(("Goal" :induct (glcp-unify-term/gobj-list-prefix pat x alist)
;;             :expand ((:free (x) (glcp-unify-term/gobj-list pat x alist))
;;                      (take (len pat) x))))))





(define gl-interp-finish-simplify-if-test-ite ((test-bfr interp-st-bfr-p)
                                               (then-bfr interp-st-bfr-p)
                                               (else-bfr interp-st-bfr-p)
                                               (then-unreachable)
                                               (else-unreachable)
                                               interp-st)
  :returns (mv (ite (interp-st-bfr-p ite new-interp-st))
               new-interp-st)
  (b* (((when then-unreachable)
        (if else-unreachable
            (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
              (mv nil interp-st))
          (mv (interp-st-bfr-fix else-bfr) interp-st)))
       ((when else-unreachable)
        (mv (interp-st-bfr-fix then-bfr) interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ite logicman)
               (bfr-ite test-bfr then-bfr else-bfr)
               (mv ite interp-st)))
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
                    (interp-st->errmsg interp-st)))))                         

















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

(local (defthm gl-object-count-of-car-weak
         (<= (gl-object-count (car x)) (gl-objectlist-count x))
         :hints (("goal" :cases ((consp x))))
         :rule-classes :linear))

(local (defthm gl-objectlist-count-of-cdr-weak
         (<= (gl-objectlist-count (cdr x)) (gl-objectlist-count x))
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
         (implies (syntaxp (quotep n))
                  (equal (stack$a-nth-scratch n stack)
                         (if (zp n)
                             (stack$a-top-scratch stack)
                           (stack$a-nth-scratch (1- n)
                                                (stack$a-pop-scratch stack)))))
         :hints(("Goal" :in-theory (enable stack$a-top-scratch stack$a-pop-scratch stack$a-nth-scratch)))))


(local (in-theory (disable (tau-system) len default-car default-cdr
                           pseudo-termp
                           pseudo-term-listp
                           fgetprop
                           not
                           acl2::nfix-when-not-natp
                           equal-of-booleans-rewrite
                           mv-nth-cons-meta
                           acl2::take-redefinition
                           acl2::take-of-too-many
                           acl2::take-of-len-free
                           acl2::take-when-atom
                           acl2::lower-bound-of-len-when-sublistp
                           append)))


(define gl-interp-check-reclimit (interp-st)
  :inline t
  (or (zp (interp-st->reclimit interp-st))
      (interp-st->errmsg interp-st))
  ///
  (defthm not-check-reclimit-implies-posp-reclimit
    (implies (not (gl-interp-check-reclimit interp-st))
             (posp (interp-st->reclimit interp-st)))
    :rule-classes :forward-chaining)

  (def-updater-independence-thm gl-interp-check-reclimit-of-update
    (implies (and (equal (interp-st->reclimit new) (interp-st->reclimit old))
                  (equal (interp-st->errmsg new) (interp-st->errmsg old)))
             (equal (gl-interp-check-reclimit new) (gl-interp-check-reclimit old)))))


(set-state-ok t)

(progn
  (with-output
    :off (event prove)
    (defines gl-interp
      :flag-local nil
      (define gl-interp-test ((x pseudo-termp)
                              (interp-st interp-st-bfrs-ok)
                              state)
        ;; Translate a term to a GL object under the given alist substitution, preserving IFF.
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count x) 60)
        :well-founded-relation acl2::nat-list-<
        :verify-guards nil
        :measure-debug t
        ;; :guard (bfr-listp (gl-object-alist-bfrlist alist) (interp-st->bfrstate interp-st))
        :returns (mv xbfr
                     new-interp-st)
        (b* (((interp-st-bind
               (equiv-contexts '(iff)))
              ((gl-interp-recursive-call xobj interp-st)
               (gl-interp-term-equivs x interp-st state))))
          (gl-interp-simplify-if-test xobj interp-st state)))

      (define gl-interp-term-equivs ((x pseudo-termp)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020 (pseudo-term-binding-count x) 40)
        :returns (mv
                  (xobj gl-object-p)
                  new-interp-st)
        (b* (((mv xobj interp-st)
              (gl-interp-term x interp-st state))
             ;; ((when err) (mv nil interp-st state))
             ((unless (glcp-term-obj-p xobj))
              (mv xobj interp-st))
             (contexts (interp-st->equiv-contexts interp-st)))
          (stobj-let ((pathcond (interp-st->pathcond interp-st))
                      (logicman (interp-st->logicman interp-st))
                      (bvar-db (interp-st->bvar-db interp-st)))
                     (error val pathcond)
                     (try-equivalences-loop
                      xobj contexts 100 ;; bozo, configure reclimit for try-equivalences-loop?
                      pathcond bvar-db logicman state)
                     (b* (((when error)
                           (gl-interp-error
                            :msg (gl-msg "Try-equivalences-loop failed: ~@0" error))))
                       (mv val interp-st)))))

      (define gl-interp-term ((x pseudo-termp)
                              (interp-st interp-st-bfrs-ok)
                              state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count x) 20)
        :returns (mv
                  (xobj gl-object-p)
                  new-interp-st)
        (pseudo-term-case x
          :const (mv (g-concrete x.val) interp-st)
          :var (b* ((minor-look (assoc-eq x.name (interp-st-minor-bindings interp-st)))
                    ((when minor-look)
                     (mv (cdr minor-look) interp-st))
                    (major-look (assoc-eq x.name (interp-st-bindings interp-st)))
                    ((unless major-look)
                     (gl-interp-error
                      :msg (msg "Unbound variable: ~x0" x.name))))
                 (mv (cdr major-look) interp-st))
          :lambda
          (b* (((mv x-bindings body) (lambda-nest-to-bindinglist x))
               (interp-st (interp-st-push-minor-frame interp-st))
               (interp-st (interp-st-set-minor-debug x interp-st))
               ((interp-st-bind
                 (equiv-contexts nil))
                ((gl-interp-recursive-call interp-st)
                 ;; replaces the top of stack with the bindings
                 (gl-interp-bindinglist x-bindings interp-st state)))

               ;; ((when err)
               ;;  (b* ((interp-st (interp-st-pop-minor-frame interp-st)))
               ;;    (mv nil interp-st state)))
               ((mv val interp-st)
                (gl-interp-term-equivs body interp-st state))
               (interp-st (interp-st-pop-minor-frame interp-st)))
            (mv val interp-st))
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
                ((gl-interp-recursive-call args interp-st)
                 (gl-interp-arglist x.args interp-st state)))

               ;; ((when err)
               ;;  (mv nil interp-st state))
               )
            (gl-interp-fncall x.fn args interp-st state))))

      (define gl-interp-arglist ((args pseudo-term-listp)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-list-binding-count args) 20)
        :returns (mv
                  (arg-objs gl-objectlist-p)
                  new-interp-st)
        (b* (((when (atom args)) (mv nil interp-st))
             ((gl-interp-recursive-call arg1 interp-st)
              (gl-interp-term-equivs (car args) interp-st state))
             ;; ((when err) (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-gl-obj arg1 interp-st))
             ((mv rest interp-st)
              (gl-interp-arglist (cdr args) interp-st state))
             ((mv arg interp-st) (interp-st-pop-scratch-gl-obj interp-st)))
          (mv (cons arg rest) interp-st)))

      (define gl-interp-bindinglist ((bindings cmr::bindinglist-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (cmr::bindinglist-count bindings)
                       20)
        :returns new-interp-st
        (b* (((when (atom bindings)) interp-st)
             ((cmr::binding x1) (car bindings))
             ((gl-interp-recursive-call args interp-st)
              (gl-interp-arglist x1.args interp-st state))
             ;; ((when err) (mv interp-st state))
             (interp-st (interp-st-add-minor-bindings (pairlis$ x1.formals args) interp-st)))
          (gl-interp-bindinglist (cdr bindings) interp-st state)))
      
      (define gl-interp-fncall ((fn pseudo-fnsym-p)
                                (args gl-objectlist-p)
                                (interp-st interp-st-bfrs-ok)
                                state)
        :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       0 0 1)
        :returns (mv
                  (ans gl-object-p)
                  new-interp-st)
        (b* ((fn (pseudo-fnsym-fix fn))
             ((gl-function-mode fn-mode)
              (gl-function-mode-fix!
               (cdr (hons-assoc-equal fn (table-alist 'gl-fn-modes (w state))))))
             ((mv successp ans)
              (fncall-try-concrete-eval fn args fn-mode.dont-concrete-exec state))
             ((when successp)
              (mv ans interp-st))
             (reclimit (interp-st->reclimit interp-st))
             ((when (gl-interp-check-reclimit interp-st))
              (gl-interp-error
               :msg (gl-msg "The recursion limit ran out.")))
             (interp-st (interp-st-push-scratch-gl-objlist args interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((gl-interp-recursive-call successp ans interp-st)
               (gl-rewrite-fncall fn args fn-mode.dont-rewrite interp-st state)))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             ((when successp)
              (b* ((interp-st (interp-st-pop-scratch interp-st)))
                (mv ans interp-st)))
             (args (interp-st-top-scratch-gl-objlist interp-st))
             ((mv successp ans interp-st)
              (gl-primitive-fncall fn args fn-mode.dont-primitive-exec interp-st state))
             ((when successp)
              (b* ((interp-st (interp-st-pop-scratch interp-st)))
                (mv ans interp-st)))
             (args (interp-st-top-scratch-gl-objlist interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv successp ans interp-st)
               (gl-interp-fn-definition fn args fn-mode.dont-expand-def interp-st state)))
             ((mv args interp-st) (interp-st-pop-scratch-gl-objlist interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             ((when successp)
              (mv ans interp-st)))
          (mv (g-apply fn args) interp-st)))

      (define gl-interp-fn-definition ((fn pseudo-fnsym-p)
                                       (args gl-objectlist-p)
                                       (dont)
                                       (interp-st interp-st-bfrs-ok)
                                       state)
        :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
        :returns (mv successp
                     (ans gl-object-p)
                     new-interp-st)
        (b* (((when dont)
              (mv nil nil interp-st))
             (rules (fn-definition-rules fn (glcp-config->definition-table
                                             (interp-st->config interp-st))
                                         (w state)))
             ((unless rules)
              (mv nil nil interp-st))
             (interp-st (interp-st-push-scratch-gl-objlist args interp-st))
             ((mv successp ans interp-st)
              (gl-rewrite-try-rules rules fn interp-st state))
             (interp-st (interp-st-pop-scratch interp-st)))
          (mv successp ans interp-st)))


      (define gl-rewrite-fncall ((fn pseudo-fnsym-p)
                                 (args gl-objectlist-p)
                                 (dont)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
        :returns (mv successp
                     (ans gl-object-p)
                     new-interp-st)
        (b* (((when dont)
              (mv nil nil interp-st))
             (rules (fn-rewrite-rules fn (glcp-config->rewrite-rule-table
                                          (interp-st->config interp-st))
                                      (w state)))
             ((unless rules)
              (mv nil nil interp-st))
             (interp-st (interp-st-push-scratch-gl-objlist args interp-st))
             ((mv successp ans interp-st)
              (gl-rewrite-try-rules rules fn interp-st state))
             (interp-st (interp-st-pop-scratch interp-st)))
          (mv successp ans interp-st)))
      

      (define gl-rewrite-try-rules ((rules pseudo-rewrite-rule-listp)
                                    (fn pseudo-fnsym-p)
                                    (interp-st interp-st-bfrs-ok)
                                    state)
        :guard (and (< 0 (interp-st-scratch-len interp-st))
                    (scratchobj-case (interp-st-top-scratch interp-st) :gl-objlist))
        ;; :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 (len rules) 0)
        :returns (mv successp
                     (ans gl-object-p)
                     new-interp-st)
        (b* (((when (atom rules))
              (mv nil nil interp-st))
             (args (interp-st-top-scratch-gl-objlist interp-st))
             ((gl-interp-recursive-call successp ans interp-st)
              (gl-rewrite-try-rule (car rules) fn args interp-st state))
             ((when successp)
              (mv successp ans interp-st)))
          (gl-rewrite-try-rules (cdr rules) fn interp-st state)))

      (define gl-rewrite-try-rule ((rule pseudo-rewrite-rule-p)
                                   (fn pseudo-fnsym-p)
                                   (args gl-objectlist-p)
                                   (interp-st interp-st-bfrs-ok)
                                   state)
        :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 0)
        :returns (mv successp
                     (ans gl-object-p)
                     new-interp-st)
        (b* (((acl2::rewrite-rule rule))
             ((unless (and** (mbt (and* (symbolp rule.equiv)
                                        (not (eq rule.equiv 'quote))
                                        ;; (ensure-equiv-relationp rule.equiv (w state))
                                        (not (eq rule.subclass 'acl2::meta))
                                        (pseudo-termp rule.lhs)))
                             (pseudo-term-case rule.lhs
                               :fncall (and (eq rule.lhs.fn (pseudo-fnsym-fix fn))
                                            ;; (eql (len rule.lhs.args) (len args))
                                            )
                               :otherwise nil)))
              (gl-interp-error
               :msg (gl-msg "Malformed rewrite rule: ~x0~%" rule)
               :nvals 2))
             ((unless (or (eq rule.equiv 'equal)
                          ;; bozo check refinements
                          (member rule.equiv (interp-st->equiv-contexts interp-st))))
              (mv nil nil interp-st))
             (rule.lhs.args (pseudo-term-call->args rule.lhs))
             ((mv unify-ok bindings) (glcp-unify-term/gobj-list rule.lhs.args
                                                                args
                                                                nil))
             ((unless unify-ok) (mv nil nil interp-st))
             ((unless (mbt (pseudo-term-listp rule.hyps)))
              (gl-interp-error
               :msg (gl-msg "Malformed rewrite rule: ~x0~%" rule)
               :nvals 2))
             (backchain-limit (interp-st->backchain-limit interp-st))
             ((when (and** rule.hyps (eql 0 backchain-limit)))
              (mv nil nil interp-st))
             ((when (interp-st->errmsg interp-st))
              ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
              (mv nil nil interp-st))
             (flags (interp-st->flags interp-st))
             (hyps-flags  (!interp-flags->intro-synvars
                           t
                           (!interp-flags->intro-bvars
                            nil
                            (!interp-flags->simplify-logic nil flags))))
             (interp-st (interp-st-push-frame bindings interp-st))
             (interp-st (interp-st-set-debug rule interp-st))
             ((interp-st-bind
               (flags hyps-flags flags)
               (equiv-contexts '(iff))
               (backchain-limit (1- backchain-limit) backchain-limit))
              ((gl-interp-recursive-call successp interp-st)
               (gl-rewrite-relieve-hyps rule.hyps interp-st state)))

             ((unless (and** successp (not (interp-st->errmsg interp-st))))
              (b* ((interp-st (interp-st-pop-frame interp-st))
                   (interp-st (interp-st-cancel-error :intro-bvars-fail interp-st)))
                (mv nil nil interp-st)))

             (concl-flags (!interp-flags->intro-synvars t flags))
             ((interp-st-bind
               (flags concl-flags flags))
              ((mv val interp-st)
               (gl-interp-term-equivs rule.rhs interp-st state)))

             (interp-st (interp-st-pop-frame interp-st)))

          (mv t val interp-st)))
      
      (define gl-rewrite-relieve-hyps ((hyps pseudo-term-listp)
                                       (interp-st interp-st-bfrs-ok)
                                       state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 9000
                       (pseudo-term-list-binding-count hyps) 0)
        :returns (mv successp
                     new-interp-st)
        (b* (((when (atom hyps))
              (mv t interp-st))
             ((gl-interp-recursive-call ok interp-st)
              (gl-rewrite-relieve-hyp (car hyps) interp-st state))
             ((when (not ok))
              (mv ok interp-st)))
          (gl-rewrite-relieve-hyps (cdr hyps) interp-st state)))
      
      (define gl-rewrite-relieve-hyp ((hyp pseudo-termp)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 9000
                       (pseudo-term-binding-count hyp) 0)
        :returns (mv successp
                     new-interp-st)
        (b* (((mv synp-type untrans-form trans-term vars)
              (gl-interp-match-synp hyp))
             ((when synp-type)
              (gl-rewrite-relieve-hyp-synp synp-type trans-term vars untrans-form interp-st state))
             ((mv test-bfr interp-st)
              (gl-interp-test hyp interp-st state)))
          (mv (eq test-bfr t) interp-st)))

      (define gl-interp-time$ ((timing-arg pseudo-termp)
                               (x pseudo-termp)
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                       (+ (pseudo-term-binding-count timing-arg)
                          (pseudo-term-binding-count x))
                       30)
        :returns (mv
                  (xobj gl-object-p)
                  new-interp-st)
        (b* (((interp-st-bind
               (equiv-contexts nil))
              ((gl-interp-recursive-call time$-arg interp-st)
               (gl-interp-term-equivs timing-arg interp-st state)))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             (time$-arg (gl-interp-time$-arg time$-arg x)))
          (acl2::time$1 time$-arg
                        (gl-interp-term-equivs x interp-st state))))
      
      (define gl-interp-return-last ((return-last-fnname pseudo-termp)
                                     (first-arg pseudo-termp)
                                     (x pseudo-termp)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                       (+ (pseudo-term-binding-count first-arg)
                          (pseudo-term-binding-count x))
                       40)
        :returns (mv
                  (xobj gl-object-p)
                  new-interp-st)
        (b* (((when (equal return-last-fnname ''time$1-raw))
              (gl-interp-time$ first-arg x interp-st state))
             ((when (equal return-last-fnname ''(syntax-bind)))
              (gl-interp-syntax-bind first-arg x interp-st state)))
          ;; Otherwise just evaluate the last-arg.
          (gl-interp-term-equivs x interp-st state)))
      
      

      (define gl-interp-if/or ((test pseudo-termp)
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
                  (ans gl-object-p)
                  new-interp-st)
        (if (hons-equal test then)
            (gl-interp-or test else interp-st state)
          (gl-interp-if test then else interp-st state)))

      
      (define gl-interp-if ((test pseudo-termp)
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
                  (ans gl-object-p)
                  new-interp-st)
        ;; Tricky because we have to keep the test/thenval on the stack while we
        ;; run the then/else branches, because we might simplify the logicman while
        ;; running them.
        (b* (((gl-interp-recursive-call testbfr interp-st)
              (gl-interp-test test interp-st state))
             ;; ((when err) (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((gl-interp-recursive-call then-unreachable thenval interp-st)
              ;; pushes val onto scratch if not unreachable
              (gl-maybe-interp testbfr then interp-st state))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             (testbfr (interp-st-top-scratch-bfr interp-st))
             (interp-st (interp-st-push-scratch-gl-obj thenval interp-st))
             ((gl-interp-recursive-call else-unreachable elseval interp-st)
              ;; pushes val onto scratch if not unreachable
              (gl-maybe-interp (interp-st-bfr-not testbfr) else interp-st state))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st))
             ;;       (interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             ((mv thenval interp-st) (interp-st-pop-scratch-gl-obj interp-st))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((when then-unreachable)
              (if else-unreachable
                  (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
                    (mv nil interp-st))
                (mv elseval interp-st)))
             ((when else-unreachable)
              (mv thenval interp-st)))
          (gl-interp-merge-branches testbfr thenval elseval interp-st state)))

      (define gl-interp-or ((test pseudo-termp)
                            (else pseudo-termp)
                            (interp-st interp-st-bfrs-ok)
                            state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (+ (pseudo-term-binding-count test)
                          (pseudo-term-binding-count else))
                       40)
        :returns (mv
                  (ans gl-object-p)
                  new-interp-st)
        (b* ((equiv-contexts (interp-st->equiv-contexts interp-st))
             (or-test-equiv-contexts (gl-interp-or-test-equiv-contexts equiv-contexts))
             ((interp-st-bind
               (equiv-contexts or-test-equiv-contexts equiv-contexts))
              ((gl-interp-recursive-call testval interp-st)
               (gl-interp-term-equivs test interp-st state)))
             ;; ((when err) (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-gl-obj testval interp-st))
             ((gl-interp-recursive-call testbfr interp-st)
              (gl-interp-simplify-if-test testval interp-st state))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((gl-interp-recursive-call else-unreachable elseval interp-st)
              (gl-maybe-interp (interp-st-bfr-not testbfr) else interp-st state))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv testval interp-st) (interp-st-pop-scratch-gl-obj interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             ((when else-unreachable)
              (mv testval interp-st)))
          (gl-interp-merge-branches testbfr testval elseval interp-st state)))


      (define gl-maybe-interp ((test interp-st-bfr-p)
                               (x pseudo-termp)
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (pseudo-term-binding-count x)
                       60)
        :returns (mv
                  unreachable
                  (ans gl-object-p)
                  new-interp-st)
        (b* (((mv contra interp-st)
              (interp-st-pathcond-assume test interp-st))
             ((when contra)
              (mv t nil interp-st))
             ((when (interp-st->errmsg interp-st))
              (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
                (mv nil nil interp-st)))
             ((mv ans interp-st)
              (gl-interp-term-equivs x interp-st state))
             (interp-st (interp-st-pathcond-rewind interp-st))
             ((when (eq (interp-st->errmsg interp-st) :unreachable))
              (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
                (mv t nil interp-st))))
          (mv nil ans interp-st)))

      (define gl-interp-maybe-simplify-if-test ((test interp-st-bfr-p)
                                                (xobj gl-object-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
        :guard (interp-st-bfr-listp (gl-object-bfrlist xobj))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       0
                       (gl-object-count xobj)
                       60)
        :returns (mv
                  unreachable
                  xbfr
                  new-interp-st)
        (b* (((mv contra interp-st)
              (interp-st-pathcond-assume test interp-st))
             ((when contra)
              (mv t nil interp-st))
             (reclimit (interp-st->reclimit interp-st))
             ((when (gl-interp-check-reclimit interp-st))
              (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                (gl-interp-error :msg (gl-msg "The recursion limit ran out.") :nvals 2)))
             ((when (interp-st->errmsg interp-st))
              (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
                ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
                (mv nil nil interp-st)))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv ans interp-st)
               (gl-interp-simplify-if-test xobj interp-st state)))
             (interp-st (interp-st-pathcond-rewind interp-st))
             ((when (eq (interp-st->errmsg interp-st) :unreachable))
              (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
                (mv t nil interp-st))))
          (mv nil ans interp-st)))

      (define gl-interp-simplify-if-test ((xobj gl-object-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)
        :guard (interp-st-bfr-listp (gl-object-bfrlist xobj))
        :returns (mv
                  xbfr
                  new-interp-st)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (gl-object-count xobj)
                       40)
        (gl-object-case xobj
          :g-concrete (mv (bool-fix xobj.val) interp-st)
          :g-boolean (mv xobj.bool interp-st)
          :g-integer (mv t interp-st)
          :g-cons (mv t interp-st)
          :g-var (interp-st-add-term-bvar-unique xobj interp-st state)
          :g-ite (gl-interp-simplify-if-test-ite xobj interp-st state)
          :g-apply (gl-interp-simplify-if-test-fncall xobj interp-st state)))

      ;; BOZO should we have a version of this for OR?
      (define gl-interp-simplify-if-test-ite ((xobj gl-object-p)
                                              (interp-st interp-st-bfrs-ok)
                                              state)
        :guard (and (gl-object-case xobj :g-ite)
                    (interp-st-bfr-listp (gl-object-bfrlist xobj)))
        :returns (mv
                  xbfr
                  new-interp-st)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (gl-object-count xobj)
                       30)
        (b* (((unless (mbt (gl-object-case xobj :g-ite)))
              (gl-interp-error :msg (gl-msg "Impossible case")))
             ((g-ite xobj))
             (interp-st (interp-st-push-scratch-gl-obj xobj.else interp-st))
             (interp-st (interp-st-push-scratch-gl-obj xobj.then interp-st))
             ;; scratch: xobj.then, xobj.else
             ((gl-interp-recursive-call test-bfr interp-st)
              (gl-interp-simplify-if-test xobj.test interp-st state))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st))
             ;;       (interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             (xobj.then (interp-st-top-scratch-gl-obj interp-st))
             (interp-st (interp-st-update-scratch-bfr 0 test-bfr interp-st))
             ;; scratch: test-bfr, xobj.else
             ((gl-interp-recursive-call then-unreachable then-bfr interp-st)
              (gl-interp-maybe-simplify-if-test test-bfr xobj.then interp-st state))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st))
             ;;       (interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             (test-bfr (interp-st-top-scratch-bfr interp-st))
             (xobj.else (interp-st-nth-scratch-gl-obj 1 interp-st))
             (interp-st (interp-st-update-scratch-bfr 1 then-bfr interp-st))
             (neg-test (stobj-let ((logicman (interp-st->logicman interp-st)))
                                  (not)
                                  (bfr-not test-bfr)
                                  not))
             ;; scratch: test-bfr, then-bfr
             ((mv else-unreachable else-bfr interp-st)
              (gl-interp-maybe-simplify-if-test neg-test xobj.else interp-st state))
             ;; ((when err)
             ;;  (b* ((interp-st (interp-st-pop-scratch interp-st))
             ;;       (interp-st (interp-st-pop-scratch interp-st)))
             ;;    (mv nil interp-st state)))
             ((mv test-bfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv then-bfr interp-st) (interp-st-pop-scratch-bfr interp-st)))
          (gl-interp-finish-simplify-if-test-ite
               test-bfr then-bfr else-bfr then-unreachable else-unreachable interp-st)))
      ;;    ((when then-unreachable)
      ;;     (if else-unreachable
      ;;         (mv :unreachable nil interp-st state)
      ;;       (mv nil else-bfr interp-st state)))
      ;;    ((when else-unreachable)
      ;;     (mv nil then-bfr interp-st state))
      ;;    ((mv ite interp-st) (stobj-let ((logicman (interp-st->logicman interp-st)))
      ;;                                   (ite logicman)
      ;;                                   (bfr-ite test-bfr then-bfr else-bfr)
      ;;                                   (mv ite interp-st))))
      ;; (mv nil ite interp-st state)))

      (define gl-interp-simplify-if-test-fncall ((xobj gl-object-p)
                                                 (interp-st interp-st-bfrs-ok)
                                                 state)
        :guard (and (gl-object-case xobj :g-apply)
                    (interp-st-bfr-listp (gl-object-bfrlist xobj)))

        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (gl-object-count xobj)
                       20)
        :returns (mv
                  xbfr
                  new-interp-st)
        (b* (((unless (mbt (gl-object-case xobj :g-apply)))
              (gl-interp-error :msg (gl-msg "Impossible")))
             ((mv not-matched neg-arg)
              (gl-apply-match-not xobj))
             ((when not-matched)
              (b* (((mv bfr interp-st)
                    (gl-interp-simplify-if-test neg-arg interp-st state))
                   ;; ((when err)
                   ;;  (mv nil interp-st state))
                   )
                (mv (interp-st-bfr-not bfr) interp-st)))
             ((g-apply xobj))
             ((gl-function-mode fn-mode)
              (gl-function-mode-fix!
               (cdr (hons-assoc-equal xobj.fn (table-alist 'gl-fn-modes (w state))))))

             ;; BOZO support gl-interp-force-check.

             ;; We rewrite this fncall again because it presumably might not have
             ;; been done in IFF context before.  E.g.
             ;; (let ((a (foo x)))
             ;;   (if a y z))
             ;; Note we wouldn't do this fully "right" even if we had perfect
             ;; knowledge of congruences because our test term might be bound to a
             ;; variable that is used in both Boolean and non-Boolean contexts.
             (reclimit (interp-st->reclimit interp-st))
             ((when (gl-interp-check-reclimit interp-st))
              (gl-interp-error
               :msg (gl-msg "The recursion limit ran out.")))
             (interp-st (interp-st-push-scratch-gl-obj xobj interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit)
               (equiv-contexts '(iff)))
              ((gl-interp-recursive-call successp ans interp-st)
               (gl-rewrite-fncall xobj.fn xobj.args fn-mode.dont-rewrite-under-if-test interp-st state)))

             ((mv xobj interp-st) (interp-st-pop-scratch-gl-obj interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             ((when successp)
              (b* (((interp-st-bind
                     (reclimit (1- reclimit) reclimit))
                    ((mv ans interp-st)
                     (gl-interp-simplify-if-test ans interp-st state))))
                (mv ans interp-st)))

             (look (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
                              (look)
                              (get-term->bvar xobj bvar-db)
                              look))
             ((when look)
              (b* ((bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
                                   (bfr)
                                   (bfr-var look)
                                   bfr)))
                (mv bfr interp-st)))

             ((unless (interp-flags->intro-bvars (interp-st->flags interp-st)))
              ;; Note: we only return intro-bvars-fail when this flag is set to
              ;; false, which it is not at the top level.  So when we set the flag
              ;; to true (as we do in relieve-hyp and add-bvar-constraint-substs,
              ;; e.g.) we check for this error specifically and catch it.
              ;; Otherwise we expect callers not to set intro-bvars to nil and then
              ;; they won't have to deal with this error specially.
              (b* ((interp-st (interp-st-set-error :intro-bvars-fail interp-st)))
                (mv nil interp-st)))

             ((unless (gl-object-symbolic-boolean-free xobj))
              (gl-interp-error
               :msg (gl-msg "An object used as an IF test was not reduced to ~
                             either a term-like object or a symbolic Boolean, ~
                             i.e. it had both function calls and symbolic ~
                             Boolean parts.  This isn't currently allowed.  ~
                             The state global variable (~x0 ~x1) holds the object."
                            '@ 'gl-interp-error-debug-obj)
               :debug-obj xobj))

             ((mv bfr interp-st)
              (interp-st-add-term-bvar xobj interp-st state))

             (interp-st (interp-st-push-scratch-bfr bfr interp-st))

             (interp-st
              (gl-interp-add-constraints xobj interp-st state))

             ((mv bfr interp-st) (interp-st-pop-scratch-bfr interp-st))

             ;; ((when err)
             ;;  (mv nil interp-st state))
             )
          (mv bfr interp-st)))


      (define gl-interp-add-constraints ((xobj gl-object-p)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
        :guard (and ;; (gl-object-case xobj :g-apply)
                    (interp-st-bfr-listp (gl-object-bfrlist xobj)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       1900
                       (gl-object-count xobj)
                       15)
        :returns new-interp-st
        (b* ((constraint-db (interp-st->constraint-db interp-st))
             ((mv constraint-substs constraint-db)
              (gbc-process-new-lit xobj constraint-db state))
             (interp-st (update-interp-st->constraint-db constraint-db interp-st))
             ((unless constraint-substs) interp-st)
             (reclimit (interp-st->reclimit interp-st))
             ((when (gl-interp-check-reclimit interp-st))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.") :nvals 0))
             ;; Disable the pathcond so that constraint thms are simulated in an empty (universal) context.
             ((mv pathcond-enabledp interp-st) (stobj-let ((pathcond (interp-st->pathcond interp-st)))
                                                          (enabledp pathcond)
                                                          (b* ((enabledp (pathcond-enabledp pathcond))
                                                               (pathcond (update-pathcond-enabledp nil pathcond)))
                                                            (mv enabledp pathcond))
                                                          (mv enabledp interp-st)))

             (flags (interp-st->flags interp-st))
             (new-flags  (!interp-flags->intro-synvars
                          t
                          (!interp-flags->intro-bvars
                           nil
                           (!interp-flags->simplify-logic nil flags))))
             ((interp-st-bind
               (flags new-flags flags)
               (reclimit (1- reclimit) reclimit))
              (interp-st
               (gl-interp-add-constraints-for-substs constraint-substs interp-st state))))
          
          (stobj-let ((pathcond (interp-st->pathcond interp-st)))
                     (pathcond)
                     (update-pathcond-enabledp pathcond-enabledp pathcond)
                     interp-st)))
      


      (define gl-interp-add-constraints-for-substs ((substs constraint-instancelist-p)
                                                    (interp-st interp-st-bfrs-ok)
                                                    state)
        :guard (interp-st-bfr-listp (constraint-instancelist-bfrlist substs))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       10000
                       (len substs)
                       10)
        :returns new-interp-st
        (b* (((when (atom substs)) interp-st)
             ((constraint-instance sub1) (car substs))
             (thm-body (meta-extract-formula sub1.thmname state))
             ((unless (pseudo-termp thm-body))
              (gl-interp-add-constraints-for-substs (cdr substs) interp-st state))
             ((when (interp-st->errmsg interp-st))
              ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
              interp-st)
             (interp-st (interp-st-push-scratch-cinstlist (cdr substs) interp-st))
             (interp-st (interp-st-push-frame sub1.subst interp-st))
             ((gl-interp-recursive-call bfr interp-st)
              (gl-interp-test thm-body interp-st state))
             (interp-st (interp-st-pop-frame interp-st))
             ((mv rest interp-st) (interp-st-pop-scratch-cinstlist interp-st))
             ((unless (mbt (eql (len rest) (len (cdr substs)))))
              ;; impossible case
              interp-st)
             
             ((when (interp-st->errmsg interp-st))
              (b* ((interp-st (interp-st-cancel-error :intro-bvars-fail interp-st)))
                (gl-interp-add-constraints-for-substs rest interp-st state)))
             ;; ((when err)
             ;;  (mv interp-st state))
             ((mv contra interp-st) (stobj-let ((constraint-pathcond (interp-st->constraint interp-st))
                                                (logicman (interp-st->logicman interp-st)))
                                               (contra constraint-pathcond)
                                               (logicman-pathcond-assume bfr constraint-pathcond)
                                               (mv contra interp-st)))
             ((when contra)
              (gl-interp-error
               :msg (gl-msg "A contradiction has been noted in the ~
                             constraints.  This is likely due to a bug in GL ~
                             or an unsound fact stored in ACL2 (e.g., via ~
                             TTAG, skip-proofs, defaxiom, or soundness bug). ~
                             The constraint instance that led to the ~
                             contradiction is stored in the state global (~x0 ~
                             ~x1), but note that a previous constraint ~
                             instance might have caused the unsoundness."
                            '@ 'gl-interp-error-debug-obj)
               :debug-obj sub1
               :nvals 0)))
          (gl-interp-add-constraints-for-substs rest interp-st state)))
      

      (define gl-interp-merge-branches ((testbfr interp-st-bfr-p)
                                        (thenval gl-object-p)
                                        (elseval gl-object-p)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
        :guard (and (interp-st-bfr-listp (gl-object-bfrlist thenval))
                    (interp-st-bfr-listp (gl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000 0 0)
        :returns (mv
                  (ans gl-object-p)
                  new-interp-st)
        (b* ((thenval (gl-object-fix thenval))
             (elseval (gl-object-fix elseval))
             ((when (eq testbfr t)) (mv thenval interp-st))
             ((when (eq testbfr nil)) (mv elseval interp-st))
             ((when (hons-equal thenval elseval)) (mv thenval interp-st)))
          (gl-interp-merge-branches-rewrite testbfr thenval elseval nil interp-st state)))

      (define gl-interp-merge-branches-rewrite ((testbfr interp-st-bfr-p)
                                                (thenval gl-object-p)
                                                (elseval gl-object-p)
                                                switchedp
                                                (interp-st interp-st-bfrs-ok)
                                                state)
        :guard (and (interp-st-bfr-listp (gl-object-bfrlist thenval))
                    (interp-st-bfr-listp (gl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       1900 0 (if switchedp 20 30))
        :returns (mv
                  (ans gl-object-p)
                  new-interp-st)
        (b* ((thenval (gl-object-fix thenval))
             (elseval (gl-object-fix elseval))
             (fn (gl-fncall-object->fn thenval))
             (rules (and** fn (fn-branch-merge-rules fn 
                                                     (glcp-config->branch-merge-rules
                                                      (interp-st->config interp-st))
                                                     (w state))))
             ((unless rules)
              ;; Note: we try to apply if-merge rules based on the leading function
              ;; symbol of the then or else objects.  We try then first
              ;; (switchedp=nil), then else (switchedp=t), and if both fail we move
              ;; on to merge-branches-subterms.
              (if switchedp
                  (gl-interp-merge-branch-subterms
                   (interp-st-bfr-not testbfr)
                   elseval thenval interp-st state)
                (gl-interp-merge-branches-rewrite
                 (interp-st-bfr-not testbfr)
                 elseval thenval t interp-st state)))

             (reclimit (interp-st->reclimit interp-st))
             ((when (gl-interp-check-reclimit interp-st))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.")))
             (interp-st (interp-st-push-scratch-gl-obj elseval interp-st))
             (interp-st (interp-st-push-scratch-gl-obj thenval interp-st))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             (interp-st (interp-st-push-scratch-gl-objlist
                         (list (g-boolean testbfr) thenval elseval)
                         interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv successp ans interp-st)
               (gl-rewrite-try-rules rules 'if interp-st state)))
             (interp-st (interp-st-pop-scratch interp-st))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv thenval interp-st) (interp-st-pop-scratch-gl-obj interp-st))
             ((mv elseval interp-st) (interp-st-pop-scratch-gl-obj interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             ((when successp)
              (mv ans interp-st)))
          (if switchedp
              (gl-interp-merge-branch-subterms
               (interp-st-bfr-not testbfr)
               elseval thenval interp-st state)
            (gl-interp-merge-branches-rewrite
             (interp-st-bfr-not testbfr)
             elseval thenval t interp-st state))))

      (define gl-interp-merge-branch-subterms ((testbfr interp-st-bfr-p)
                                               (thenval gl-object-p)
                                               (elseval gl-object-p)
                                               (interp-st interp-st-bfrs-ok)
                                               state)
        :guard (and (interp-st-bfr-listp (gl-object-bfrlist thenval))
                    (interp-st-bfr-listp (gl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       1800 0 0)
        :returns (mv
                  (ans gl-object-p)
                  new-interp-st)
        (b* (((mv thenfn thenargs) (gl-object-recognize-merge-fncall thenval))
             ((mv elsefn elseargs) (gl-object-recognize-merge-fncall elseval))
             ((unless (and** thenfn
                             (eq thenfn elsefn)
                             (eql (len thenargs) (len elseargs))))
              (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (obj logicman)
                         (gl-object-basic-merge testbfr thenval elseval)
                         (mv obj interp-st)))
             ;; BOZO sad:
             (reclimit (interp-st->reclimit interp-st))
             ((when (gl-interp-check-reclimit interp-st))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.")))

             ;; (scratch (interp-st-scratch interp-st))
             ;; (thenval-stack (interp-st->thenval-stack interp-st))
             ;; (elseval-stack (interp-st->elseval-stack interp-st))
             ;; (interp-st (update-interp-st->thenval-stack (append thenargs thenval-stack) interp-st))
             ;; (interp-st (update-interp-st->elseval-stack (append elseargs elseval-stack) interp-st))
             ;; (interp-st (interp-st-push-bool-scratch testbfr interp-st))
             ;; ;; pops args off thenval/elseval-stack, pushes onto scratch

             
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit)
               (equiv-contexts nil))
              ((gl-interp-recursive-call args interp-st)
               (gl-interp-merge-branch-args testbfr thenargs elseargs interp-st state)))

             ;; ((when err)
             ;;  ;; pop off any args pushed on before error
             ;;  (b* (;; (interp-st (interp-st-pop-scratch (- (len (interp-st-scratch interp-st))
             ;;       ;;                                      (len scratch))
             ;;       ;;                                   interp-st))
             ;;       ;; (new-thenval-stack (interp-st->thenval-stack interp-st))
             ;;       ;; (interp-st (update-interp-st->thenval-stack
             ;;       ;;             (nthcdr (- (len new-thenval-stack)
             ;;       ;;                        (len thenval-stack))
             ;;       ;;                     new-thenval-stack)
             ;;       ;;             interp-st))
             ;;       ;; (new-elseval-stack (interp-st->elseval-stack interp-st))
             ;;       ;; (interp-st (update-interp-st->elseval-stack
             ;;       ;;             (nthcdr (- (len new-elseval-stack)
             ;;       ;;                        (len elseval-stack))
             ;;       ;;                     new-elseval-stack)
             ;;       ;;             interp-st))
             ;;       )
             ;;    (mv nil interp-st state)))
             )
          (gl-interp-fncall thenfn args interp-st state)))

      (define gl-interp-merge-branch-args ((testbfr interp-st-bfr-p)
                                           (thenargs gl-objectlist-p)
                                           (elseargs gl-objectlist-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
        :guard (and (eql (len thenargs) (len elseargs))
                    (interp-st-bfr-listp (gl-objectlist-bfrlist thenargs))
                    (interp-st-bfr-listp (gl-objectlist-bfrlist elseargs)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       3000 (len thenargs) 0)
        :returns (mv
                  (args gl-objectlist-p)
                  new-interp-st)
        (b* (((when (atom thenargs))
              (mv nil interp-st))
             ;; (thenstack (interp-st->thenval-stack interp-st))
             ;; (thenval (car thenstack))
             ;; (interp-st (update-interp-st->thenval-stack (cdr thenstack) interp-st))
             ;; (elsestack (interp-st->elseval-stack interp-st))
             ;; (elseval (car elsestack))
             ;; (interp-st (update-interp-st->elseval-stack (cdr elsestack) interp-st))
             (interp-st (interp-st-push-scratch-gl-objlist (cdr thenargs) interp-st))
             (interp-st (interp-st-push-scratch-gl-objlist (cdr elseargs) interp-st))
             (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
             ((gl-interp-recursive-call ans interp-st)
              (gl-interp-merge-branches testbfr (car thenargs) (car elseargs) interp-st state))
             ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
             ((mv rest-elseargs interp-st) (interp-st-pop-scratch-gl-objlist interp-st))
             ((mv rest-thenargs interp-st) (interp-st-pop-scratch-gl-objlist interp-st))
             
             ((unless (mbt (eql (len (cdr thenargs)) (len rest-thenargs))))
              (mv nil interp-st))
             ;; ((when err)
             ;;  (mv nil interp-st state))
             (interp-st (interp-st-push-scratch-gl-obj ans interp-st))
             ((mv args interp-st)
              (gl-interp-merge-branch-args testbfr rest-thenargs rest-elseargs interp-st state))
             ((mv arg1 interp-st) (interp-st-pop-scratch-gl-obj interp-st)))
          (mv (cons arg1 args) interp-st))))))




(local (defun find-flag-is-hyp (clause)
         (if (atom clause)
             nil
           (let ((lit (car clause)))
             (case-match lit
               (('not ('acl2::flag-is ('quote val))) val)
               (& (find-flag-is-hyp (cdr clause))))))))


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
                   (and (or (not ',wait-til-stablep) stable-under-simplificationp)
                        (expand-marked)))
                  :in-theory (disable . ,fns)
                  :do-not-induct t
                  :clause-processor (cmr::resolve-flags-cp
                                     clause
                                     ',(cons 'acl2::flag fns)))))))

(defsection stack-isomorphic-of-gl-interp

  (define scratchobj-isomorphic ((x scratchobj-p) (y scratchobj-p))
    (and (eq (scratchobj-kind x) (scratchobj-kind y))
         (scratchobj-case x
           :gl-objlist (eql (len x.val) (len (scratchobj-gl-objlist->val y)))
           :bfrlist (eql (len x.val) (len (scratchobj-bfrlist->val y)))
           :cinstlist (eql (len x.val) (len (scratchobj-cinstlist->val y)))
           :otherwise t))
    ///
    (defequiv scratchobj-isomorphic)

    (defcong scratchobj-isomorphic equal (scratchobj-kind x) 1)

    (defthm len-gl-objlist-when-scratchobj-isomorphic
      (implies (and (scratchobj-isomorphic x y)
                    (scratchobj-case x :gl-objlist))
               (= (len (scratchobj-gl-objlist->val x))
                  (len (scratchobj-gl-objlist->val y))))
      :rule-classes :linear)

    (defthm len-bfrlist-when-scratchobj-isomorphic
      (implies (and (scratchobj-isomorphic x y)
                    (scratchobj-case x :bfrlist))
               (= (len (scratchobj-bfrlist->val x))
                  (len (scratchobj-bfrlist->val y))))
      :rule-classes :linear)

    (defthm len-cinstlist-when-scratchobj-isomorphic
      (implies (and (scratchobj-isomorphic x y)
                    (scratchobj-case x :cinstlist))
               (= (len (scratchobj-cinstlist->val x))
                  (len (scratchobj-cinstlist->val y))))
      :rule-classes :linear))

  (define scratchlist-isomorphic ((x scratchlist-p) (y scratchlist-p))
    (if (atom x)
        (atom y)
      (and (consp y)
           (scratchobj-isomorphic (car x) (car y))
           (scratchlist-isomorphic (cdr x) (cdr y))))
    ///
    (defequiv scratchlist-isomorphic)

    (defcong scratchlist-isomorphic scratchobj-isomorphic (car x) 1
      :hints(("Goal" :in-theory (enable default-car))))
    (defcong scratchlist-isomorphic scratchlist-isomorphic (cdr x) 1)
    
    (defcong scratchobj-isomorphic scratchlist-isomorphic (cons x y) 1)
    (defcong scratchlist-isomorphic scratchlist-isomorphic (cons x y) 2)

    (defcong scratchlist-isomorphic equal (len x) 1
      :hints(("Goal" :in-theory (enable len)))))

  (define minor-frame-scratch-isomorphic ((x minor-frame-p) (y minor-frame-p))
    (scratchlist-isomorphic (minor-frame->scratch x) (minor-frame->scratch y))
    ///
    (defequiv minor-frame-scratch-isomorphic)

    (defcong minor-frame-scratch-isomorphic scratchlist-isomorphic (minor-frame->scratch x) 1)

    (defcong scratchlist-isomorphic minor-frame-scratch-isomorphic (minor-frame bindings scratch debug) 2)

    (defthm minor-frame-scratch-isomorphic-normalize-minor-frame
      (implies (syntaxp (not (and (Equal bindings ''nil)
                                  (equal debug ''nil))))
               (minor-frame-scratch-isomorphic (minor-frame bindings scratch debug)
                                               (minor-frame nil scratch nil)))))

  (define minor-stack-scratch-isomorphic ((x minor-stack-p) (y minor-stack-p))
    (and (minor-frame-scratch-isomorphic (car x) (car y))
         (if (atom (cdr x))
             (atom (cdr y))
           (and (consp (cdr y))
                (minor-stack-scratch-isomorphic (cdr x) (cdr y)))))
    ///
    (defequiv minor-stack-scratch-isomorphic)

    (defcong minor-stack-scratch-isomorphic minor-frame-scratch-isomorphic (car x) 1
      :hints(("Goal" :in-theory (enable default-car))))
    (defcong minor-stack-scratch-isomorphic minor-stack-scratch-isomorphic (cdr x) 1
      :hints(("Goal" :in-theory (enable default-car))))
    
    (defcong minor-frame-scratch-isomorphic minor-stack-scratch-isomorphic (cons x y) 1)

    (defthm minor-stack-scratch-isomorphic-cons-cdr-congruence
      (implies (minor-stack-scratch-isomorphic x y)
               (minor-stack-scratch-isomorphic (cons frame (cdr x))
                                               (cons frame (cdr y))))
      :rule-classes :congruence)

    (defcong minor-stack-scratch-isomorphic acl2::pos-equiv (len x) 1
      :hints(("Goal" :in-theory (enable len pos-fix)))))


  (define major-frame-scratch-isomorphic ((x major-frame-p) (y major-frame-p))
    (minor-stack-scratch-isomorphic (major-frame->minor-stack x) (major-frame->minor-stack y))
    ///
    (defequiv major-frame-scratch-isomorphic)

    (defcong major-frame-scratch-isomorphic minor-stack-scratch-isomorphic (major-frame->minor-stack x) 1)

    (defcong minor-stack-scratch-isomorphic major-frame-scratch-isomorphic (major-frame bindings debug minor-stack) 3)

    (defthm major-frame-scratch-isomorphic-normalize-major-frame
      (implies (syntaxp (not (and (Equal bindings ''nil)
                                  (equal debug ''nil))))
               (major-frame-scratch-isomorphic (major-frame bindings debug minor-stack)
                                               (major-frame nil nil minor-stack)))))

  (define major-stack-scratch-isomorphic ((x major-stack-p) (y major-stack-p))
    (and (major-frame-scratch-isomorphic (car x) (car y))
         (if (atom (cdr x))
             (atom (cdr y))
           (and (consp (cdr y))
                (major-stack-scratch-isomorphic (cdr x) (cdr y)))))
    ///
    (defequiv major-stack-scratch-isomorphic)

    (defcong major-stack-scratch-isomorphic major-frame-scratch-isomorphic (car x) 1
      :hints(("Goal" :in-theory (enable default-car))))
    (defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic (cdr x) 1
      :hints(("Goal" :in-theory (enable default-car))))
    
    (defcong major-frame-scratch-isomorphic major-stack-scratch-isomorphic (cons x y) 1)

    (defthm major-stack-scratch-isomorphic-cons-cdr-congruence
      (implies (major-stack-scratch-isomorphic x y)
               (major-stack-scratch-isomorphic (cons frame (cdr x))
                                               (cons frame (cdr y))))
      :rule-classes :congruence)

    (defcong major-stack-scratch-isomorphic acl2::pos-equiv (len x) 1
      :hints(("Goal" :in-theory (enable len pos-fix)))))


  (define interp-st-scratch-isomorphic (x y)
    :non-executable t
    :verify-guards nil
    (major-stack-scratch-isomorphic (interp-st->stack x) (interp-st->stack y))
    ///
    (defequiv interp-st-scratch-isomorphic)

    (defcong interp-st-scratch-isomorphic major-stack-scratch-isomorphic (interp-st->stack x) 1)

    (defcong major-stack-scratch-isomorphic interp-st-scratch-isomorphic (update-interp-st->stack stack x) 1)

    (defthm update-interp-st->stack-norm-under-interp-st-scratch-isomorphic
      (implies (syntaxp (not (equal x ''nil)))
               (interp-st-scratch-isomorphic
                (update-interp-st->stack stack x)
                (update-interp-st->stack stack nil))))

    (defthm interp-st-scratch-isomorphic-of-update-interp-st->stack-identity
      (interp-st-scratch-isomorphic
       (update-interp-st->stack (major-stack-fix (interp-st->stack interp-st)) x)
       interp-st))

    (defthm interp-st-scratch-isomorphic-of-update-interp-st->stack-identity2
      (interp-st-scratch-isomorphic
       (update-interp-st->stack (interp-st->stack interp-st) x)
       interp-st))

    (def-updater-independence-thm interp-st-scratch-isomorphic-identity
      (implies (major-stack-equiv (interp-st->stack new) (interp-st->stack old))
               (equal (interp-st-scratch-isomorphic new x)
                      (interp-st-scratch-isomorphic old x)))))
  

  (defcong major-stack-scratch-isomorphic
    major-stack-scratch-isomorphic (stack$a-pop-scratch stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defcong major-stack-scratch-isomorphic
    major-stack-scratch-isomorphic (stack$a-pop-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-frame))))

  (defcong major-stack-scratch-isomorphic
    major-stack-scratch-isomorphic (stack$a-pop-minor-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame))))

  (defcong major-stack-scratch-isomorphic
    major-stack-scratch-isomorphic (stack$a-set-bindings bindings stack) 2
    :hints(("Goal" :in-theory (enable stack$a-set-bindings))))

  (defcong scratchlist-isomorphic scratchlist-isomorphic (update-nth n obj x) 3
    :hints(("Goal" :in-theory (enable update-nth))))

  (defcong major-stack-scratch-isomorphic
    major-stack-scratch-isomorphic (stack$a-update-scratch n obj stack) 3
    :hints(("Goal" :in-theory (enable stack$a-update-scratch))))

  (defthm stack$a-pop-scratch-of-stack$a-push-scratch
    (equal (stack$a-pop-scratch (stack$a-push-scratch obj stack))
           (major-stack-fix stack))
    :hints(("Goal" :in-theory (enable stack$a-push-scratch stack$a-pop-scratch default-car)
            :expand ((major-stack-fix stack)))))


  (defthm stack$a-pop-frame-of-stack$a-set-bindings
    (equal (stack$a-pop-frame (stack$a-set-bindings bindings stack))
           (stack$a-pop-frame stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-bindings))))

  (defthm stack$a-pop-frame-of-stack$a-set-debug
    (equal (stack$a-pop-frame (stack$a-set-debug obj stack))
           (stack$a-pop-frame stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-set-debug))))

  (defthm stack$a-pop-frame-of-stack$a-push-frame
    (equal (stack$a-pop-frame (stack$a-push-frame stack))
           (major-stack-fix stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-frame stack$a-push-frame))))

  (defthm stack$a-pop-minor-frame-of-stack$a-set-minor-bindings
    (equal (stack$a-pop-minor-frame (stack$a-set-minor-bindings bindings stack))
           (stack$a-pop-minor-frame stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-set-minor-bindings))))

  (defthm stack$a-pop-minor-frame-of-stack$a-set-minor-debug
    (equal (stack$a-pop-minor-frame (stack$a-set-minor-debug obj stack))
           (stack$a-pop-minor-frame stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-set-minor-debug))))

  (defthm stack$a-pop-minor-frame-of-stack$a-push-minor-frame
    (equal (stack$a-pop-minor-frame (stack$a-push-minor-frame stack))
           (major-stack-fix stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame stack$a-push-minor-frame
                                      major-stack-fix default-car))))


  (defthm major-stack-scratch-isomorphic-of-add-binding
    (major-stack-scratch-isomorphic (stack$a-add-binding var val stack) stack)
    :hints(("Goal" :in-theory (enable stack$a-add-binding major-stack-scratch-isomorphic
                                      major-frame-scratch-isomorphic))))

  (defthm major-stack-scratch-isomorphic-of-set-bindings
    (major-stack-scratch-isomorphic (stack$a-set-bindings bindings stack) stack)
    :hints(("Goal" :in-theory (enable stack$a-set-bindings major-stack-scratch-isomorphic
                                      major-frame-scratch-isomorphic))))

  (defthm major-stack-scratch-isomorphic-of-add-minor-bindings
    (major-stack-scratch-isomorphic (stack$a-add-minor-bindings bindings stack) stack)
    :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings
                                      major-stack-scratch-isomorphic
                                      major-frame-scratch-isomorphic
                                      minor-stack-scratch-isomorphic
                                      minor-frame-scratch-isomorphic))))

  (defret major-stack-scratch-isomorphic-of-syntax-bind
    (interp-st-scratch-isomorphic new-interp-st interp-st)
    :hints(("Goal" :in-theory (enable gl-interp-syntax-bind)))
    :fn gl-interp-syntax-bind)

  (defret major-stack-scratch-isomorphic-of-relieve-hyp-synp
    (interp-st-scratch-isomorphic new-interp-st
      interp-st)
    :hints(("Goal" :in-theory (enable gl-rewrite-relieve-hyp-synp)))
    :fn gl-rewrite-relieve-hyp-synp)
  
  (defthm major-stack-scratch-isomorphic-of-gl-primitive-fncall
    (interp-st-scratch-isomorphic
     (mv-nth 2 (gl-primitive-fncall fn args dont interp-st state))
     interp-st)
    :hints(("Goal" :in-theory (enable gl-primitive-fncall
                                      gl-int-primitive
                                      gl-intcons-primitive
                                      gl-endint-primitive
                                      gl-intcar-primitive
                                      gl-intcdr-primitive
                                      gl-bool-primitive))))


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
        :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)
                (let ((flag (find-flag-is-hyp clause)))
                  (and flag
                       (prog2$ (cw "flag: ~x0~%" flag)
                               '(:no-op t)))))
        :mutual-recursion gl-interp))))



(local
 (defthm major-stack-bfrlist-of-atom
   (implies (atom x)
            (equal (major-stack-bfrlist x) nil))
   :hints(("Goal" :in-theory (enable major-stack-bfrlist
                                     default-car)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
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
           :do-not-induct t))))

(local
 (defthm scratchlist-bfrlist-of-update-nth
   (implies (and (not (member v (scratchobj->bfrlist obj)))
                 (not (member v (scratchlist-bfrlist x))))
            (not (member v (scratchlist-bfrlist (update-nth n obj x)))))
   :hints(("Goal" :in-theory (enable update-nth)))))

(local
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
           :do-not-induct t))))


(local (defthm gl-objectlist-bfrlist-of-append
         (equal (gl-objectlist-bfrlist (append x y))
                (append (gl-objectlist-bfrlist x)
                        (gl-objectlist-bfrlist y)))
         :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist append)))))

(local (defthm member-nthcdr
         (implies (not (member v x))
                  (not (member v (nthcdr n x))))))



(local (defthm member-gl-objectlist-bfrlist-of-nthcdr
         (implies (not (member v (gl-objectlist-bfrlist x)))
                  (not (member v (gl-objectlist-bfrlist (nthcdr n x)))))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(local
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
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-set-bindings
   (implies (and (not (member v (major-stack-bfrlist stack)))
                 (not (member v (gl-object-alist-bfrlist bindings))))
            (not (member v (major-stack-bfrlist (stack$a-set-bindings bindings stack)))))
   :hints(("Goal" :in-theory (enable stack$a-set-bindings
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-set-minor-bindings
   (implies (and (not (member v (major-stack-bfrlist stack)))
                 (not (member v (gl-object-alist-bfrlist bindings))))
            (not (member v (major-stack-bfrlist (stack$a-set-minor-bindings bindings stack)))))
   :hints(("Goal" :in-theory (enable stack$a-set-minor-bindings
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :expand ((major-stack-bfrlist stack)
                    (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-add-minor-bindings
   (set-equiv (major-stack-bfrlist (stack$a-add-minor-bindings bindings stack))
              (append (gl-object-alist-bfrlist bindings)
                      (major-stack-bfrlist stack)))
   :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-push-frame
   (equal (major-stack-bfrlist (stack$a-push-frame stack))
          (major-stack-bfrlist stack))
   :hints(("Goal" :in-theory (enable stack$a-push-frame
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-push-minor-frame
   (equal (major-stack-bfrlist (stack$a-push-minor-frame stack))
          (major-stack-bfrlist stack))
   :hints(("Goal" :in-theory (enable stack$a-push-minor-frame
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-pop-frame
   (implies (not (member v (major-stack-bfrlist stack)))
            (not (member v (major-stack-bfrlist (stack$a-pop-frame stack)))))
   :hints(("Goal" :in-theory (enable stack$a-pop-frame
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist
                                     default-car)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-pop-minor-frame
   (implies (not (member v (major-stack-bfrlist stack)))
            (not (member v (major-stack-bfrlist (stack$a-pop-minor-frame stack)))))
   :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist
                                     default-car)
           :do-not-induct t))))

(local
   (defthm gl-object-alist-bfrlist-of-stack$a-bindings
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (gl-object-alist-bfrlist (stack$a-bindings stack)))))
     :hints(("Goal" :in-theory (enable stack$a-bindings
                                       major-frame-bfrlist)
             :expand ((major-stack-bfrlist stack))
             :do-not-induct t))))

(local
 (defthm gl-object-alist-bfrlist-of-stack$a-minor-bindings
   (implies (not (member v (major-stack-bfrlist stack)))
            (not (member v (gl-object-alist-bfrlist (stack$a-minor-bindings stack)))))
   :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-stack-bfrlist
                                     minor-frame-bfrlist)
           :expand ((major-stack-bfrlist stack)
                    (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
           :do-not-induct t))))


(local
 (defthm scratchobj->bfrlist-of-stack$a-top-scratch
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (scratchobj->bfrlist (stack$a-top-scratch stack)))))
     :hints(("Goal" :in-theory (enable stack$a-top-scratch
                                       major-frame-bfrlist
                                       minor-frame-bfrlist)
             :expand ((major-stack-bfrlist stack)
                      (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
             :do-not-induct t))))



(local
 (defthm major-stack-bfrlist-of-stack$a-set-debug
   (equal (major-stack-bfrlist (stack$a-set-debug obj stack))
          (major-stack-bfrlist stack))
   :hints(("Goal" :in-theory (enable stack$a-set-debug
                                     major-stack-bfrlist
                                     major-frame-bfrlist)))))

(local
 (defthm major-stack-bfrlist-of-stack$a-set-minor-debug
   (equal (major-stack-bfrlist (stack$a-set-minor-debug obj stack))
          (major-stack-bfrlist stack))
   :hints(("Goal" :in-theory (enable stack$a-set-minor-debug
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-stack-bfrlist
                                     minor-frame-bfrlist))))) 


(local (defthm bfr-listp-of-gl-objectlist-bfrlist-cdr
         (implies (bfr-listp (gl-objectlist-bfrlist x))
                  (bfr-listp (gl-objectlist-bfrlist (cdr x))))
         :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist)))))

(local (defthm bfr-listp-of-gl-objectlist-bfrlist-nthcdr
         (implies (bfr-listp (gl-objectlist-bfrlist x))
                  (bfr-listp (gl-objectlist-bfrlist (nthcdr n x))))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(local (defthm bfr-listp-of-gl-object-bfrlist-car
         (implies (bfr-listp (gl-objectlist-bfrlist x))
                  (bfr-listp (gl-object-bfrlist (car x))))
         :hints(("Goal" :expand ((gl-objectlist-bfrlist x))
                 :in-theory (enable default-car)))))

(local (defthm bfr-listp-of-gl-objectlist-bfrlist-take
         (implies (bfr-listp (gl-objectlist-bfrlist x))
                  (bfr-listp (gl-objectlist-bfrlist (take n x))))
         :hints(("Goal" :in-theory (enable acl2::take-redefinition)))))

(local (defthm gl-objectlist-bfrlist-of-rev
         (set-equiv (gl-objectlist-bfrlist (rev x))
                          (gl-objectlist-bfrlist x))
         :hints(("Goal" :in-theory (enable rev gl-objectlist-bfrlist)))))

(local (defthm bfr-listp-of-constraint-instancelist-bfrlist-cdr
         (implies (bfr-listp (constraint-instancelist-bfrlist x))
                  (bfr-listp (constraint-instancelist-bfrlist (cdr x))))
         :hints(("Goal" :expand ((constraint-instancelist-bfrlist x))
                 :in-theory (enable default-cdr)))))

(local (defthm bfr-listp-of-constraint-instancelist-bfrlist-car
         (implies (bfr-listp (constraint-instancelist-bfrlist x))
                  (bfr-listp (constraint-instance-bfrlist (car x))))
         :hints(("Goal" :expand ((constraint-instancelist-bfrlist x))
                 :in-theory (enable default-car)))))

(local (defthm gl-object-alist-bfrlist-of-constraint-instance->subst
         (equal (gl-object-alist-bfrlist (constraint-instance->subst x))
                (constraint-instance-bfrlist x))
         :hints(("Goal" :expand ((constraint-instance-bfrlist x))))))

(local (defthm bfr-p-car-of-bfr-list
         (implies (bfr-listp x)
                  (bfr-p (car x)))
         :hints(("Goal" :in-theory (enable default-car bfr-listp)))))


;; (local (in-theory (disable bfr-listp-of-gl-objectlist-bfrlist
;;                            bfr-listp-of-gl-object-bfrlist)))

(defthm update-interp-st->stack-of-update-interp-st->stack
  (equal (update-interp-st->stack x (update-interp-st->stack x1 interp-st))
         (update-interp-st->stack x interp-st))
  :hints(("Goal" :in-theory (enable update-interp-st->stack))))

(local (in-theory (enable bfr-listp-when-not-member-witness)))

(defthm bfr-p-of-g-boolean->bool-when-bfr-listp
  (implies (and (gl-object-case x :g-boolean)
                (bfr-listp (gl-object-bfrlist x)))
           (b* (((g-boolean x)))
             (bfr-p x.bool)))
  :hints(("Goal" :in-theory (enable gl-object-bfrlist))))

(defthm bfr-p-of-bool-fix
  (bfr-p (bool-fix x))
  :hints(("Goal" :in-theory (enable bfr-p aig-p acl2::ubddp ubddp max-depth))))


(local (in-theory (disable member-equal)))



(encapsulate nil
  (local (defthm pseudo-var-listp-when-nonnil-symbol-listp
           (implies (and (symbol-listp x)
                         (not (member nil x)))
                    (pseudo-var-list-p x))
           :hints(("Goal" :in-theory (enable member)))))
  
  (defthm pseudo-var-listp-of-fn-get-def-formals
    (pseudo-var-list-p (mv-nth 1 (acl2::fn-get-def fn state)))
    :hints(("Goal" :in-theory (enable acl2::fn-get-def)))))

(defthm gl-object-alist-bfrlist-of-pairlis$
  (implies (and (pseudo-var-list-p vars)
                (equal (len vars) (len vals)))
           (equal (gl-object-alist-bfrlist (pairlis$ vars vals))
                  (gl-objectlist-bfrlist vals)))
  :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist gl-object-alist-bfrlist pairlis$
                                    pseudo-var-list-p len))))


(defcong major-stack-scratch-isomorphic
  scratchobj-isomorphic
  (stack$a-top-scratch stack) 1
  :hints(("Goal" :in-theory (enable stack$a-top-scratch))))

(defthm stack$a-top-scratch-of-stack$a-push-scratch
  (equal (stack$a-top-scratch (stack$a-push-scratch obj stack))
         (scratchobj-fix obj))
  :hints(("Goal" :in-theory (enable stack$a-push-scratch stack$a-top-scratch))))

(local (defthm bfr-p-of-scratchobj-bfr->val
         (implies (double-rewrite (scratchobj-case x :bfr))
                  (equal (bfr-p (scratchobj-bfr->val x))
                         (bfr-listp (scratchobj->bfrlist x))))
         :hints(("Goal" :in-theory (enable scratchobj->bfrlist)))))


(local
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
                                   :bfr (acl2::remove-assoc :bfrlist *scratchobj-types*))))))))




(defcong interp-st-scratch-isomorphic interp-st-scratch-isomorphic
  (update-interp-st->reclimit reclimit interp-st) 2
  :hints(("Goal" :in-theory (enable interp-st-scratch-isomorphic))))

(Defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic
  (stack$a-push-scratch obj stack) 2
  :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

(Defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic
  (stack$a-pop-scratch stack) 1
  :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

(defthm major-stack-scratch-isomorphic-of-gl-primitive-fncall-double
    (interp-st-scratch-isomorphic
     (mv-nth 2 (gl-primitive-fncall fn args dont interp-st state))
     (Double-rewrite interp-st))
    :hints(("Goal" :in-theory (enable gl-primitive-fncall
                                      gl-int-primitive
                                      gl-intcons-primitive
                                      gl-endint-primitive
                                      gl-intcar-primitive
                                      gl-intcdr-primitive
                                      gl-bool-primitive))))

(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (std::defret-mutual len-of-gl-interp-arglist
    (defret len-of-gl-interp-arglist
      (equal (len arg-objs) (len args))
      :fn gl-interp-arglist)
    :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
    :mutual-recursion gl-interp
    :skip-others t))

(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (std::defret-mutual true-listp-of-gl-interp-arglist
    (defret true-listp-of-gl-interp-arglist
      (true-listp arg-objs)
      :fn gl-interp-arglist
      :rule-classes :type-prescription)
    :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
    :mutual-recursion gl-interp
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


(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate interp-st-bfrs-ok-of-<fn>
      :formal-hyps
      (((interp-st-bfr-p x)           (lbfr-p x (interp-st->logicman interp-st)))
       ((gl-object-p x)               (lbfr-listp (gl-object-bfrlist x) (interp-st->logicman interp-st)))
       ((gl-objectlist-p x)           (lbfr-listp (gl-objectlist-bfrlist x) (interp-st->logicman interp-st)))
       (interp-st                     (interp-st-bfrs-ok interp-st))
       ((constraint-instancelist-p x) (lbfr-listp (constraint-instancelist-bfrlist x) (interp-st->logicman interp-st))))
      :return-concls
      ((xbfr                        (lbfr-p xbfr (interp-st->logicman new-interp-st)))
       ((gl-object-p x)             (lbfr-listp (gl-object-bfrlist x) (interp-st->logicman new-interp-st)))
       ((gl-objectlist-p x)         (lbfr-listp (gl-objectlist-bfrlist x) (interp-st->logicman new-interp-st)))
       (new-interp-st               (interp-st-bfrs-ok new-interp-st)))
      :rules
      (;; (t (:add-keyword :hints ('(:do-not-induct t)
       ;;                          (let ((flag (find-flag-is-hyp clause)))
       ;;                            (and flag
       ;;                                 (prog2$ (cw "flag: ~x0~%" flag)
       ;;                                         '(:no-op t)))))))
       ((:fnname gl-rewrite-try-rules)
        (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)
              `(:do-not-induct t
                ;; :clause-processor (cmr::resolve-flags-cp clause
                ;;                                         (cons 'acl2::flag
                ;;                                               ',(acl2::fgetprop 'gl-interp-test 'recursivep nil (w state))))
                )
              (let ((flag (find-flag-is-hyp clause)))
                (and flag
                     (prog2$ (cw "flag: ~x0~%" flag)
                             '(:no-op t)))))
      :mutual-recursion gl-interp
      ;; :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
      )))


;; Giant hack to get enough lemmas that we don't have to rely on (slow)
;; bfr-listp-when-not-member-witness reasoning.  Not at all sure this is worth anything.
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
  ;; (local (defstub dummy-concl () t))
  (local
   (make-event
    '(:or
      (with-output
        :off (event prove)
        :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
        (std::defret-mutual-generate interp-st-bfrs-ok-of-<fn>
          :formal-hyps
          (((interp-st-bfr-p x)           (hyp-marker (lbfr-p x (interp-st->logicman interp-st))))
           ((gl-object-p x)               (hyp-marker (lbfr-listp (gl-object-bfrlist x) (interp-st->logicman interp-st))))
           ((gl-objectlist-p x)           (hyp-marker (lbfr-listp (gl-objectlist-bfrlist x) (interp-st->logicman interp-st))))
           (interp-st                     (hyp-marker (interp-st-bfrs-ok interp-st)))
           ((constraint-instancelist-p x) (hyp-marker (lbfr-listp (constraint-instancelist-bfrlist x) (interp-st->logicman interp-st)))))
          
          :rules
          ((t (:add-concl (equal (w new-state) (w state))))
           ;; (t (:add-keyword :hints ('(:do-not-induct t)
           ;;                          (let ((flag (find-flag-is-hyp clause)))
           ;;                            (and flag
           ;;                                 (prog2$ (cw "flag: ~x0~%" flag)
           ;;                                         '(:no-op t)))))))
           ((:fnname gl-rewrite-try-rules)
            (:add-hyp (hyp-marker (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))))
          
          :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)
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
          :mutual-recursion gl-interp
          ;; :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
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
         (name-and-record-thms (@ interp-st-bfrs-ok-lemma-thm-clauses) 0 (w state)))))





;; (define logicman-pathcond-eval! (env pathcond &optional (logicman 'logicman))
;;   (declare (Xargs :non-executable t))
;;   :no-function t
;;   :verify-guards nil
;;   (prog2$ (acl2::throw-nonexec-error 'logicman-pathcond-eval!-fn (list env pathcond logicman))
;;           (logicman-pathcond-eval env (update-nth *pathcond-enabledp* t (pathcond-fix pathcond)) logicman))
;;   ///
;;   (local (defthm update-nth-of-update-nth
;;            (equal (update-nth n a (update-nth n b x))
;;                   (update-nth n a x))
;;            :hints(("Goal" :in-theory (enable update-nth)))))

;;   (defthm logicman-pathcond-eval!-of-update-pathcond-enabledp
;;     (equal (logicman-pathcond-eval! env (update-nth *pathcond-enabledp* v pathcond) logicman)
;;            (logicman-pathcond-eval! env pathcond logicman))
;;     :hints(("Goal" :in-theory (enable pathcond-fix))))

;;   (defthm logicman-pathcond-eval!-of-logicman-extension
;;     (implies (and (bind-logicman-extension new old)
;;                   (logicman-pathcond-p pathcond old))
;;              (equal (logicman-pathcond-eval! env pathcond new)
;;                     (logicman-pathcond-eval! env pathcond old))))

;;   (def-updater-independence-thm logicman-pathcond-eval!-of-interp-st-logicman-extension
;;     (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
;;                   (logicman-pathcond-p pathcond (interp-st->logicman old)))
;;              (equal (logicman-pathcond-eval! env pathcond (interp-st->logicman new))
;;                     (logicman-pathcond-eval! env pathcond (interp-st->logicman old)))))

;;   ;; (defthm logicman-pathcond-eval!-of-logicman-pathcond-assume
;;   ;;   (implies (not contradictionp)
;;   ;;            (equal (logicman-pathcond-eval! env new-pathcond)
;;   ;;                   (and (logicman-pathcond-eval! env pathcond)
;;   ;;                        (or (not (pathcond-enabledp pathcond))
;;   ;;                            (bfr-eval x env))))))
;;   )


(define gl-interp-real-errorp (err)
  (and err (not (eq err :unreachable))))

(defthm pathcond-enabledp-of-pathcond-rewind
  (iff (nth *pathcond-enabledp* (pathcond-rewind mode pathcond))
       (nth *pathcond-enabledp* pathcond))
  :hints(("Goal" :in-theory (e/d (pathcond-rewind) (nth-add1 nth update-nth)))))

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
      :rules ((t (:add-concl ;; (implies t ;; (not (gl-interp-real-errorp err))
                                      (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
                                            (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t :expand :lambdas)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '( :expand :lambdas))))))))
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)))))


(define maybe-cons (do-it val lst)
  :verify-guards nil
  (if do-it (cons val lst) lst)
  ///
  (defcong iff equal (maybe-cons do-it val lst) 1))

(define maybe-cdr (do-it lst)
  :verify-guards nil
  (if do-it (cdr lst) lst)
  ///
  (defcong iff equal (maybe-cdr do-it lst) 1)
  (defthm maybe-cdr-of-maybe-cons
    (equal (maybe-cdr do-it (maybe-cons do-it val lst))
           lst)
    :hints(("Goal" :in-theory (enable maybe-cons)))))

(define maybe-incr (do-it x)
  :verify-guards nil
  (if do-it (+ 1 (nfix x)) (nfix x))
  ///
  (defcong iff equal (maybe-incr do-it x) 1))

(define maybe-decr (do-it x)
  :verify-guards nil
  (if do-it (nfix (+ -1 (nfix x))) (nfix x))
  ///
  (defcong iff equal (maybe-decr do-it x) 1)

  (defthm maybe-decr-of-maybe-incr
    (equal (maybe-decr do-it (maybe-incr do-it x))
           (nfix x))
    :hints(("Goal" :in-theory (enable maybe-incr)))))



(define logicman-pathcond-eval-checkpoints (env pathcond logicman)
  :non-executable t
  :no-function t
  :verify-guards nil
  :measure (pathcond-rewind-stack-len (lbfr-mode) pathcond)
  (if (or (zp (pathcond-rewind-stack-len (lbfr-mode) pathcond))
          (not (pathcond-enabledp pathcond)))
      nil
    (b* ((pathcond (pathcond-rewind (lbfr-mode) pathcond))
         (eval (logicman-pathcond-eval env pathcond logicman)))
      (cons eval (logicman-pathcond-eval-checkpoints env pathcond logicman))))
  ///
  (deffixequiv logicman-pathcond-eval-checkpoints)

  (defthm logicman-pathcond-eval-checkpoints-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (equal (logicman-pathcond-eval-checkpoints env pathcond new)
                    (logicman-pathcond-eval-checkpoints env pathcond old))))

  (def-updater-independence-thm logicman-pathcond-eval-checkpoints-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (logicman-pathcond-p pathcond (interp-st->logicman old)))
             (equal (logicman-pathcond-eval-checkpoints env pathcond (interp-st->logicman new))
                    (logicman-pathcond-eval-checkpoints env pathcond (interp-st->logicman old)))))

  (defret logicman-pathcond-eval-checkpoints-of-logicman-pathcond-assume
    (implies (and (not contradictionp)
                  (equal (logicman->mode logicman) (logicman->mode logicman1)))
             (equal (logicman-pathcond-eval-checkpoints env new-pathcond logicman1)
                    (maybe-cons (nth *pathcond-enabledp* pathcond)
                                (logicman-pathcond-eval env pathcond logicman1)
                                (logicman-pathcond-eval-checkpoints env pathcond logicman1))))
    :hints(("Goal" :in-theory (enable maybe-cons)))
    :fn logicman-pathcond-assume)

  (defret logicman-pathcond-eval-checkpoints-of-pathcond-rewind
    (implies (equal bfr-mode (lbfr-mode))
             (equal (logicman-pathcond-eval-checkpoints env new-pathcond logicman)
                    (maybe-cdr (nth *pathcond-enabledp* pathcond)
                               (logicman-pathcond-eval-checkpoints env pathcond logicman))))
    :hints(("Goal" :in-theory (enable maybe-cdr)
            :expand ((logicman-pathcond-eval-checkpoints env pathcond logicman)
                     (logicman-pathcond-eval-checkpoints env (pathcond-rewind (lbfr-mode) pathcond) logicman))))
    :fn pathcond-rewind)

  (defthm len-of-logicman-pathcond-eval-checkpoints
    (implies (nth *pathcond-enabledp* pathcond)
             (equal (len (logicman-pathcond-eval-checkpoints env pathcond logicman))
                    (pathcond-rewind-stack-len (lbfr-mode) pathcond)))))


(define logicman-pathcond-eval-checkpoints! (env pathcond logicman)
  :non-executable t
  :no-function t
  :verify-guards nil
  (b* ((pathcond (update-nth *pathcond-enabledp* t pathcond)))
    (cons (logicman-pathcond-eval env pathcond logicman)
          (logicman-pathcond-eval-checkpoints env pathcond logicman)))
  ///
  (deffixequiv logicman-pathcond-eval-checkpoints)

  (defthm update-pathcond-enabledp-under-pathcond-equiv
    (implies (iff* enabledp (pathcond-enabledp pathcond))
             (pathcond-equiv (update-nth *pathcond-enabledp* enabledp pathcond)
                             pathcond))
    :hints(("Goal" :in-theory (enable pathcond-fix))))

  (fty::deffixcong pathcond-equiv pathcond-equiv (update-nth n v x) x
    :hints(("Goal" :in-theory (enable pathcond-fix))))

  ;; (local (defthm logicman-pathcond-eval-checkpoints-of-update-pathcond-enabledp
  ;;          (implies (nth *pathcond-enabledp* pathcond)
  ;;                   (equal (logicman-pathcond-eval-checkpoints
  ;;                           env (update-nth *pathcond-enabledp* t pathcond) logicman)
  ;;                          (logicman-pathcond-eval-checkpoints
  ;;                           env pathcond logicman)))
  ;;          :hints(("Goal" :in-theory (e/d (logicman-pathcond-eval-checkpoints)
  ;;                                         (LOGICMAN-PATHCOND-EVAL-CHECKPOINTS-OF-PATHCOND-REWIND)))
  ;;                 (and (equal id (acl2::parse-clause-id "Subgoal *1/3'10'"))
  ;;                      '(:error t)))))

  (defthm logicman-pathcond-eval-checkpoints!-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (equal (logicman-pathcond-eval-checkpoints! env pathcond new)
                    (logicman-pathcond-eval-checkpoints! env pathcond old))))

  (def-updater-independence-thm logicman-pathcond-eval-checkpoints!-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (logicman-pathcond-p pathcond (interp-st->logicman old)))
             (equal (logicman-pathcond-eval-checkpoints! env pathcond (interp-st->logicman new))
                    (logicman-pathcond-eval-checkpoints! env pathcond (interp-st->logicman old)))))

  (defret logicman-pathcond-eval-checkpoints!-of-logicman-pathcond-assume
    (implies (and (not contradictionp)
                  (equal (logicman->mode logicman) (logicman->mode logicman1)))
             (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman1)
                    (maybe-cons (nth *pathcond-enabledp* pathcond)
                                (logicman-pathcond-eval env new-pathcond logicman1)
                                (logicman-pathcond-eval-checkpoints! env pathcond logicman1))))
    :hints(("Goal" :in-theory (enable maybe-cons))
           (and stable-under-simplificationp
                '(:in-theory (enable logicman-pathcond-assume))))
    :fn logicman-pathcond-assume)

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

  (defret logicman-pathcond-eval-checkpoints!-of-pathcond-rewind
    (implies (and (equal bfr-mode (lbfr-mode))
                  (pathcond-rewind-ok bfr-mode pathcond))
             (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman)
                    (maybe-cdr (nth *pathcond-enabledp* pathcond)
                               (logicman-pathcond-eval-checkpoints! env pathcond logicman))))
    :hints(("Goal" :in-theory (enable maybe-cdr)
            :expand ((logicman-pathcond-eval-checkpoints env pathcond logicman)))
           (and stable-under-simplificationp
                '(:in-theory (enable pathcond-rewind pathcond-rewind-ok)))
           )
    :fn pathcond-rewind)

  (local (defthm update-nth-of-update-nth
           (equal (update-nth n a (update-nth n b x))
                  (update-nth n a x))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defthm logicman-pathcond-eval-checkpoints!-of-update-pathcond-enabledp
    (equal (logicman-pathcond-eval-checkpoints! env (update-nth *pathcond-enabledp* v pathcond) logicman)
           (logicman-pathcond-eval-checkpoints! env pathcond logicman)))

  (defthm pathcond-rewind-stack-len-of-update-pathcond-enabledp
    (equal (pathcond-rewind-stack-len mode (update-nth *pathcond-enabledp* v pathcond))
           (pathcond-rewind-stack-len mode pathcond))
    :hints(("Goal" :in-theory (enable pathcond-rewind-stack-len))))

  (defthm len-of-logicman-pathcond-eval-checkpoints!
    (equal (len (logicman-pathcond-eval-checkpoints! env pathcond logicman))
           (+ 1 (pathcond-rewind-stack-len (lbfr-mode) pathcond)))))





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
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)))))



(defthm pathcond-rewind-stack-len-of-pathcond-rewind
  (equal (pathcond-rewind-stack-len mode (pathcond-rewind mode pathcond))
         (maybe-decr (nth *pathcond-enabledp* pathcond)
                     (pathcond-rewind-stack-len mode pathcond)))
  :hints(("Goal" :in-theory (enable maybe-decr pos-fix nfix))
         (and stable-under-simplificationp
              '(:in-theory (enable pathcond-rewind)))))

(defret pathcond-rewind-stack-len-of-logicman-pathcond-assume-maybe
  (implies (and (equal mode (logicman->mode logicman))
                (not contradictionp))
           (equal (pathcond-rewind-stack-len mode new-pathcond)
                  (maybe-incr (nth *pathcond-enabledp* pathcond)
                              (pathcond-rewind-stack-len mode pathcond))))
  :hints(("Goal" :in-theory (enable maybe-incr pos-fix nfix))
         (and stable-under-simplificationp
              '(:in-theory (enable logicman-pathcond-assume))))
  :fn logicman-pathcond-assume)

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
      :rules ((t (:add-concl (implies (and ;; (not (gl-interp-real-errorp err))
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
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)))))


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
      :no-induction-hint t)))



(local (defret pathcond-rewind-ok-of-interp-st-pathcond-assume
         (implies (and (not contra)
                       (equal bfr-mode (logicman->mode (interp-st->logicman interp-st))))
                  (pathcond-rewind-ok bfr-mode (interp-st->pathcond new-interp-st)))
         :hints(("Goal" :in-theory (enable interp-st-pathcond-assume pathcond-rewind-ok
                                           maybe-incr)))
         :fn interp-st-pathcond-assume))

(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (gl-interp-real-errorp err))
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
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)))))

(defsection pathcond-eval-preserved

  (local
   (defthm pathcond-eval-equal-when-eval-checkpoints!-equal
     (implies (and (equal evals (logicman-pathcond-eval-checkpoints! env pathcond logicman))
                   (bind-free (case-match evals
                                (('logicman-pathcond-eval-checkpoints! prev-env prev-pathcond prev-logicman)
                                 (and (equal prev-env env)
                                      (not (equal pathcond prev-pathcond))
                                      `((prev-pathcond . ,prev-pathcond)
                                        (prev-logicman . ,prev-logicman))))
                                (& nil)))
                   (equal evals (logicman-pathcond-eval-checkpoints! env prev-pathcond prev-logicman))
                   (iff* (pathcond-enabledp pathcond) (pathcond-enabledp prev-pathcond)))
              (equal (logicman-pathcond-eval env pathcond logicman)
                     (logicman-pathcond-eval env prev-pathcond prev-logicman)))
     :hints (("Goal" :in-theory (enable logicman-pathcond-eval-checkpoints! iff*)))))
     
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond-eval
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (gl-interp-real-errorp err))
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
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      :hints (("goal" :do-not-induct t))
      :no-induction-hint t)))

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

  (local (in-theory (disable not acl2::member-of-cons)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-constraint-eval-tightens
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (gl-interp-real-errorp err))
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
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))))

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
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl ;;(implies (not (gl-interp-real-errorp err))
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
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st)))
                           :gl-objlist))))
      :hints (("goal" :do-not-induct t :expand ((:free (x) (hide x)))
               :in-theory (enable iff* and*)))
      :no-induction-hint t)))



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
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)))))

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
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)))))


;; (local (defthmd redundant-update-nth
;;          (implies (< (nfix n) (len x))
;;                   (equal (update-nth n (nth n x) x)
;;                          x))
;;          :hints(("Goal" :in-theory (enable update-nth nth len)))))

;; (local (defthm interp-st-redundant-update-reclimit
;;          (implies (and (interp-stp interp-st)
;;                        (equal reclimit (double-rewrite (ifix (interp-st->reclimit interp-st)))))
;;                   (equal (update-interp-st->reclimit reclimit interp-st)
;;                          interp-st))
;;          :hints(("Goal" :in-theory (e/d (update-interp-st->reclimit interp-st->reclimit
;;                                            interp-stp
;;                                            redundant-update-nth)
;;                                         (equal-len-hyp))))))

(local (defthm alistp-when-gl-object-alist-p-rw
         (implies (gl-object-alist-p x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable gl-object-alist-p)))))


(local (Defthm stack$a-scratch-len-of-set-minor-debug
         (equal (stack$a-scratch-len (stack$a-set-minor-debug obj stack))
                (stack$a-scratch-len stack))
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-set-minor-debug)))))

(local (Defthm stack$a-scratch-len-of-set-minor-bindings
         (equal (stack$a-scratch-len (stack$a-set-minor-bindings obj stack))
                (stack$a-scratch-len stack))
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-set-minor-bindings)))))

(local (Defthm stack$a-scratch-len-of-push-minor-frame
         (equal (stack$a-scratch-len (stack$a-push-minor-frame stack))
                0)
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-push-minor-frame)))))

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

(local (Defthm stack$a-minor-frames-of-set-minor-debug
         (equal (stack$a-minor-frames (stack$a-set-minor-debug obj stack))
                (stack$a-minor-frames stack))
         :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                           stack$a-set-minor-debug
                                           len)))))

(local (Defthm stack$a-minor-frames-of-set-minor-bindings
         (equal (stack$a-minor-frames (stack$a-set-minor-bindings obj stack))
                (stack$a-minor-frames stack))
         :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                           stack$a-set-minor-bindings
                                           len)))))

(local (Defthm stack$a-minor-frames-of-push-minor-frame
         (equal (stack$a-minor-frames (stack$a-push-minor-frame stack))
                (+ 1 (stack$a-minor-frames stack)))
         :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                           stack$a-push-minor-frame)))))

(defthm posp-of-stack$a-minor-frames
  (posp (stack$a-minor-frames stack$c))
  :hints(("Goal" :in-theory (enable stack$a-minor-frames)))
  :rule-classes :type-prescription)

(defthm posp-of-stack$a-frames
  (posp (stack$a-frames stack$c))
  :hints(("Goal" :in-theory (enable stack$a-frames)))
  :rule-classes :type-prescription)


(local (defthm pathcond-rewind-ok-by-stack-len
         (implies (and (equal stack-len (pathcond-rewind-stack-len bfr-mode pathcond))
                       (bind-free (case-match stack-len
                                    (('maybe-incr cond x) `((cond . ,cond) (x . ,x)))))
                       (equal stack-len (maybe-incr cond x))
                       (iff* cond (nth *pathcond-enabledp* pathcond)))
                  (pathcond-rewind-ok bfr-mode pathcond))
         :hints(("Goal" :in-theory (enable pathcond-rewind-ok maybe-incr)))))

(defthm gl-object-alist-p-of-pairlis$
  (implies (and (gl-objectlist-p vals)
                (pseudo-var-list-p vars)
                (equal (len vars) (len vals)))
           (gl-object-alist-p (pairlis$ vars vals)))
  :hints(("Goal" :in-theory (enable pairlis$ gl-object-alist-p))))



(local (Defthm stack$a-scratch-len-of-push-scratch
         (equal (stack$a-scratch-len (stack$a-push-scratch obj stack))
                (+ 1 (stack$a-scratch-len stack)))
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-push-scratch)))))

(local (Defthm stack$a-scratch-len-of-pop-scratch
         (equal (stack$a-scratch-len (stack$a-pop-scratch stack))
                (nfix (+ -1 (stack$a-scratch-len stack))))
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-pop-scratch len)))))

(local (Defthm stack$a-scratch-len-of-update-scratch
         (implies (< (nfix n) (stack$a-scratch-len stack))
                  (equal (stack$a-scratch-len (stack$a-update-scratch n obj stack))
                         (stack$a-scratch-len stack)))
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-update-scratch len)))))

(local (Defthm stack$a-frames-of-push-frame
         (equal (stack$a-frames (stack$a-push-frame stack))
                (+ 1 (stack$a-frames stack)))
         :hints(("Goal" :in-theory (enable stack$a-frames
                                           stack$a-push-frame)))))

(local (Defthm stack$a-minor-frames-of-push-frame
         (equal (stack$a-minor-frames (stack$a-push-frame stack))
                1)
         :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                           stack$a-push-frame)))))

(local (Defthm stack$a-minor-frames-of-set-debug
         (equal (stack$a-minor-frames (stack$a-set-debug obj stack))
                (stack$a-minor-frames stack))
         :hints(("Goal" :in-theory (enable stack$a-minor-frames
                                           stack$a-set-debug)))))

(local (Defthm stack$a-frames-of-set-debug
         (equal (stack$a-frames (stack$a-set-debug obj stack))
                (stack$a-frames stack))
         :hints(("Goal" :in-theory (enable stack$a-frames
                                           stack$a-set-debug len)))))

(local (Defthm stack$a-scratch-len-of-set-debug
         (equal (stack$a-scratch-len (stack$a-set-debug obj stack))
                (stack$a-scratch-len stack))
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-set-debug)))))

(local (Defthm stack$a-scratch-len-of-push-frame
         (equal (stack$a-scratch-len (stack$a-push-frame stack))
                0)
         :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                           stack$a-push-frame)))))

(defcong scratchobj-isomorphic major-stack-scratch-isomorphic (stack$a-push-scratch obj stack) 1
  :hints(("Goal" :in-theory (enable stack$a-push-scratch))))





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
      :rules (((not (or (:fnname gl-interp-bindinglist)
                        (:fnname gl-interp-add-constraints)
                        (:fnname gl-interp-add-constraints-for-substs)))
               (:add-concl (equal (list . <values>)
                                  <call>))))
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)
              (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))


(defsection gl-interp-term-guards
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
   (defthm len-gl-objlist-when-scratchobj-isomorphic-rw
     (implies (and (scratchobj-isomorphic y (double-rewrite x))
                   (syntaxp (not (equal y x)))
                   (scratchobj-case y :gl-objlist))
              (equal (len (scratchobj-gl-objlist->val x))
                     (len (scratchobj-gl-objlist->val y))))))


  (local (defthm eqlablep-of-rewrite-rule->equiv
           (implies (pseudo-rewrite-rule-p rule)
                    (eqlablep (acl2::rewrite-rule->equiv rule)))
           :hints(("Goal" :in-theory (enable pseudo-rewrite-rule-p)))))
  
  ;; ugh
  (local (defthm booleanp-of-interp-st-pathcond-enabledp
           (implies (interp-stp interp-st)
                    (booleanp (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))
           :hints(("Goal" :in-theory (enable interp-stp pathcondp interp-st->pathcond)))
           :rule-classes :type-prescription))
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (verify-guards gl-interp-term
      :guard-debug t)))







;; (fty::defmap eval-env :key-type pseudo-var :true-listp t)

;; (fty::defprod ev-constraint-instance
;;   ((thmname symbolp)
;;    (subst eval-env-p))
;;   :layout :tree)

;; (fty::deflist ev-constraint-instancelist :elt-type ev-constraint-instance :true-listp t)

;; (local
;;  (progn
;;    (include-book "scratchobj")
;;    (defconst *ev-scratchobj-type-mapping*
;;      '((:gl-obj . t)
;;        (:gl-objlist . true-listp)
;;        (:bfr . booleanp)
;;        (:bfrlist . boolean-listp)
;;        (:cinst . ev-constraint-instance-p)
;;        (:cinstlist . ev-constraint-instancelist-p)))
;;    (defun scratchobj-tmplsubst-add-evtypes (x)
;;      (declare (xargs :mode :program))
;;      (if (atom x)
;;          nil
;;        (b* (((acl2::tmplsubst x1) (car x))
;;             (kindlook (assoc :<kind> x1.atoms))
;;             ((unless kindlook) (er hard? 'scratchobj-tmplsubst-add-evtypes "failed to find :<kind>"))
;;             (kind (cdr kindlook))
;;             (evtype-look (assoc kind *ev-scratchobj-type-mapping*))
;;             ((unless evtype-look) (er hard? 'scratchobj-tmplsubst-add-evtypes "failed to find: ~x0" kind))
;;             (evtype (cdr evtype-look)))
;;          (cons (acl2::change-tmplsubst
;;                 x1 :atoms (cons `(<evtype> . ,evtype) x1.atoms))
;;                (scratchobj-tmplsubst-add-evtypes (cdr x))))))

;;    (defconst *scratchobj-evtypes-tmplsubsts*
;;      (scratchobj-tmplsubst-add-evtypes *scratchobj-tmplsubsts*))))
            
         
;; (make-event
;;  `(progn
;;     (fty::deftagsum ev-scratchobj
;;       :layout :tree
;;       . ,(acl2::template-proj '(:<kind> ((val <evtype>)))
;;                               *scratchobj-evtypes-tmplsubsts*))

;;     (defthm scratchobj-kind-p-of-ev-scratchobj-kind
;;       (scratchobj-kind-p (ev-scratchobj-kind x))
;;       :hints(("Goal" :in-theory (enable ev-scratchobj-kind))))))


;; (fty::deflist ev-scratchlist :elt-type ev-scratchobj :true-listp t)

;; (fty::defprod ev-minor-frame
;;   ((bindings eval-env-p)
;;    (scratch ev-scratchlist-p)
;;    (debug)))

;; (fty::deflist ev-minor-stack :elt-type ev-minor-frame :true-listp t :non-emptyp t
;;   ///
;;   (defthm ev-minor-stack-p-of-cons-cdr
;;     (implies (and (ev-minor-stack-p x)
;;                   (ev-minor-frame-p a))
;;              (ev-minor-stack-p (cons a (cdr x))))
;;     :hints(("Goal" :in-theory (enable ev-minor-stack-p)))))

;; (make-event
;;  `(fty::defprod ev-major-frame
;;     ((bindings eval-env-p)
;;      (debug)
;;      (minor-stack ev-minor-stack-p :default ',(list (make-ev-minor-frame))))))

;; (fty::deflist ev-major-stack :elt-type ev-major-frame :true-listp t :non-emptyp t
;;   ///
;;   (defthm ev-major-stack-p-of-cons-cdr
;;     (implies (and (ev-major-stack-p x)
;;                   (ev-major-frame-p a))
;;              (ev-major-stack-p (cons a (cdr x))))
;;     :hints(("Goal" :in-theory (enable ev-major-stack-p)))))

(define gl-object-ev ((x gl-object-p)
                      (env gl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (gl-object-bfrlist x))
  :returns (new-x gl-object-p)
  (g-concrete (fgl-object-eval x env))
  ///

  (defthm gl-object-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (gl-object-bfrlist x) old))
             (equal (gl-object-ev x env new)
                    (gl-object-ev x env old)))
    :hints(("Goal" :in-theory (enable gl-object-bfrlist))))

  (def-updater-independence-thm gl-object-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-object-bfrlist x) (interp-st->logicman old)))
             (equal (gl-object-ev x env (interp-st->logicman new))
                    (gl-object-ev x env (interp-st->logicman old))))))

(define gl-objectlist-ev ((x gl-objectlist-p)
                      (env gl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (gl-objectlist-bfrlist x))
  :returns (new-x gl-objectlist-p)
  (if (atom x)
      nil
    (cons (gl-object-ev (car x) env)
          (gl-objectlist-ev (cdr x) env)))
  ///

  (defthm gl-objectlist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (gl-objectlist-bfrlist x) old))
             (equal (gl-objectlist-ev x env new)
                    (gl-objectlist-ev x env old)))
    :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist))))

  (def-updater-independence-thm gl-objectlist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-objectlist-bfrlist x) (interp-st->logicman old)))
             (equal (gl-objectlist-ev x env (interp-st->logicman new))
                    (gl-objectlist-ev x env (interp-st->logicman old))))))




(define gl-object-alist-ev ((x gl-object-alist-p)
                                   (env gl-env-p)
                                   &optional (logicman 'logicman))
  :guard (lbfr-listp (gl-object-alist-bfrlist x))
  :guard-hints (("goal" :in-theory (enable gl-object-alist-bfrlist)))
  :returns (ans gl-object-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x)
                    (gl-object-ev (cdar x) env))
              (gl-object-alist-ev (cdr x) env))
      (gl-object-alist-ev (cdr x) env)))
  ///
  (local (in-theory (enable gl-object-alist-fix)))

  (defthm gl-object-alist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (gl-object-alist-bfrlist x) old))
             (equal (gl-object-alist-ev x env new)
                    (gl-object-alist-ev x env old)))
    :hints(("Goal" :in-theory (enable gl-object-alist-bfrlist))))

  (def-updater-independence-thm gl-object-alist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-object-alist-bfrlist x) (interp-st->logicman old)))
             (equal (gl-object-alist-ev x env (interp-st->logicman new))
                    (gl-object-alist-ev x env (interp-st->logicman old)))))

  (defret lookup-under-iff-of-gl-object-alist-ev
    (implies (pseudo-var-p k)
             (iff (hons-assoc-equal k ans)
                  (hons-assoc-equal k x))))

  (defret lookup-of-gl-object-alist-ev
    (implies (and (pseudo-var-p k)
                  (hons-assoc-equal k x))
             (equal (hons-assoc-equal k ans)
                    (cons k (gl-object-ev (cdr (hons-assoc-equal k x)) env))))))

(define constraint-instance-ev ((x constraint-instance-p)
                                       (env gl-env-p)
                                       &optional (logicman 'logicman))
  :guard (lbfr-listp (constraint-instance-bfrlist x))
  :returns (ev constraint-instance-p)
  (b* (((constraint-instance x)))
    (make-constraint-instance
     :thmname x.thmname
     :subst (gl-object-alist-ev x.subst env)))
  ///
  (defthm constraint-instance-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (constraint-instance-bfrlist x) old))
             (equal (constraint-instance-ev x env new)
                    (constraint-instance-ev x env old))))

  (def-updater-independence-thm constraint-instance-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (constraint-instance-bfrlist x) (interp-st->logicman old)))
             (equal (constraint-instance-ev x env (interp-st->logicman new))
                    (constraint-instance-ev x env (interp-st->logicman old))))))

(define constraint-instancelist-ev ((x constraint-instancelist-p)
                                           (env gl-env-p)
                                           &optional (logicman 'logicman))
  :guard (lbfr-listp (constraint-instancelist-bfrlist x))
  :returns (ev constraint-instancelist-p)
  (if (atom x)
      nil
    (cons (constraint-instance-ev (car x) env)
          (constraint-instancelist-ev (cdr x) env)))
  ///
  (defthm constraint-instancelist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (constraint-instancelist-bfrlist x) old))
             (equal (constraint-instancelist-ev x env new)
                    (constraint-instancelist-ev x env old))))

  (def-updater-independence-thm constraint-instancelist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (constraint-instancelist-bfrlist x) (interp-st->logicman old)))
             (equal (constraint-instancelist-ev x env (interp-st->logicman new))
                    (constraint-instancelist-ev x env (interp-st->logicman old))))))

(define scratchobj-ev ((x scratchobj-p)
                              (env gl-env-p)
                              &optional (logicman 'logicman))
  :guard (lbfr-listp (scratchobj->bfrlist x))
  :returns (ev scratchobj-p)
  (scratchobj-case x
    :gl-obj (scratchobj-gl-obj (gl-object-ev x.val env))
    :gl-objlist (scratchobj-gl-objlist (gl-objectlist-ev x.val env))
    :bfr (scratchobj-bfr (gobj-bfr-eval x.val env))
    :bfrlist (scratchobj-bfrlist (gobj-bfr-list-eval x.val env))
    :cinst (scratchobj-cinst (constraint-instance-ev x.val env))
    :cinstlist (scratchobj-cinstlist (constraint-instancelist-ev x.val env)))
  ///
  (defthm scratchobj-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (scratchobj->bfrlist x) old))
             (equal (scratchobj-ev x env new)
                    (scratchobj-ev x env old))))

  (def-updater-independence-thm scratchobj-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (scratchobj->bfrlist x) (interp-st->logicman old)))
             (equal (scratchobj-ev x env (interp-st->logicman new))
                    (scratchobj-ev x env (interp-st->logicman old)))))

  (defthm scratchobj-ev-of-scratchobj-gl-obj
    (equal (scratchobj-ev (Scratchobj-gl-obj val) env)
           (scratchobj-gl-obj (gl-object-ev val env))))

  (defthm scratchobj-ev-of-scratchobj-gl-objlist
    (equal (scratchobj-ev (Scratchobj-gl-objlist val) env)
           (scratchobj-gl-objlist (gl-objectlist-ev val env))))

  (defthm scratchobj-ev-of-scratchobj-bfr
    (equal (scratchobj-ev (Scratchobj-bfr val) env)
           (scratchobj-bfr (gobj-bfr-eval val env)))))

(define scratchlist-ev ((x scratchlist-p)
                        (env gl-env-p)
                        &optional (logicman 'logicman))
  :guard (lbfr-listp (scratchlist-bfrlist x))
  :returns (ev scratchlist-p)
  (if (atom x)
      nil
    (cons (scratchobj-ev (car x) env)
          (scratchlist-ev (cdr x) env)))
  ///
  (defthm scratchlist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (scratchlist-bfrlist x) old))
             (equal (scratchlist-ev x env new)
                    (scratchlist-ev x env old))))

  (def-updater-independence-thm scratchlist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (scratchlist-bfrlist x) (interp-st->logicman old)))
             (equal (scratchlist-ev x env (interp-st->logicman new))
                    (scratchlist-ev x env (interp-st->logicman old))))))

(define minor-frame-ev ((x minor-frame-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (minor-frame-bfrlist x))
  :returns (ev minor-frame-p)
  (b* (((minor-frame x)))
    (make-minor-frame
     :bindings (gl-object-alist-ev x.bindings env)
     :debug x.debug
     :scratch (scratchlist-ev x.scratch env)))
  ///
  (defthm minor-frame-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (minor-frame-bfrlist x) old))
             (equal (minor-frame-ev x env new)
                    (minor-frame-ev x env old))))

  (def-updater-independence-thm minor-frame-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (minor-frame-bfrlist x) (interp-st->logicman old)))
             (equal (minor-frame-ev x env (interp-st->logicman new))
                    (minor-frame-ev x env (interp-st->logicman old))))))

(define minor-stack-ev ((x minor-stack-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (minor-stack-bfrlist x))
  :returns (ev minor-stack-p)
  :measure (len x)
  :ruler-extenders (cons)
  (cons (minor-frame-ev (car x) env)
        (and (consp (cdr x))
             (minor-stack-ev (cdr x) env)))
  ///
  (defthm minor-stack-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (minor-stack-bfrlist x) old))
             (equal (minor-stack-ev x env new)
                    (minor-stack-ev x env old))))

  (def-updater-independence-thm minor-stack-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (minor-stack-bfrlist x) (interp-st->logicman old)))
             (equal (minor-stack-ev x env (interp-st->logicman new))
                    (minor-stack-ev x env (interp-st->logicman old))))))



(define major-frame-ev ((x major-frame-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (major-frame-bfrlist x))
  :returns (ev major-frame-p)
  (b* (((major-frame x)))
    (make-major-frame
     :bindings (gl-object-alist-ev x.bindings env)
     :debug x.debug
     :minor-stack (minor-stack-ev x.minor-stack env)))
  ///
  (defthm major-frame-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (major-frame-bfrlist x) old))
             (equal (major-frame-ev x env new)
                    (major-frame-ev x env old))))

  (def-updater-independence-thm major-frame-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (major-frame-bfrlist x) (interp-st->logicman old)))
             (equal (major-frame-ev x env (interp-st->logicman new))
                    (major-frame-ev x env (interp-st->logicman old))))))

(define major-stack-ev ((x major-stack-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (major-stack-bfrlist x))
  :returns (ev major-stack-p)
  :measure (len x)
  :ruler-extenders (cons)
  (cons (major-frame-ev (car x) env)
        (and (consp (cdr x))
             (major-stack-ev (cdr x) env)))
  ///
  (defthm major-stack-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (major-stack-bfrlist x) old))
             (equal (major-stack-ev x env new)
                    (major-stack-ev x env old))))

  (def-updater-independence-thm major-stack-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (major-stack-bfrlist x) (interp-st->logicman old)))
             (equal (major-stack-ev x env (interp-st->logicman new))
                    (major-stack-ev x env (interp-st->logicman old))))))


(defsection stack-semantics-preserved-lemmas
  (local (in-theory (enable major-stack-ev
                            minor-stack-ev
                            major-frame-ev
                            minor-frame-ev)))

  (defthm scratchlist-ev-of-cdr
    (equal (scratchlist-ev (cdr x) env)
           (cdr (scratchlist-ev x env)))
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm scratchlist-ev-of-cons
    (equal (scratchlist-ev (cons x y) env)
           (cons (scratchobj-ev x env)
                 (scratchlist-ev y env)))
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm scratchlist-ev-of-nil
    (equal (scratchlist-ev nil env) nil)
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm gl-object-alist-ev-of-nil
    (equal (gl-object-alist-ev nil env) nil)
    :hints(("Goal" :in-theory (enable gl-object-alist-ev))))

  (defthm major-stack-ev-of-stack$a-pop-scratch
    (equal (major-stack-ev (stack$a-pop-scratch stack) env)
           (stack$a-pop-scratch (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defthm major-stack-ev-of-stack$a-push-scratch
    (equal (major-stack-ev (stack$a-push-scratch obj stack) env)
           (stack$a-push-scratch
            (scratchobj-ev obj env)
            (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

  (defthm major-stack-ev-of-stack$a-pop-frame
    (equal (major-stack-ev (stack$a-pop-frame stack) env)
           (stack$a-pop-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-frame default-car))))

  (defthm major-stack-ev-of-stack$a-set-bindings
    (equal (major-stack-ev (stack$a-set-bindings bindings stack) env)
           (stack$a-set-bindings (gl-object-alist-ev bindings env)
                                 (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-bindings))))

  (defthm major-stack-ev-of-stack$a-push-frame
    (equal (major-stack-ev (stack$a-push-frame stack) env)
           (stack$a-push-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-frame))))

  (defthm major-stack-ev-of-stack$a-set-debug
    (equal (major-stack-ev (stack$a-set-debug obj stack) env)
           (stack$a-set-debug obj (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-debug))))

  (defthm gl-object-alist-ev-of-append
    (equal (gl-object-alist-ev (append a b) env)
           (append (gl-object-alist-ev a env)
                   (gl-object-alist-ev b env)))
    :hints(("Goal" :in-theory (enable gl-object-alist-ev))))

  (defthm major-stack-ev-of-stack$a-add-minor-bindings
    (equal (major-stack-ev (stack$a-add-minor-bindings bindings stack) env)
           (stack$a-add-minor-bindings
            (gl-object-alist-ev bindings env)
            (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings))))

  (defthm major-stack-ev-of-stack$a-pop-minor-frame
    (equal (major-stack-ev (stack$a-pop-minor-frame stack) env)
           (stack$a-pop-minor-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame))))

  (defthm major-stack-ev-of-stack$a-set-minor-debug
    (equal (major-stack-ev (stack$a-set-minor-debug obj stack) env)
           (stack$a-set-minor-debug obj (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-minor-debug))))

  (defthm major-stack-ev-of-stack$a-set-minor-bindings
    (equal (major-stack-ev (stack$a-set-minor-bindings bindings stack) env)
           (stack$a-set-minor-bindings
            (gl-object-alist-ev bindings env)
            (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-minor-bindings))))

  (defthm major-stack-ev-of-stack$a-push-minor-frame
    (equal (major-stack-ev (stack$a-push-minor-frame stack) env)
           (stack$a-push-minor-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-minor-frame)))))


(define stack-equiv-except-top-bindings ((x major-stack-p)
                                         (y major-stack-p))

  (b* (((major-frame x1) (car x))
       ((major-frame y1) (car y)))
    (and ;;(ec-call (gl-bindings-extension-p x1.bindings y1.bindings))
     (equal x1.debug y1.debug)
     (minor-stack-equiv x1.minor-stack y1.minor-stack)
     (if (atom (cdr x))
         (atom (cdr y))
       (and (consp (cdr y))
            (major-stack-equiv (cdr x) (cdr y))))))
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
    :hints(("Goal" :in-theory (enable stack$a-minor-frames len))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (major-stack-ev stack env logicman) 1
    :hints(("Goal" :in-theory (enable major-stack-ev major-frame-ev))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (stack$a-pop-scratch stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defcong stack-equiv-except-top-bindings
    stack-equiv-except-top-bindings
    (stack$a-pop-minor-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame))))

  (defcong stack-equiv-except-top-bindings
    equal
    (stack$a-pop-frame stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-frame
                                      major-stack-fix default-car))))

  (defret stack-equiv-except-top-bindings-of-gl-interp-syntax-bind
    (implies (equal logicman (interp-st->logicman new-interp-st))
             (stack-equiv-except-top-bindings
              (major-stack-ev
               (interp-st->stack new-interp-st)
               env logicman)
              (major-stack-ev
               (interp-st->stack interp-st)
               env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable gl-interp-syntax-bind
                                      stack$a-add-binding
                                      major-stack-ev
                                      major-frame-ev)))
    :fn gl-interp-syntax-bind)

  (defret stack-equiv-except-top-bindings-of-gl-rewrite-relieve-hyp-synp
    (implies (equal logicman (interp-st->logicman new-interp-st))
             (stack-equiv-except-top-bindings
              (major-stack-ev
               (interp-st->stack new-interp-st)
               env logicman)
              (major-stack-ev
               (interp-st->stack interp-st)
               env (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable gl-rewrite-relieve-hyp-synp
                                      stack$a-set-bindings
                                      major-stack-ev
                                      major-frame-ev)))
    :fn gl-rewrite-relieve-hyp-synp))


(define minor-stack-equiv-except-top-bindings ((x minor-stack-p)
                                               (y minor-stack-p))

  (b* (((minor-frame x1) (car x))
       ((minor-frame y1) (car y)))
    (and ;;(ec-call (gl-bindings-extension-p x1.bindings y1.bindings))
     (equal x1.debug y1.debug)
     (scratchlist-equiv x1.scratch y1.scratch)
     (if (atom (cdr x))
         (atom (cdr y))
       (and (consp (cdr y))
            (minor-stack-equiv (cdr x) (cdr y))))))
  ///
  (defequiv minor-stack-equiv-except-top-bindings))

(define stack-equiv-except-top-major/minor-bindings ((x major-stack-p)
                                                     (y major-stack-p))

  (b* (((major-frame x1) (car x))
       ((major-frame y1) (car y)))
    (and ;;(ec-call (gl-bindings-extension-p x1.bindings y1.bindings))
     (equal x1.debug y1.debug)
     (minor-stack-equiv-except-top-bindings x1.minor-stack y1.minor-stack)
     (if (atom (cdr x))
         (atom (cdr y))
       (and (consp (cdr y))
            (major-stack-equiv (cdr x) (cdr y))))))
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
    (major-stack-ev stack env logicman) 1
    :hints(("Goal" :in-theory (enable major-stack-ev major-frame-ev minor-stack-ev minor-frame-ev))))

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
  :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings))))

  (defcong stack-equiv-except-top-major/minor-bindings
    stack-equiv-except-top-bindings
    (stack$a-pop-minor-frame stack)
    1
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame
                                      stack-equiv-except-top-bindings))))

  (defrefinement stack-equiv-except-top-bindings
    stack-equiv-except-top-major/minor-bindings
    :hints(("Goal" :in-theory (enable stack-equiv-except-top-bindings)))))




(defsection gl-interp-stack-equiv-except-top-bindings
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-stack-equiv-except-top-bindings
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((not (:fnname gl-interp-bindinglist))
               (:add-concl (stack-equiv-except-top-bindings
                            (major-stack-ev (interp-st->stack new-interp-st)
                                            env
                                            (interp-st->logicman new-interp-st))
                            (major-stack-ev (interp-st->stack interp-st)
                                            env
                                            (interp-st->logicman interp-st)))))
              ((:fnname gl-interp-bindinglist)
               (:add-concl (stack-equiv-except-top-major/minor-bindings
                            (major-stack-ev (interp-st->stack new-interp-st)
                                            env
                                            (interp-st->logicman new-interp-st))
                            (major-stack-ev (interp-st->stack interp-st)
                                            env
                                            (interp-st->logicman interp-st)))))
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
      :mutual-recursion gl-interp)))

(defsection stack-bindings-extension-p
  (define gl-bindings-extension-p ((x gl-object-alist-p)
                                   (y gl-object-alist-p))
    (or (gl-object-alist-equiv x y)
        (and (consp x)
             (if (mbt (and (consp (car x))
                           (pseudo-var-p (caar x))))
                 (not (hons-assoc-equal (caar x) (cdr x)))
               t)
             (gl-bindings-extension-p (cdr x) y)))
    ///

    (deffixequiv gl-bindings-extension-p
      :hints(("Goal" :in-theory (enable gl-object-alist-fix))))

    (defthm gl-bindings-extension-p-transitive
      (implies (and (gl-bindings-extension-p x y)
                    (gl-bindings-extension-p y z))
               (gl-bindings-extension-p x z))
      :hints (("Goal" :induct (gl-bindings-extension-p x y))))

    (defthm gl-bindings-extension-p-self
      (gl-bindings-extension-p x x)
      :hints (("goal" :expand ((gl-bindings-extension-p x x))))))


  (define stack-bindings-equiv ((x major-stack-p)
                                (y major-stack-p))
    (b* (((major-frame x1) (car x))
         ((major-frame y1) (car y)))
      (gl-object-alist-equiv x1.bindings y1.bindings))
    ///
    (defequiv stack-bindings-equiv)

    (defrefinement major-stack-equiv stack-bindings-equiv)

    ;; (defthm stack-bindings-equiv-major-frame->bindings-congruence
    ;;   (implies (stack-bindings-equiv x y)
    ;;            (gl-object-alist-equiv (major-frame->bindings (car x))
    ;;                                   (major-frame->bindings (car y))))
    ;;   :rule-classes :congruence)

    (defcong stack-bindings-equiv equal (stack$a-bindings x) 1
      :hints(("Goal" :in-theory (enable stack$a-bindings))))

    (defcong gl-object-alist-equiv stack-bindings-equiv (stack$a-set-bindings bindings x) 1
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

    (def-stack-bindings-equiv-identity (stack$a-set-debug obj stack))

    (def-stack-bindings-equiv-identity (stack$a-set-minor-debug obj stack))

    (def-stack-bindings-equiv-identity (stack$a-set-minor-bindings bindings stack))

    (def-stack-bindings-equiv-identity (stack$a-add-minor-bindings bindings stack))

    (def-stack-bindings-equiv-identity (stack$a-pop-scratch stack))

    (def-stack-bindings-equiv-identity (stack$a-push-scratch obj stack))

    (def-stack-bindings-equiv-identity (stack$a-update-scratch n obj stack)))

  (define stack-bindings-extension-p ((x major-stack-p)
                                      (y major-stack-p))
    (b* (((major-frame x1) (car x))
         ((major-frame y1) (car y)))
      (gl-bindings-extension-p x1.bindings y1.bindings))
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
                                        gl-bindings-extension-p))))

    (defcong stack-bindings-equiv equal (stack-bindings-extension-p x y) 1
      :hints(("Goal" :in-theory (enable stack-bindings-equiv))))
    (defcong stack-bindings-equiv equal (stack-bindings-extension-p x y) 2
      :hints(("Goal" :in-theory (enable stack-bindings-equiv))))

    (defret stack-bindings-extension-p-of-gl-interp-syntax-bind
      (implies (equal (major-stack-ev (interp-st->stack new-interp-st) env logicman)
                      (major-stack-ev (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st)))
               (stack-bindings-extension-p
                (major-stack-ev (interp-st->stack new-interp-st) env logicman)
                (major-stack-ev (interp-st->stack interp-st) env
                                (interp-st->logicman interp-st))))
      :hints(("Goal" :in-theory (enable gl-interp-syntax-bind
                                        stack$a-add-binding
                                        stack$a-bindings
                                        major-stack-ev
                                        major-frame-ev
                                        gl-object-alist-ev
                                        gl-bindings-extension-p)))
      :fn gl-interp-syntax-bind)

    (local (Defthm gl-bindings-extension-p-of-append
             (implies (and (not (intersectp-equal (alist-keys a) (alist-keys b)))
                           (no-duplicatesp-equal (alist-keys a))
                           (equal bb b))
                      (gl-bindings-extension-p (Append a bb) b))
             :hints(("Goal" :in-theory (enable gl-bindings-extension-p append)))))

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

    (local (defthm len-of-gl-object-alist-ev
             (equal (len (gl-object-alist-ev x env))
                    (len (gl-object-alist-fix x)))
             :hints(("Goal" :in-theory (enable gl-object-alist-ev
                                               gl-object-alist-fix
                                               len)))))

    (local (defthm alist-keys-of-gl-object-alist-ev
             (equal (alist-keys (gl-object-alist-ev x env))
                    (alist-keys (gl-object-alist-fix x)))
             :hints(("Goal" :in-theory (enable gl-object-alist-ev
                                               gl-object-alist-fix
                                               alist-keys)))))

    (local (defthm gl-object-alist-p-when-gl-bfr-object-alist-p
             (implies (gl-bfr-object-alist-p x)
                      (gl-object-alist-p x))
             :hints(("Goal" :in-theory (enable gl-bfr-object-alist-p)))
             :rule-classes :forward-chaining))

    (defret stack-bindings-extension-p-of-gl-rewrite-relieve-hyp-synp
      (implies (equal (major-stack-ev (interp-st->stack new-interp-st) env logicman)
                      (major-stack-ev (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st)))
               (stack-bindings-extension-p
                (major-stack-ev (interp-st->stack new-interp-st) env
                                logicman)
                (major-stack-ev (interp-st->stack interp-st) env
                                (interp-st->logicman interp-st))))
      :hints(("Goal" :in-theory (enable gl-rewrite-relieve-hyp-synp
                                        stack$a-set-bindings
                                        stack$a-bindings
                                        major-stack-ev
                                        major-frame-ev)))
      :fn gl-rewrite-relieve-hyp-synp)

    (def-updater-independence-thm ev-interp-st-stack-bindings-extension-p-trans-rw
      (implies (and (syntaxp (not (equal old older)))
                    (stack-bindings-extension-p
                     (major-stack-ev (interp-st->stack new) env logicman)
                     (major-stack-ev (interp-st->stack old) env
                                     (interp-st->logicman old)))
                    (stack-bindings-extension-p
                     (major-stack-ev (interp-st->stack old) env
                                     (interp-st->logicman old))
                     older))
               (stack-bindings-extension-p
                (major-stack-ev (interp-st->stack new) env logicman) older))
      :hints(("Goal" :in-theory (enable stack-bindings-extension-p-transitive))))))
                        


(defsection gl-interp-stack-bindings-extension
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-stack-bindings-extended
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl (stack-bindings-extension-p
                              (major-stack-ev (interp-st->stack new-interp-st)
                                              env
                                              (interp-st->logicman new-interp-st))
                              (major-stack-ev (interp-st->stack interp-st)
                                              env
                                              (interp-st->logicman interp-st))))
                 (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t)))))))
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
      :mutual-recursion gl-interp))

  ;; (local (defthm stack-bindings-extension-p-when-equal-bindings
  ;;          (implies (and (equal (stack$a-bindings y) (stack$A-bindings z))
  ;;                        (stack-bindings-extension-p x (major-stack-ev y env)))
  ;;                   (stack-bindings-extension-p x (major-stack-ev z env)))
  ;;          :hints(("Goal" :in-theory (enable stack$a-bindings stack-bindings-extension-p
  ;;                                            major-frame-ev)
  ;;                  :expand ((major-stack-ev y env)
  ;;                           (major-stack-ev z env))))))
                    


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
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :rules ((t (:add-concl (implies (and (equal (stack$a-bindings old-stack-ev)
                                                  (stack$a-bindings (major-stack-ev
                                                                     (interp-st->stack interp-st)
                                                                     env
                                                                     (interp-st->logicman interp-st)))))
                                      (stack-bindings-extension-p
                                       (major-stack-ev (interp-st->stack new-interp-st)
                                                       env
                                                       (interp-st->logicman new-interp-st))
                                       old-stack-ev))))
                               
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))
      :no-induction-hint t
      :mutual-recursion gl-interp)))

(defsection gl-interp-preserves-equiv-contexts
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
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
      :mutual-recursion gl-interp)))


(defthm true-listp-of-fgl-ev-list
  (true-listp (fgl-ev-list x a))
  :hints (("goal" :induct (len x) :in-theory (enable len)))
  :rule-classes :type-prescription)

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


(local
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

   (fty::deffixcong alistp-equiv equal (hons-assoc-equal x a) a)))


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




(defthm fgl-object-eval-of-gl-object-ev
  (equal (fgl-object-eval (gl-object-ev x env) env2 logicman2)
         (fgl-object-eval x env))
  :hints(("Goal" :in-theory (enable gl-object-ev))))

(defthm fgl-objectlist-eval-of-gl-objectlist-ev
  (equal (fgl-objectlist-eval (gl-objectlist-ev x env) env2 logicman2)
         (fgl-objectlist-eval x env))
  :hints(("Goal" :in-theory (enable gl-objectlist-ev
                                    fgl-objectlist-eval))))

(defthm fgl-object-alist-eval-of-gl-object-ev
  (equal (fgl-object-alist-eval (gl-object-alist-ev x env) env2 logicman2)
         (fgl-object-alist-eval x env))
  :hints(("Goal" :in-theory (enable gl-object-alist-ev
                                    fgl-object-alist-eval))))

(defthm hons-assoc-equal-of-fgl-object-alist-eval-under-iff
  (iff (hons-assoc-equal k (fgl-object-alist-eval x env))
       (hons-assoc-equal k (gl-object-alist-fix x)))
  :hints(("Goal" :in-theory (enable fgl-object-alist-eval
                                    gl-object-alist-fix))))

(defsection eval-alist-extension-p
  (defmacro eval-alist-extension-p (x y)
    `(acl2::sub-alistp ,y ,x))

  (local (defthm lookup-in-gl-bindings-extension
           (implies (and (gl-bindings-extension-p x y)
                         (pseudo-var-p k)
                         (hons-assoc-equal k y))
                    (and (hons-assoc-equal k x)
                         (gl-object-equiv (cdr (hons-assoc-equal k x))
                                          (cdr (hons-assoc-equal k y)))))
           :hints(("Goal" :in-theory (enable gl-bindings-extension-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance hons-assoc-equal-of-gl-object-alist-fix)
                               (:instance hons-assoc-equal-of-gl-object-alist-fix (x y)))
                         :in-theory (disable hons-assoc-equal-of-gl-object-alist-fix))))))

  (defthm eval-alist-extension-p-of-eval-when-gl-bindings-extension-p
    (implies (gl-bindings-extension-p x y)
             (eval-alist-extension-p
              (fgl-object-alist-eval x env)
              (fgl-object-alist-eval y env)))
    :hints(("Goal" :use ((:instance acl2::sub-alistp-when-witness
                          (a (fgl-object-alist-eval y env)) (b (fgl-object-alist-eval x env)))))))

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


;; (define eval-alist-extension-p ((x alistp)
;;                                 (y alistp))
;;   (or (equal (mbe :logic (acl2::alist-fix x) :exec x)
;;              (mbe :logic (acl2::alist-fix y) :exec y))
;;       (and (consp x)
;;            (if (mbt (consp (car x)))
;;                (and (not (hons-assoc-equal (caar x) (cdr x)))
;;                     (eval-alist-extension-p (cdr x) y))
;;              (eval-alist-extension-p (cdr x) y))))
;;   ///
;;   (defthm eval-alist-extension-p-of-eval-when-gl-bindings-extension-p
;;     (implies (gl-bindings-extension-p x y)
;;              (eval-alist-extension-p
;;               (fgl-object-alist-eval x env)
;;               (fgl-object-alist-eval y env)))
;;     :hints(("Goal" :in-theory (enable fgl-object-alist-eval gl-bindings-extension-p))))

;;   (defthm eval-alist-extension-p-self
;;     (eval-alist-extension-p x x))

  
;;   (defthm eval-alist-extension-p-of-eval-stack-bindings
;;     (implies (stack-bindings-extension-p stack1 stack0)
;;              (eval-alist-extension-p
;;               (fgl-object-alist-eval (stack$a-bindings stack1) env)
;;               (fgl-object-alist-eval (stack$a-bindings stack0) env)))
;;     :hints(("Goal" :in-theory (enable stack-bindings-extension-p
;;                                       stack$a-bindings)))))


;; (define eval-alist-extension-prefix ((x alistp)
;;                                      (y alistp))
;;   :guard (eval-alist-extension-p x y)
;;   :guard-hints (("goal" :in-theory (enable eval-alist-extension-p)))
;;   :returns (prefix alistp)
;;   (if (equal (mbe :logic (acl2::alist-fix x) :exec x)
;;              (mbe :logic (acl2::alist-fix y) :exec y))
;;       nil
;;     (and (mbt (consp x))
;;          (if (mbt (consp (car x)))
;;              (cons (car x)
;;                    (eval-alist-extension-prefix (cdr x) y))
;;            (eval-alist-extension-prefix (cdr x) y))))
;;   ///
;;   (defthm lookup-in-eval-alist-extension-when-lookup-in-suffix
;;     (implies (and (eval-alist-extension-p x y)
;;                   (hons-assoc-equal k y))
;;              (equal (hons-assoc-equal k x) (hons-assoc-equal k y)))
;;     :hints(("Goal" :in-theory (enable eval-alist-extension-p))))

;;   (defthm lookup-in-eval-alist-extension-prefix
;;     (implies (eval-alist-extension-p x y)
;;              (equal (hons-assoc-equal k (eval-alist-extension-prefix x y))
;;                     (and (not (hons-assoc-equal k y))
;;                          (hons-assoc-equal k x))))
;;     :hints(("Goal" :in-theory (enable eval-alist-extension-p)))))



;; (cmr::defthm-term-vars-flag
;;   (defthm fgl-ev-of-append-eval-alist-extension
;;     (implies (eval-alist-extension-p b a)
;;              (equal (fgl-ev x (append minor b))
;;                     (fgl-ev x (append minor a (eval-alist-extension-prefix b a)))))
;;     :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
;;     :flag cmr::term-vars)
;;   (defthm fgl-ev-list-of-append-eval-alist-extension
;;     (implies (eval-alist-extension-p b a)
;;              (equal (fgl-ev-list x (append minor b))
;;                     (fgl-ev-list x (append minor a (eval-alist-extension-prefix b a)))))
;;     :flag cmr::termlist-vars))

;; (cmr::defthm-term-vars-flag
;;   (defthm fgl-ev-of-append-eval-alist-extension-ext
;;     (implies (eval-alist-extension-p b a)
;;              (equal (fgl-ev x (append minor b ext))
;;                     (fgl-ev x (append minor a (eval-alist-extension-prefix b a) ext))))
;;     :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
;;     :flag cmr::term-vars)
;;   (defthm fgl-ev-list-of-append-eval-alist-extension-ext
;;     (implies (eval-alist-extension-p b a)
;;              (equal (fgl-ev-list x (append minor b ext))
;;                     (fgl-ev-list x (append minor a (eval-alist-extension-prefix b a) ext))))
;;     :flag cmr::termlist-vars))

;; (cmr::defthm-term-vars-flag
;;   (defthm fgl-ev-of-append-eval-alist-extension-ext
;;     (implies (and (eval-alist-extension-p b a)
;;                   (eval-alist-extension-p c b))
;;              (equal (fgl-ev x (append minor c ext))
;;                     (fgl-ev x (append minor a (eval-alist-extension-prefix b a) ext))))
;;     :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
;;     :flag cmr::term-vars)
;;   (defthm fgl-ev-list-of-append-eval-alist-extension-ext
;;     (implies (and (eval-alist-extension-p b a)
;;                   (eval-alist-extension-p c b))
;;              (equal (fgl-ev-list x (append minor c ext))
;;                     (fgl-ev-list x (append minor a (eval-alist-extension-prefix b a) ext))))
;;     :flag cmr::termlist-vars))

;; (defsection fgl-ev-equiv-contexts-p
;;   (defun-sk fgl-ev-equiv-contexts-p (contexts)
;;     (forall (x y z)
;;             (and (fgl-ev-context-equiv contexts x x)
;;                  (implies (fgl-ev-context-equiv contexts x y)
;;                           (fgl-ev-context-equiv contexts y x))
;;                  (implies (and (fgl-ev-context-equiv contexts x y)
;;                                (fgl-ev-context-equiv contexts y z))
;;                           (fgl-ev-context-equiv contexts x z))))
;;     :rewrite :direct)

;;   (in-theory (disable fgl-ev-equiv-contexts-p))

;;   (defthm fgl-ev-equiv-contexts-p-of-iff
;;     (fgl-ev-equiv-contexts-p '(iff))
;;     :hints(("Goal" :in-theory (enable fgl-ev-equiv-contexts-p
;;                                       fgl-ev-context-equiv))))

;;   (defthm fgl-ev-equiv-contexts-p-of-nil
;;     (fgl-ev-equiv-contexts-p nil)
;;     :hints(("Goal" :in-theory (enable fgl-ev-equiv-contexts-p
;;                                       fgl-ev-context-equiv))))

;;   (defthm fgl-ev-equiv-contexts-p-of-gl-interp-or-test-equiv-contexts
;;     (implies (fgl-ev-equiv-contexts-p contexts)
;;              (fgl-ev-equiv-contexts-p (gl-interp-or-test-equiv-contexts contexts)))
;;     :hints(("Goal" :in-theory (enable gl-interp-or-test-equiv-contexts)))))


;; (cmr::defthm-term-vars-flag
;;   (defthm fgl-ev-of-append-eval-alist-extension-prefix
;;     (implies (eval-alist-extension-p b a)
;;              (equal (fgl-ev x (append a (eval-alist-extension-prefix b a)))
;;                     (fgl-ev x b)))
;;     :hints('(:in-theory (enable fgl-ev-when-pseudo-term-call)))
;;     :flag cmr::term-vars)
;;   (defthm fgl-ev-list-of-append-eval-alist-extension-prefix
;;     (implies (eval-alist-extension-p b a)
;;              (equal (fgl-ev-list x (append a (eval-alist-extension-prefix b a)))
;;                     (fgl-ev-list x b)))
;;     :flag cmr::termlist-vars))


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
  (defun-sk fgl-ev-context-equiv-forall-extensions (contexts
                                                               obj
                                                               term
                                                               eval-alist)
    (forall (ext)
            (implies (eval-alist-extension-p ext eval-alist)
                     (equal (fgl-ev-context-fix contexts
                                                (fgl-ev term ext))
                            (fgl-ev-context-fix contexts obj))))
    :rewrite :direct)
  
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

  ;; (defthm context-equiv-when-fgl-ev-context-equiv-forall-extensions
  ;;   (implies (and (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist0)
  ;;                 (eval-alist-extension-p eval-alist eval-alist0))
  ;;            (fgl-ev-context-equiv contexts obj (fgl-ev term eval-alist)))
  ;;   :hints (("goal" :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
  ;;                          (eval-alist eval-alist0)
  ;;                          (ext (eval-alist-extension-prefix eval-alist eval-alist0))))
  ;;            :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc))))

  (defthm context-equiv-when-fgl-ev-context-equiv-forall-extensions-implies-equal
    (implies (and (fgl-ev-context-equiv-forall-extensions nil obj term eval-alist)
                  (eval-alist-extension-p eval-alist1 eval-alist))
             (equal (fgl-ev term eval-alist1) obj))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall))
    :rule-classes :forward-chaining)

  (defthm context-equiv-when-fgl-ev-context-equiv-forall-extensions-implies-iff
    (implies (fgl-ev-context-equiv-forall-extensions '(iff) obj term eval-alist)
             (iff (fgl-ev term eval-alist) obj))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall))
    :rule-classes :forward-chaining)


  ;; (defthm fgl-ev-context-equiv-of-gl-interp-or-test-equiv-contexts-implies-contexts
  ;;   (implies (fgl-ev-context-equiv (gl-interp-or-test-equiv-contexts contexts) a b)
  ;;            (fgl-ev-context-equiv contexts a b))
  ;;   :hints(("Goal" :in-theory (enable gl-interp-or-test-equiv-contexts)))
  ;;   :rule-classes :forward-chaining)

  (defthm fgl-ev-context-fix-or-test-of-nil
    (equal (fgl-ev-context-fix (gl-interp-or-test-equiv-contexts contexts) nil) nil)
    :hints(("Goal" :in-theory (enable gl-interp-or-test-equiv-contexts))))

  (defthm fgl-ev-context-fix-of-or-test-equiv-contexts-nil
    (iff (fgl-ev-context-fix (gl-interp-or-test-equiv-contexts contexts) x)
         x)
    :hints(("Goal" :in-theory (e/d (gl-interp-or-test-equiv-contexts)))))
  
  (local (defthm equal-of-or-test-contexts-implies-iff
           (b* ((contexts (gl-interp-or-test-equiv-contexts contexts)))
             (implies (equal (fgl-ev-context-fix contexts x)
                             (fgl-ev-context-fix contexts y))
                      (iff x y)))
           :hints(("Goal" :in-theory (enable gl-interp-or-test-equiv-contexts)))
           :rule-classes :forward-chaining))

  (local (defthm equal-of-or-test-contexts-implies-contexts
           (b* ((contexts1 (gl-interp-or-test-equiv-contexts contexts)))
             (implies (equal (fgl-ev-context-fix contexts1 x)
                             (fgl-ev-context-fix contexts1 y))
                      (equal (fgl-ev-context-fix contexts x)
                             (fgl-ev-context-fix contexts y))))
           :hints(("Goal" :in-theory (enable gl-interp-or-test-equiv-contexts)))
           :rule-classes :forward-chaining))

  ;; (local (in-theory (enable fgl-ev-context-equiv-of-gl-interp-or-test-equiv-contexts-implies-contexts)))

  (defthm fgl-ev-context-equiv-forall-extensions-rewrite-or
    (implies (and (fgl-ev-context-equiv-forall-extensions 
                   (gl-interp-or-test-equiv-contexts contexts)
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
                   (gl-interp-or-test-equiv-contexts contexts)
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

;; "goal" :expand
;;              ((fgl-ev-context-equiv-forall-extensions
;;                contexts obj0 term eval-alist))
;;              :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
;;                     (obj obj1)
;;                     (ext (fgl-ev-context-equiv-forall-extensions-witness
;;                           contexts obj0 term eval-alist))))
;;              :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc))))


  (defthm fgl-ev-context-equiv-forall-extensions-null
    (implies (pseudo-term-case x :null)
             (fgl-ev-context-equiv-forall-extensions
              contexts nil x eval-alist))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions))))

  (defthm fgl-ev-context-equiv-forall-extensions-const
    (implies (pseudo-term-case x :quote)
             (fgl-ev-context-equiv-forall-extensions
              contexts (pseudo-term-quote->val x) x eval-alist))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions))))

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

  (local (defthm lookup-in-gl-object-alist-ev
           (iff (hons-assoc-equal k (gl-object-alist-ev x env))
                (hons-assoc-equal k (gl-object-alist-fix x)))
           :hints(("Goal" :in-theory (enable gl-object-alist-ev
                                             gl-object-alist-fix)))))

  (local (defthm lookup-in-minor-stack-of-stack-ev
           (iff (hons-assoc-equal var (stack$a-minor-bindings
                                       (major-stack-ev stack env)))
                (hons-assoc-equal var (stack$a-minor-bindings stack)))
           :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                             major-frame-ev
                                             minor-frame-ev)
                   :expand ((major-stack-ev stack env)
                            (minor-stack-ev
                             (major-frame->minor-stack (car stack))
                             env))))))

  (defthm major-stack-ev-of-stack$a-add-binding
    (equal (major-stack-ev (stack$a-add-binding var val stack) env)
           (stack$a-add-binding var (gl-object-ev val env)
                                (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-add-binding
                                      major-stack-ev
                                      gl-object-alist-ev
                                      major-frame-ev))))

  (defthm stack$a-bindings-of-stack$a-add-binding
    (equal (stack$a-bindings (stack$a-add-binding var val stack))
           (cons (cons (pseudo-var-fix var)
                       (gl-object-fix val))
                 (stack$a-bindings stack)))
    :hints(("Goal" :in-theory (enable stack$a-bindings
                                      stack$a-add-binding))))
  

  (defthm fgl-ev-context-equiv-forall-extensions-of-return-last-syntax-bind
    (b* (((mv ans new-interp-st) (gl-interp-syntax-bind synp-arg x interp-st state)))
      (implies (and (not (interp-st->errmsg new-interp-st)))
               (fgl-ev-context-equiv-forall-extensions
                contexts
                (fgl-object-eval ans env (interp-st->logicman interp-st))
                x
                (append (fgl-object-alist-eval
                         (stack$a-minor-bindings
                          (major-stack-ev (interp-st->stack interp-st)
                                          env (interp-st->logicman interp-st)))
                         nil nil)
                        (fgl-object-alist-eval
                         (stack$a-bindings
                          (major-stack-ev (interp-st->stack new-interp-st)
                                          env (interp-st->logicman interp-st)))
                         nil nil)))))
    :hints(("Goal" :in-theory (enable gl-interp-syntax-bind fgl-ev-context-equiv-forall-extensions)))))




(local (in-theory (disable acl2::rewrite-rule-term)))                  

(defthmd rewrite-rule-term-alt-def
  (equal (acl2::rewrite-rule-term x)
         (if (eq (acl2::rewrite-rule->subclass x) 'acl2::meta)
             ''t
           `(implies ,(conjoin (acl2::rewrite-rule->hyps x))
                     (,(acl2::rewrite-rule->equiv x)
                      ,(acl2::rewrite-rule->lhs x)
                      ,(acl2::rewrite-rule->rhs x)))))
  :hints(("Goal" :in-theory (enable acl2::rewrite-rule-term
                                    acl2::rewrite-rule->subclass
                                    acl2::rewrite-rule->hyps
                                    acl2::rewrite-rule->equiv
                                    acl2::rewrite-rule->lhs
                                    acl2::rewrite-rule->rhs))))



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
 (defsection fgl-ev-context-fix-equal-by-eval



   (local (defthm member-equiv-contexts-implies-not-quote
            (implies (member-equal x (equiv-contexts-fix contexts))
                     (not (equal x 'quote)))
            :hints(("Goal" :in-theory (enable equiv-contexts-fix equiv-context-fix)))
            :rule-classes :forward-chaining))

   
   (local (defthm kwote-lst-redef
            (equal (kwote-lst x)
                   (if (atom x)
                       nil
                     (cons (pseudo-term-quote (car x))
                           (kwote-lst (cdr x)))))
            :hints(("Goal" :in-theory (enable pseudo-term-quote)))
            :rule-classes :definition))

   (local (defthm pseudo-fnsym-p-when-equiv-context-p
            (implies (and (symbolp x)
                          (equiv-context-p x))
                     (pseudo-fnsym-p x))
            :hints(("Goal" :in-theory (enable equiv-context-p)))))

   (local (in-theory (disable pseudo-fnsym-p-of-equiv-context-when-atom)))

   (local (defthm fgl-ev-context-equiv-some-by-eval
            (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
                                  nil)
                          (member-equal fn (equiv-contexts-fix contexts))
                          (symbolp fn))
                     (fgl-ev-context-equiv-some contexts x y))
            :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-some
                                              equiv-contexts-fix
                                              fgl-ev-equiv-context-equiv-base)))))

   (local (defthm fgl-ev-context-equiv-by-eval
            (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
                                  nil)
                          (member-equal fn (equiv-contexts-fix contexts))
                          (symbolp fn))
                     (fgl-ev-context-equiv contexts x y))
            :hints(("Goal" :use ((:instance fgl-ev-context-equiv-suff
                                  (trace (list x y))))
                    :in-theory (e/d (fgl-ev-context-equiv-symm)
                                    (fgl-ev-context-equiv-is-equal-of-fixes))))))

   (defthmd fgl-ev-context-fix-equal-by-eval
     (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
                           nil)
                   (member-equal fn (equiv-contexts-fix contexts))
                   (symbolp fn))
              (equal (fgl-ev-context-fix contexts x)
                     (fgl-ev-context-fix contexts y)))
     :hints (("goal" :use fgl-ev-context-equiv-by-eval
              :in-theory (disable fgl-ev-context-equiv-by-eval)))
     :rule-classes :forward-chaining)))


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

  (defthm fgl-ev-context-equiv-forall-extensions-when-iff
    (iff (fgl-ev-context-equiv-forall-extensions
          '(iff) obj term eval-alist)
         (iff-forall-extensions obj term eval-alist))
    :hints ((acl2::witness :ruleset context-equiv-forall)))

  (defthm iff-forall-extensions-when-extension
    (implies (and (iff-forall-extensions obj term (append minor major0))
                  (eval-alist-extension-p major1 major0))
             (iff-forall-extensions obj term (append minor major1)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset iff-forall)))

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

  

  (defthm apply-rewrite-rule-when-iff-forall-extensions
    (implies (and (fgl-ev-theoremp (acl2::Rewrite-rule-term rule))
                  (iff-forall-extensions
                   t (conjoin (acl2::rewrite-rule->hyps rule))
                   major-bindings1)
                  (mv-nth 0 (glcp-unify-term/gobj-list
                             (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                             args nil))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts rhs-obj (acl2::rewrite-rule->rhs rule)
                   major-bindings2)
                  (pseudo-term-case (acl2::rewrite-rule->lhs rule) :fncall)
                  (equal (pseudo-term-fncall->fn (acl2::rewrite-rule->lhs rule)) fn)
                  (equal (acl2::rewrite-rule->equiv rule) 'equal)
                  (not (equal (acl2::rewrite-rule->subclass rule) 'acl2::meta))
                  (eval-alist-extension-p
                   major-bindings2
                   (fgl-object-alist-eval
                    (mv-nth 1 (glcp-unify-term/gobj-list
                               (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                               args nil))
                    env))
                  (eval-alist-extension-p major-bindings2 major-bindings1))
             (equal (fgl-ev-context-fix contexts
                                        (fgl-ev (cons fn
                                                      (kwote-lst (fgl-objectlist-eval args env)))
                                                nil))
                    (fgl-ev-context-fix contexts rhs-obj)))
  :hints (("Goal" :in-theory (e/d (rewrite-rule-term-alt-def
                                   fgl-ev-of-fncall-args)
                                  (fgl-ev-list-of-extension-when-term-vars-bound))
           :use ((:instance fgl-ev-falsify
                  (x (acl2::rewrite-rule-term rule))
                  (a major-bindings2))
                 (:instance fgl-ev-list-of-extension-when-term-vars-bound
                  (x (pseudo-term-call->args (acl2::rewrite-rule->lhs rule)))
                  (a (fgl-object-alist-eval
                      (mv-nth 1 (glcp-unify-term/gobj-list
                                 (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                                 args nil))
                      env))
                  (b major-bindings2))))
          (acl2::witness :ruleset (context-equiv-forall))))

  (local (in-theory (enable fgl-ev-context-fix-equal-by-eval)))

  (local (defthm member-equiv-contexts-implies-not-quote
            (implies (member-equal x (equiv-contexts-fix contexts))
                     (not (equal x 'quote)))
            :hints(("Goal" :in-theory (enable equiv-contexts-fix equiv-context-fix)))
            :rule-classes :forward-chaining))

   (local (defthm kwote-lst-redef
            (equal (kwote-lst x)
                   (if (atom x)
                       nil
                     (cons (pseudo-term-quote (car x))
                           (kwote-lst (cdr x)))))
            :hints(("Goal" :in-theory (enable pseudo-term-quote)))
            :rule-classes :definition))  

                    

  (defthm apply-rewrite-rule-when-iff-forall-extensions-context-equiv
    (implies (and (fgl-ev-theoremp (acl2::Rewrite-rule-term rule))
                  (iff-forall-extensions
                   t (conjoin (acl2::rewrite-rule->hyps rule))
                   major-bindings1)
                  (mv-nth 0 (glcp-unify-term/gobj-list
                             (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                             args nil))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts rhs-obj (acl2::rewrite-rule->rhs rule)
                   major-bindings2)
                  (pseudo-term-case (acl2::rewrite-rule->lhs rule) :fncall)
                  (equal (pseudo-term-fncall->fn (acl2::rewrite-rule->lhs rule)) fn)
                  (symbolp (acl2::rewrite-rule->equiv rule))
                  (member-equal (acl2::rewrite-rule->equiv rule)
                                (equiv-contexts-fix contexts))
                  (not (equal (acl2::rewrite-rule->subclass rule) 'acl2::meta))
                  (eval-alist-extension-p
                   major-bindings2
                   (fgl-object-alist-eval
                    (mv-nth 1 (glcp-unify-term/gobj-list
                               (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                               args nil))
                    env))
                  (eval-alist-extension-p major-bindings2 major-bindings1))
             (equal (fgl-ev-context-fix contexts
                                        (fgl-ev (cons fn
                                                      (kwote-lst (fgl-objectlist-eval args env)))
                                                nil))
                    (fgl-ev-context-fix contexts rhs-obj)))
  :hints (("Goal" :in-theory (e/d (rewrite-rule-term-alt-def
                                   fgl-ev-of-fncall-args)
                                  (fgl-ev-list-of-extension-when-term-vars-bound))
           :use ((:instance fgl-ev-falsify
                  (x (acl2::rewrite-rule-term rule))
                  (a major-bindings2))
                 (:instance fgl-ev-list-of-extension-when-term-vars-bound
                  (x (pseudo-term-call->args (acl2::rewrite-rule->lhs rule)))
                  (a (fgl-object-alist-eval
                      (mv-nth 1 (glcp-unify-term/gobj-list
                                 (pseudo-term-call->args (acl2::rewrite-rule->lhs rule))
                                 args nil))
                      env))
                  (b major-bindings2))))
          (acl2::witness :ruleset (context-equiv-forall))))

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
    (implies (mv-nth 0 (gl-interp-match-synp hyp))
             (iff-forall-extensions
              t hyp eval-alist))
    :hints(("Goal" :in-theory (enable iff-forall-extensions
                                      gl-interp-match-synp))))



  (defthm iff-forall-extensions-of-if
    (implies (and (iff-forall-extensions test-res test (append minor-bindings major-bindings1))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts then-res then (append minor-bindings major-bindings2))
                  (fgl-ev-context-equiv-forall-extensions
                   contexts else-res else (append minor-bindings major-bindings3))
                  (equal res (if* test-res then-res else-res))
                  (eval-alist-extension-p major-bindings2 major-bindings1)
                  (eval-alist-extension-p major-bindings3 major-bindings2))
             (fgl-ev-context-equiv-forall-extensions
              contexts res (pseudo-term-fncall 'if (list test then else))
              (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff-forall-extensions-of-if-false
    (implies (and (iff-forall-extensions nil test (append minor-bindings major-bindings1))
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

  (defthm iff-forall-extensions-of-if-true
    (implies (and (iff-forall-extensions t test (append minor-bindings major-bindings1))
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

  (defthm iff-forall-extensions-of-if-true-equiv
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
            (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff-forall-extensions-of-if-false-equiv
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





  ;; (defthm fgl-ev-context-equiv-by-rewrite-rule
  ;;   )
                            


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
      :hints(("Goal" :in-theory (enable equal-list-forall-extensions)))))



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
                               maj)))))))
             


(defsection gl-interp-preserves-errmsg
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
      :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
      :mutual-recursion gl-interp)))


(defsection bvar-db-ok-of-gl-interp
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

  (local (defthmd gl-object-bfrlist-of-get-bvar->term$a-aux
           (implies (and (not (member v (bvar-db-bfrlist-aux m bvar-db)))
                         (< (nfix n) (nfix m))
                         (<= (base-bvar$a bvar-db) (nfix n)))
                    (not (member v (gl-object-bfrlist (get-bvar->term$a n bvar-db)))))
           :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)))))

  (local (defthm gl-object-bfrlist-of-get-bvar->term$a
           (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db)))
                    (not (member v (gl-object-bfrlist (get-bvar->term$a n bvar-db)))))
           :hints (("goal" :in-theory (enable bvar-db-bfrlist)
                    :use ((:instance gl-object-bfrlist-of-get-bvar->term$a-aux
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

  ;; (local (defthm interp-st-bvar-db-ok-necc-free
  ;;          (b* ((bvar-db (interp-st->bvar-db interp-st))
  ;;               (logicman (interp-st->logicman interp-st)))
  ;;            (implies (and (interp-st-bvar-db-ok interp-st env)
  ;;                          (case-split
  ;;                            (equal (fgl-object-eval (get-bvar->term$a n bvar-db1)
  ;;                                                    env logicman1)
  ;;                                   (fgl-object-eval (get-bvar->term$a n bvar-db)
  ;;                                                    env logicman)))
  ;;                          (<= (base-bvar$a bvar-db) (nfix n))
  ;;                          (< (nfix n) (next-bvar$a bvar-db)))
  ;;                     (iff* (fgl-object-eval (get-bvar->term$a n bvar-db1)
  ;;                                            env logicman1)
  ;;                           (gobj-bfr-eval (bfr-var n) env logicman))))))

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
                     ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                     ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                     (interp-st                     (interp-st-bfrs-ok interp-st))
                     ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
       
       :rules ((t (:add-concl (implies (not (interp-st-bvar-db-ok interp-st env))
                                       (not (interp-st-bvar-db-ok new-interp-st env))))
                  (:add-keyword :hints ('(:do-not-induct t)
                                        (let ((flag (find-flag-is-hyp clause)))
                                          (and flag
                                               (prog2$ (cw "flag: ~x0~%" flag)
                                                       '(:no-op t)))))))
               ((:fnname gl-rewrite-try-rules)
                (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist))))

       :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
       :mutual-recursion gl-interp)))


  (define interp-st-bvar-db-ok* (interp-st env)
    :verify-guards nil
    (interp-st-bvar-db-ok interp-st env))

  (local (in-theory (enable interp-st-bvar-db-ok*)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-bvar-db-ok-implies-previous-ok
      
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
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
              ((:fnname gl-rewrite-try-rules)
               (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st)))
                           :gl-objlist))))
      
      :hints (("goal" :do-not-induct t
               :in-theory (enable and*)))
      :no-induction-hint t
      :mutual-recursion gl-interp)))

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



(local (in-theory (disable w)))

;; (defsection gl-interp-preserves-w-state
;;   (with-output
;;     :off (event)
;;     :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
;;     (std::defret-mutual-generate <fn>-preserves-w-state
;;       :rules ((t (:add-concl (equal (w new-state) (w state)))
;;                  (:add-keyword :hints ('(:do-not-induct t)
;;                                        (let ((flag (find-flag-is-hyp clause)))
;;                                          (and flag
;;                                               (prog2$ (cw "flag: ~x0~%" flag)
;;                                                       '(:no-op t))))))))
;;       :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
;;       :mutual-recursion gl-interp)))

(defret logicman-pathcond-eval-preserved-by-logicman-pathcond-assume
  (implies (and (logicman-pathcond-eval env pathcond)
                (bfr-eval x env)
                (not contradictionp))
           (logicman-pathcond-eval env new-pathcond logicman))
  :hints (("goal" :cases ((pathcond-enabledp pathcond))))
  :fn logicman-pathcond-assume)

(defthm not-logicman-pathcond-eval-of-assume
  (implies (and (acl2::rewriting-positive-literal
                 `(logicman-pathcond-eval-fn
                   ,env
                   (mv-nth '1 (logicman-pathcond-assume-fn ,x ,pathcond ,logicman))
                   ,logicman))
                (logicman-pathcond-eval env pathcond logicman)
                (not (mv-nth 0 (logicman-pathcond-assume x pathcond))))
           (iff (logicman-pathcond-eval env (mv-nth 1 (logicman-pathcond-assume x pathcond)))
                (or (not (pathcond-enabledp pathcond))
                    (bfr-eval x env)))))

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))
    

(acl2::set-case-split-limitations '(500 100000))

;; (local (in-theory (disable bfr-listp-when-not-member-witness)))

(defthm stack$a-minor-bindings-of-push-scratch
  (equal (stack$a-minor-bindings (stack$a-push-scratch obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                    stack$a-push-scratch))))

(include-book "tools/some-events" :dir :system)


(defsection check-equiv-replacement-correct
  (local (std::set-define-current-function check-equiv-replacement))
  (local (in-theory (enable check-equiv-replacement)))
  
  (local (defthm kwote-lst-redef
           (equal (kwote-lst x)
                  (if (atom x)
                      nil
                    (cons (pseudo-term-quote (car x))
                          (kwote-lst (cdr x)))))
           :hints(("Goal" :in-theory (enable pseudo-term-quote)))
           :rule-classes :definition))

  (local (in-theory (disable kwote-lst)))

  (local (in-theory (enable fgl-ev-context-fix-equal-by-eval)))

  (local (in-theory (enable fgl-apply fgl-objectlist-eval)))
  (defret check-equiv-replacement-correct
    (implies (and ok
                  (xor negp (fgl-object-eval equiv-term env)))
             (equal (fgl-ev-context-fix contexts (fgl-object-eval equiv env))
                    (fgl-ev-context-fix contexts (fgl-object-eval x env))))))
             ;; (and (implies negp
             ;;               (fgl-ev-context-equiv contexts
             ;;                                     (fgl-object-eval equiv env)
             ;;                                     (not (fgl-object-eval x env))))
             ;;      (implies (not negp)
             ;;               )))))


(defsection try-equivalences-correct
  (local (std::set-define-current-function try-equivalences))
  (local (in-theory (enable try-equivalences)))

  (defthm try-equivalences-of-pathcond-fix
    (equal (try-equivalences x bvars contexts (pathcond-fix pathcond) bvar-db logicman state)
           (try-equivalences x bvars contexts pathcond bvar-db logicman state)))

  ;; (local (defretd eval-equal-bit-of-logicman-pathcond-implies
  ;;          (implies (and (logicman-pathcond-eval env pathcond)
  ;;                        ans)
  ;;                   (equal (bfr-eval x env)
  ;;                          (bit->bool ans)))
  ;;          :hints (("goal" :use eval-when-logicman-pathcond-implies))
  ;;          :fn logicman-pathcond-implies))

  ;; (local (in-theory (e/d (eval-equal-bit-of-logicman-pathcond-implies)
  ;;                        (eval-when-logicman-pathcond-implies))))

  (local (defthm bfr-eval-of-gl-env->bfr-vars
           (equal (bfr-eval bfr (gl-env->bfr-vals env))
                  (gobj-bfr-eval bfr env))
           :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

  (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

  ;; (local (in-theory (enable interp-st-bvar-db-ok-necc)))

  (defret try-equivalences-correct
    :pre-bind ((logicman (interp-st->logicman interp-st))
               (bvar-db (interp-st->bvar-db interp-st))
               (pathcond (interp-st->pathcond interp-st)))
    (implies (and ok
                  (logicman-pathcond-eval (gl-env->bfr-vals env)
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
                          (env (gl-env->bfr-vals env))))
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
                  (logicman-pathcond-eval (gl-env->bfr-vals env)
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




(defthm stack$a-minor-bindings-of-stack$a-set-minor-debug
  (equal (stack$a-minor-bindings (stack$a-set-minor-debug obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-minor-debug))))

(defthm stack$a-minor-bindings-of-stack$a-push-frame
  (equal (stack$a-minor-bindings (stack$a-push-frame stack))
         nil)
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-push-frame))))

(defthm stack$a-minor-bindings-of-stack$a-set-debug
  (equal (stack$a-minor-bindings (stack$a-set-debug obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-debug))))

(defthm stack$a-minor-bindings-of-stack$a-set-bindings
  (equal (stack$a-minor-bindings (stack$a-set-bindings bindings stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-bindings))))

(defthm stack$a-minor-bindings-of-stack$a-set-minor-bindings
  (equal (stack$a-minor-bindings (stack$a-set-minor-bindings bindings stack))
         (gl-object-alist-fix bindings))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-set-minor-bindings))))

(defthm stack$a-minor-bindings-of-stack$a-add-minor-bindings
  (equal (stack$a-minor-bindings (stack$a-add-minor-bindings bindings stack))
         (append (gl-object-alist-fix bindings) (stack$a-minor-bindings stack)))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings stack$a-add-minor-bindings))))

(defthm stack$a-bindings-of-stack$a-add-minor-bindings
  (equal (stack$a-bindings (stack$a-add-minor-bindings bindings stack))
         (stack$a-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-add-minor-bindings))))

(defthm stack$a-bindings-of-stack$a-set-bindings
  (equal (stack$a-bindings (stack$a-set-bindings bindings stack))
         (gl-object-alist-fix bindings))
  :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-set-bindings))))

(defthm fgl-object-alist-eval-of-append
  (equal (fgl-object-alist-eval (append a b) env)
         (append (fgl-object-alist-eval a env)
                 (fgl-object-alist-eval b env)))
  :hints(("Goal" :in-theory (enable fgl-object-alist-eval))))

(defthm fgl-object-alist-eval-of-pairlis$
  (implies (pseudo-var-list-p keys)
           (equal (fgl-object-alist-eval (pairlis$ keys vals) env)
                  (pairlis$ keys (fgl-objectlist-eval vals env))))
  :hints(("Goal" :in-theory (enable fgl-object-alist-eval pairlis$ fgl-objectlist-eval default-car))))


(defthm fgl-object-alist-eval-of-nil
  (equal (fgl-object-alist-eval nil env) nil)
  :hints(("Goal" :in-theory (enable fgl-object-alist-eval))))




(define fgl-ev-good-rewrite-rulesp (rules)
  (if (atom rules)
      t
    (and (fgl-ev-theoremp (acl2::rewrite-rule-term (car rules)))
         (fgl-ev-good-rewrite-rulesp (cdr rules))))
  ///
  (defthm fgl-ev-theoremp-of-car-when-fgl-ev-good-rewrite-rulesp
    (implies (and (fgl-ev-good-rewrite-rulesp rules)
                  (consp rules))
             (fgl-ev-theoremp (acl2::rewrite-rule-term (car rules)))))

  (defthm fgl-ev-good-rewrite-rulesp-of-cdr
    (implies (fgl-ev-good-rewrite-rulesp rules)
             (fgl-ev-good-rewrite-rulesp (cdr rules))))

  (defthm fgl-ev-good-rewrite-rulesp-of-fn-definition-rules
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (fgl-ev-good-rewrite-rulesp (fn-definition-rules fn deftable wrld)))
    :hints (("goal" :use ((:functional-instance mextract-good-rewrite-rulesp-of-fn-definition-rules
                           (acl2::mextract-ev fgl-ev)
                           (acl2::mextract-ev-lst fgl-ev-list)
                           (acl2::mextract-ev-falsify fgl-ev-falsify)
                           (acl2::mextract-global-badguy fgl-ev-meta-extract-global-badguy)
                           (mextract-good-rewrite-rulesp fgl-ev-good-rewrite-rulesp))))))

  (defthm fgl-ev-good-rewrite-rulesp-of-fn-rewrite-rules
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (fgl-ev-good-rewrite-rulesp (fn-rewrite-rules fn runetable wrld)))
    :hints (("goal" :use ((:functional-instance mextract-good-rewrite-rulesp-of-fn-rewrite-rules
                           (acl2::mextract-ev fgl-ev)
                           (acl2::mextract-ev-lst fgl-ev-list)
                           (acl2::mextract-ev-falsify fgl-ev-falsify)
                           (acl2::mextract-global-badguy fgl-ev-meta-extract-global-badguy)
                           (mextract-good-rewrite-rulesp fgl-ev-good-rewrite-rulesp))))))

  (defthm fgl-ev-good-branch-merge-rulep-of-fn-branch-merge-rules
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (equal wrld (w state)))
             (fgl-ev-good-rewrite-rulesp (fn-branch-merge-rules fn runes wrld)))
    :hints (("goal" :use ((:functional-instance mextract-good-rewrite-rulesp-of-fn-branch-merge-rules
                           (acl2::mextract-ev fgl-ev)
                           (acl2::mextract-ev-lst fgl-ev-list)
                           (acl2::mextract-ev-falsify fgl-ev-falsify)
                           (acl2::mextract-global-badguy fgl-ev-meta-extract-global-badguy)
                           (mextract-good-rewrite-rulesp fgl-ev-good-rewrite-rulesp)))))))




(def-updater-independence-thm eval-alist-extension-p-of-interp-st-update
  (implies (and (stack-bindings-extension-p
                 (major-stack-ev (interp-st->stack new) env (interp-st->logicman new))
                 (major-stack-ev (interp-st->stack old) env (interp-st->logicman old)))
                (eval-alist-extension-p
                 (fgl-object-alist-eval
                  (stack$a-bindings
                   (major-stack-ev
                    (interp-st->stack old) env (interp-st->logicman old)))
                  nil nil)
                 other))
           (eval-alist-extension-p
            (fgl-object-alist-eval
             (stack$a-bindings
              (major-stack-ev
               (interp-st->stack new) env (interp-st->logicman new)))
             nil nil)
            other))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-2
                                    stack$a-bindings
                                    stack-bindings-extension-p))))


;; (def-updater-independence-thm eval-alist-extension-p-of-interp-st-alist-eval
;;   (implies (and (stack-bindings-extension-p
;;                  (major-stack-ev
;;                   (interp-st->stack new) env (interp-st->logicman new))
;;                  other))
;;            (eval-alist-extension-p
;;             (fgl-object-alist-eval
;;              (stack$a-bindings
;;               (major-stack-ev
;;                (interp-st->stack new) env (interp-st->logicman new)))
;;              nil nil)
;;             other))
;;   :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive))))

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


(defsection-unique gl-interp-correct
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))


  (def-updater-independence-thm fgl-objectlist-eval-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-objectlist-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-objectlist-eval x env (interp-st->logicman new))
                    (fgl-objectlist-eval x env (interp-st->logicman old)))))

  (def-updater-independence-thm fgl-object-alist-eval-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-object-alist-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-object-alist-eval x env (interp-st->logicman new))
                    (fgl-object-alist-eval x env (interp-st->logicman old)))))
  


  (local (defthm fgl-object-eval-rewrite-with-fgl-object-ev
           (implies (and (equal ev (double-rewrite (gl-object-ev x env)))
                         (syntaxp ;; (prog2$ (cw "~x0~%ev: ~x1~%"
                          ;;             'fgl-object-eval-rewrite-with-fgl-object-ev
                          ;;             ev)
                          (and (not (equal ev x))
                               (case-match ev
                                 (('gl-object-ev-fn xans & &)
                                  (not (equal xans x)))
                                 (& t))))
                         (equal eval (fgl-object-eval ev nil nil))
                         (syntaxp ;; (prog2$ (cw "eval: ~x0~%" eval)
                          (case-match eval
                            (('fgl-object-eval-fn ('gl-object-ev-fn xans & &) & &)
                             (not (equal xans x)))
                            (('fgl-object-eval-fn xans & &)
                             (not (equal xans x)))
                            (& t))))
                    (equal (fgl-object-eval x env) eval))))

  (local (defthm fgl-objectlist-eval-rewrite-with-fgl-objectlist-ev
           (implies (and (equal ev (double-rewrite (gl-objectlist-ev x env)))
                         (syntaxp (and (not (equal ev x))
                                       (case-match ev
                                         (('gl-objectlist-ev-fn xans & &)
                                          (not (equal xans x)))
                                         (& t))))
                         (equal eval (fgl-objectlist-eval ev nil nil))
                         (syntaxp (case-match eval
                                    (('fgl-objectlist-eval-fn ('gl-objectlist-ev-fn xans & &) & &)
                                     (not (equal xans x)))
                                    (('fgl-objectlist-eval-fn xans & &)
                                     (not (equal xans x)))
                                    (& t))))
                    (equal (fgl-objectlist-eval x env) eval))))

  (local (defthm fgl-object-alist-eval-rewrite-with-fgl-object-alist-ev
           (implies (and (equal ev (double-rewrite (gl-object-alist-ev x env)))
                         (syntaxp (and (not (equal ev x))
                                       (case-match ev
                                         (('gl-object-alist-ev-fn xans & &)
                                          (not (equal xans x)))
                                         (& t))))
                         (equal eval (fgl-object-alist-eval ev nil nil))
                         (syntaxp (case-match eval
                                    (('fgl-object-alist-eval-fn ('gl-objectlist-ev-fn xans & &) & &)
                                     (not (equal xans x)))
                                    (('fgl-object-alist-eval-fn xans & &)
                                     (not (equal xans x)))
                                    (& t))))
                    (equal (fgl-object-alist-eval x env) eval))))

  (local (defthm fgl-objectlist-eval-of-atom
           (implies (not (Consp x))
                    (equal (fgl-objectlist-eval x env logicman) nil))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (local (defthm fgl-objectlist-eval-of-cons
           (Equal (fgl-objectlist-eval (cons a b) env)
                  (cons (fgl-object-eval a env)
                        (fgl-objectlist-eval b env)))
           :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

  (local (defthm fgl-objectlist-eval-when-consp
           (implies (consp x)
                    (Equal (fgl-objectlist-eval x env)
                           (cons (fgl-object-eval (car x) env)
                                 (fgl-objectlist-eval (cdr x) env))))
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
   (defthm len-gl-objlist-when-scratchobj-isomorphic-rw
     (implies (and (scratchobj-isomorphic y (double-rewrite x))
                   (syntaxp (not (equal y x)))
                   (scratchobj-case y :gl-objlist))
              (equal (len (scratchobj-gl-objlist->val x))
                     (len (scratchobj-gl-objlist->val y))))))  


  (local (defthm fgl-object-ev-of-scratchobj-gl-obj->val
           (implies (double-rewrite (scratchobj-case x :gl-obj))
                    (equal (gl-object-ev (scratchobj-gl-obj->val x) env)
                           (scratchobj-gl-obj->val (scratchobj-ev x env))))
           :hints(("Goal" :in-theory (enable scratchobj-ev)))))

  (local (defthm fgl-objectlist-ev-of-scratchobj-gl-objlist->val
           (implies (double-rewrite (scratchobj-case x :gl-objlist))
                    (equal (gl-objectlist-ev (scratchobj-gl-objlist->val x) env)
                           (scratchobj-gl-objlist->val (scratchobj-ev x env))))
           :hints(("Goal" :in-theory (enable scratchobj-ev)))))


  (local (defthm fgl-object-eval-of-alist-lookup
           (implies (pseudo-var-p x)
                    (equal (fgl-object-eval
                            (cdr (hons-assoc-equal x alist)) env)
                           (cdr (hons-assoc-equal x (fgl-object-alist-eval alist env)))))
           :hints(("Goal" :in-theory (enable fgl-object-alist-eval)))))

  (local (in-theory (disable lookup-in-fgl-object-alist-eval)))

  (local (defthm fgl-object-alist-ev-of-stack$a-minor-bindings
           (equal (gl-object-alist-ev (stack$a-minor-bindings stack) env)
                  (stack$a-minor-bindings (major-stack-ev stack env)))
           :hints(("Goal" :in-theory (enable major-frame-ev
                                             minor-frame-ev
                                             stack$a-minor-bindings)
                   :expand ((major-stack-ev stack env)
                            (minor-stack-ev (major-frame->minor-stack (car stack)) env))))))

  (local (defthm fgl-object-alist-ev-of-stack$a-bindings
           (equal (gl-object-alist-ev (stack$a-bindings stack) env)
                  (stack$a-bindings (major-stack-ev stack env)))
           :hints(("Goal" :in-theory (enable major-frame-ev
                                             stack$a-bindings)
                   :expand ((major-stack-ev stack env))))))

  (local (defthm scratchobj-ev-of-stack$a-top-scratch
           (equal (scratchobj-ev (stack$a-top-scratch stack) env)
                  (double-rewrite (stack$a-top-scratch (major-stack-ev stack env))))
           :hints(("Goal" :in-theory (enable stack$a-top-scratch
                                             major-frame-ev
                                             minor-frame-ev)
                   :expand ((major-stack-ev stack env)
                            (minor-stack-ev
                             (major-frame->minor-stack (Car stack)) env)
                            (scratchlist-ev
                             (minor-frame->scratch
                              (car (major-frame->minor-stack (Car stack))))
                             env)
                            (scratchobj-ev '(:gl-obj) env)
                            (gl-object-ev nil env))))))

  (local (defthm gl-object-ev-identity
           (equal (gl-object-ev (gl-object-ev x env) env2 logicman2)
                  (gl-object-ev x env))
           :hints(("Goal" :in-theory (enable gl-object-ev)))))

  (local (defthm gl-objectlist-ev-identity
           (equal (gl-objectlist-ev (gl-objectlist-ev x env) env2 logicman2)
                  (gl-objectlist-ev x env))
           :hints(("Goal" :in-theory (enable gl-objectlist-ev)))))

  (local (defthm bfr-eval-of-boolean
           (implies (booleanp x)
                    (equal (bfr-eval x env) x))
           :hints(("Goal" :in-theory (enable bfr-eval booleanp bfr->aignet-lit)))))

  (local (defthm gobj-bfr-eval-identity
           (equal (gobj-bfr-eval (gobj-bfr-eval x env) env2 logicman2)
                  (gobj-bfr-eval x env))
           :hints(("Goal" :in-theory (e/d (gobj-bfr-eval))))))

  (local (defthm gobj-bfr-list-eval-identity
           (equal (gobj-bfr-list-eval (gobj-bfr-list-eval x env) env2 logicman2)
                  (gobj-bfr-list-eval x env))
           :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval))))))

  (local (defthm gl-object-alist-ev-identity
           (equal (gl-object-alist-ev (gl-object-alist-ev x env) env2 logicman2)
                  (gl-object-alist-ev x env))
           :hints(("Goal" :in-theory (enable gl-object-alist-ev)))))

  (local (defthm constraint-instance-ev-identity
           (equal (constraint-instance-ev (constraint-instance-ev x env) env2 logicman2)
                  (constraint-instance-ev x env))
           :hints(("Goal" :in-theory (enable constraint-instance-ev)))))

  (local (defthm constraint-instancelist-ev-identity
           (equal (constraint-instancelist-ev (constraint-instancelist-ev x env) env2 logicman2)
                  (constraint-instancelist-ev x env))
           :hints(("Goal" :in-theory (enable constraint-instancelist-ev)))))

  (local (defthm scratchobj-ev-identity
           (equal (scratchobj-ev (scratchobj-ev x env) env2 logicman2)
                  (scratchobj-ev x env))
           :hints(("Goal" :in-theory (e/d (scratchobj-ev)
                                          (fgl-object-ev-of-scratchobj-gl-obj->val
                                           fgl-objectlist-ev-of-scratchobj-gl-objlist->val))))))

  (local (defthm scratchlist-ev-identity
           (equal (scratchlist-ev (scratchlist-ev x env) env2 logicman2)
                  (scratchlist-ev x env))
           :hints(("Goal" :in-theory (enable scratchlist-ev)))))

  (local (defthm minor-frame-ev-identity
           (equal (minor-frame-ev (minor-frame-ev x env) env2 logicman2)
                  (minor-frame-ev x env))
           :hints(("Goal" :in-theory (enable minor-frame-ev)))))

  (local (defthm minor-stack-ev-identity
           (equal (minor-stack-ev (minor-stack-ev x env) env2 logicman2)
                  (minor-stack-ev x env))
           :hints(("Goal" :in-theory (enable minor-stack-ev)))))

  (local (defthm major-frame-ev-identity
           (equal (major-frame-ev (major-frame-ev x env) env2 logicman2)
                  (major-frame-ev x env))
           :hints(("Goal" :in-theory (enable major-frame-ev)))))

  (local (defthm major-stack-ev-identity
           (equal (major-stack-ev (major-stack-ev x env) env2 logicman2)
                  (major-stack-ev x env))
           :hints(("Goal" :in-theory (enable major-stack-ev)))))

  (local (defthm gl-object-alist-ev-of-stack$a-minor-bindings
           (equal (gl-object-alist-ev (stack$a-minor-bindings stack) env)
                  (double-rewrite (stack$a-minor-bindings (major-stack-ev stack env))))
           :hints(("Goal" :in-theory (enable major-frame-ev
                                             minor-frame-ev
                                             stack$a-minor-bindings)
                   :expand ((major-stack-ev stack env)
                            (minor-stack-ev
                             (major-frame->minor-stack (Car stack)) env))
                   :do-not-induct t))))

  (local (defthm lookup-present-of-gl-object-alist-ev
           (iff (hons-assoc-equal k (gl-object-alist-ev x env))
                (hons-assoc-equal k (gl-object-alist-fix x)))
           :hints(("Goal" :in-theory (enable gl-object-alist-fix gl-object-alist-ev)))))

  (local (defthm lookup-present-of-stack$a-minor-bindings-of-major-stack-ev
           (iff (hons-assoc-equal k (stack$a-minor-bindings (major-stack-ev stack env)))
                (hons-assoc-equal k (stack$a-minor-bindings stack)))
           :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                             major-frame-ev
                                             minor-frame-ev)
                   :expand ((major-stack-ev stack env)
                            (minor-stack-ev
                             (major-frame->minor-stack (Car stack)) env))))))

  (local (defthm lookup-present-of-stack$a-bindings-of-major-stack-ev
           (iff (hons-assoc-equal k (stack$a-bindings (major-stack-ev stack env)))
                (hons-assoc-equal k (stack$a-bindings stack)))
           :hints(("Goal" :in-theory (enable stack$a-bindings
                                             major-frame-ev)
                   :expand ((major-stack-ev stack env))))))

  (local (defthm gl-object-alist-ev-of-stack$a-bindings
           (equal (gl-object-alist-ev (stack$a-bindings stack) env)
                  (double-rewrite (stack$a-bindings (major-stack-ev stack env))))
           :hints(("Goal" :in-theory (enable major-frame-ev
                                             stack$a-bindings)
                   :expand ((major-stack-ev stack env))
                   :do-not-induct t))))

  (defcong stack-equiv-except-top-bindings equal (stack$a-top-scratch stack) 1
    :hints(("Goal" :in-theory (enable stack$a-top-scratch
                                      stack-equiv-except-top-bindings))))

  
  (defcong stack-equiv-except-top-bindings equal (stack$a-minor-bindings stack) 1
    :hints(("Goal" :in-theory (enable stack$a-minor-bindings
                                      stack-equiv-except-top-bindings))))

  (local (Defthm gobj-bfr-eval-of-scratchobj-bfr->val
           (implies (double-rewrite (scratchobj-case obj :bfr))
                    (equal (gobj-bfr-eval (scratchobj-bfr->val obj) env)
                           (scratchobj-bfr->val (scratchobj-ev obj env))))
           :hints(("Goal" :in-theory (enable scratchobj-ev)))))

  (local (Defthm bfr-eval-of-scratchobj-bfr->val
           (implies (double-rewrite (scratchobj-case obj :bfr))
                    (equal (bfr-eval (scratchobj-bfr->val obj) (gl-env->bfr-vals env))
                           (scratchobj-bfr->val (scratchobj-ev obj env))))
           :hints(("Goal" :in-theory (enable scratchobj-ev gobj-bfr-eval)))))

  

  (defthm gobj-bfr-eval-of-boolean
    (implies (booleanp x)
             (equal (gobj-bfr-eval x env) x))
    :hints(("Goal" :in-theory (enable gobj-bfr-eval bfr-eval bfr-fix booleanp bfr->aignet-lit)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (local (defthm bfr-eval-of-gl-env->bfr-vars
           (equal (bfr-eval bfr (gl-env->bfr-vals env))
                  (gobj-bfr-eval bfr env))
           :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

  (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval
                             if* cons-equal)))

  (local (in-theory (enable fgl-apply)))

  (local (defthm not-not-under-iff*
           (iff* (not (not x)) x)
           :hints(("Goal" :in-theory (enable not)))))

  (local (defthm cons-of-if*
           (equal (cons (if* test a b) (if* test c d))
                  (if* test (cons a c) (cons b d)))
           :hints(("Goal" :in-theory (enable if*)))))

  (local (defthm if*-of-known
           (and (implies test
                         (equal (if* test a b) a))
                (equal (if* nil a b) b))
           :hints(("Goal" :in-theory (enable if*)))))

  

  (local (defthm fgl-object-eval-when-g-ite-if*
           (implies (gl-object-case x :g-ite)
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


  (def-updater-independence-thm stack-bindings-extension-p-of-interp-st-updater-independence
    (implies (and (stack-bindings-extension-p (major-stack-ev (interp-st->stack new) env (interp-st->logicman new))
                                              (major-stack-ev (interp-st->stack old) env (interp-st->logicman old)))
                  (stack-bindings-extension-p (major-stack-ev (interp-st->stack old) env (interp-st->logicman old))
                                              other))
             (stack-bindings-extension-p (major-stack-ev (interp-st->stack new) env
                                                         (interp-st->logicman new))
                                         other))
    :hints(("Goal" :in-theory (enable stack-bindings-extension-p-transitive))))

  (defthm stack$a-bindings-of-stack$a-push-scratch
    (equal (stack$a-bindings (stack$a-push-scratch obj stack))
           (stack$a-bindings stack))
    :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-push-scratch))))

  (defthm stack$a-bindings-of-stack$a-pop-scratch
    (equal (stack$a-bindings (stack$a-pop-scratch stack))
           (stack$a-bindings stack))
    :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-pop-scratch))))

  ;; (with-output
  ;;   :off (event prove)
  ;;   :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  ;;   (std::defret-mutual-generate
  ;;     ;; (std::defret-generate <fn>-unreachable-cond
  ;;     ;;   :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
  ;;     ;;                 ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
  ;;     ;;                 ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
  ;;     ;;                 (interp-st                     (interp-st-bfrs-ok interp-st))
  ;;     ;;                 ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
  ;;     ;;                 (state                         (fgl-ev-meta-extract-global-facts :state state0)))
  ;;     ;;   :rules ((t (:add-concl (implies (and (not (interp-st->errmsg interp-st))
  ;;     ;;                                        (interp-st-bvar-db-ok new-interp-st env)
  ;;     ;;                                        (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;     ;;                                                                (interp-st->pathcond interp-st)
  ;;     ;;                                                                (interp-st->logicman interp-st))
  ;;     ;;                                        (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;     ;;                                                                (interp-st->constraint interp-st)
  ;;     ;;                                                                (interp-st->logicman interp-st)))
  ;;     ;;                                   (not (equal (interp-st->errmsg new-interp-st) :unreachable))))
  ;;     ;;              ;; (:add-keyword
  ;;     ;;              ;;  :hints ('(:do-not-induct t)
  ;;     ;;              ;;          (let ((flag (find-flag-is-hyp clause)))
  ;;     ;;              ;;            (and flag
  ;;     ;;              ;;                 (prog2$ (cw "unreachable-cond flag: ~x0~%" flag)
  ;;     ;;              ;;                         '(:no-op t))))))
  ;;     ;;              )
      
  ;;     ;;         ((:fnname gl-rewrite-try-rules)
  ;;     ;;          (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))
  ;;     ;;         ((:fnname gl-interp-add-constraints-for-substs)
  ;;     ;;          (:add-hyp (not (pathcond-enabledp (interp-st->pathcond interp-st)))))))
  ;;     ;; (std::defret-generate <fn>-constraint-preserved
  ;;     ;;   :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
  ;;     ;;                 ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
  ;;     ;;                 ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
  ;;     ;;                 (interp-st                     (interp-st-bfrs-ok interp-st))
  ;;     ;;                 ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
  ;;     ;;                 (state                         (fgl-ev-meta-extract-global-facts :state state)))
  ;;     ;;   :rules ((t (:add-concl (implies (and (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;     ;;                                                                (interp-st->constraint interp-st)
  ;;     ;;                                                                (interp-st->logicman interp-st))
  ;;     ;;                                        (interp-st-bvar-db-ok new-interp-st env))
  ;;     ;;                                   (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;     ;;                                                           (interp-st->constraint new-interp-st)
  ;;     ;;                                                           (interp-st->logicman new-interp-st))))
  ;;     ;;              ;; (:add-keyword
  ;;     ;;              ;;  :hints ('(:do-not-induct t)
  ;;     ;;              ;;          (let ((flag (find-flag-is-hyp clause)))
  ;;     ;;              ;;            (and flag
  ;;     ;;              ;;                 (prog2$ (cw "constraint-preserved flag: ~x0~%" flag)
  ;;     ;;              ;;                         '(:no-op t))))))
  ;;     ;;              )
  ;;     ;;         ((:fnname gl-rewrite-try-rules)
  ;;     ;;          (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))
  ;;     ;;         ((:fnname gl-interp-add-constraints-for-substs)
  ;;     ;;          (:add-hyp (not (pathcond-enabledp (interp-st->pathcond interp-st)))))))
  ;;     (std::defret-generate <fn>-correct
  ;;       :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
  ;;                     ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
  ;;                     ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
  ;;                     (interp-st                     (interp-st-bfrs-ok interp-st))
  ;;                     ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
  ;;                     (state                         (fgl-ev-meta-extract-global-facts :state state)))
  ;;       :rules ((t (:add-hyp (and (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;                                                         (interp-st->constraint interp-st)
  ;;                                                         (interp-st->logicman interp-st))
  ;;                                 (interp-st-bvar-db-ok new-interp-st env)))
                   
  ;;                  (:add-bindings
  ;;                   ((new-logicman (interp-st->logicman new-interp-st))
  ;;                    (logicman (interp-st->logicman interp-st))
  ;;                    (new-stack (interp-st->stack new-interp-st))
  ;;                    (stack (interp-st->stack interp-st))
  ;;                    (major-alist (fgl-object-alist-eval (stack$a-bindings new-stack) env new-logicman))
  ;;                    (minor-alist (fgl-object-alist-eval (stack$a-minor-bindings stack) env logicman))
  ;;                    (?eval-alist (append minor-alist major-alist)))))

  ;;               ((:fnname gl-rewrite-try-rules)
  ;;                (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))

  ;;               ((:fnname gl-interp-add-constraints-for-substs)
  ;;                (:push-hyp (not (pathcond-enabledp (interp-st->pathcond interp-st)))))

  ;;               (t (:add-concl (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;                                                      (interp-st->constraint new-interp-st)
  ;;                                                      new-logicman)))
  ;;               (t
  ;;                (:push-hyp
  ;;                 (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;                                         (interp-st->pathcond interp-st)
  ;;                                         logicman)))
                
  ;;               ;; ((:fnname gl-interp-add-constraints-for-substs)
  ;;               ;;  (:pop-hyp))
  ;;               (t (:push-hyp (not (interp-st->errmsg interp-st))))


  ;;               (t (:add-concl ;; (implies (and (not (interp-st->errmsg interp-st))
  ;;                   ;;               (logicman-pathcond-eval (gl-env->bfr-vals env)
  ;;                   ;;                                       (interp-st->pathcond interp-st)
  ;;                   ;;                                       logicman))
  ;;                   (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  ;;               (t (:pop-hyp)
  ;;                  (:push-hyp
  ;;                   (not (interp-st->errmsg new-interp-st))))
                

                
  ;;               ((:fnname gl-interp-test)
  ;;                (:add-concl
  ;;                 ;; (iff* (gobj-bfr-eval xbfr env new-logicman)
  ;;                 ;;       (fgl-ev x eval-alist))
  ;;                 (iff-forall-extensions
  ;;                  (gobj-bfr-eval xbfr env new-logicman) x eval-alist)))
  ;;               ((or (:fnname gl-interp-term-equivs)
  ;;                    (:fnname gl-interp-term)
  ;;                    (:fnname gl-interp-time$)
  ;;                    (:fnname gl-interp-return-last))
  ;;                (:add-concl
  ;;                 (fgl-ev-context-equiv-forall-extensions
  ;;                  (interp-st->equiv-contexts interp-st)
  ;;                  (fgl-object-eval xobj env new-logicman)
  ;;                  x eval-alist)))
  ;;               ((:fnname gl-interp-arglist)
  ;;                (:add-concl
  ;;                 ;; (equal (fgl-objectlist-eval arg-objs env new-logicman)
  ;;                 ;;        (fgl-ev-list x eval-alist))
  ;;                 (implies (equal (interp-st->equiv-contexts interp-st) nil)
  ;;                          (equal-list-forall-extensions
  ;;                           (fgl-objectlist-eval arg-objs env new-logicman)
  ;;                           args eval-alist))))
  ;;               ((:fnname gl-interp-bindinglist)
  ;;                (:add-concl
  ;;                 ;; (equal (fgl-object-alist-eval (stack$a-minor-bindings new-stack) env new-logicman)
  ;;                 ;;        (fgl-ev-bindinglist-minmaj bindings
  ;;                 ;;                                   minor-alist
  ;;                 ;;                                   major-alist))
  ;;                 (implies (equal (interp-st->equiv-contexts interp-st) nil)
  ;;                          (equal-bindinglist-forall-extensions
  ;;                           (fgl-object-alist-eval (stack$a-minor-bindings new-stack) env new-logicman)
  ;;                           bindings minor-alist major-alist))))
  ;;               ((:fnname gl-interp-fncall)
  ;;                (:add-concl
  ;;                 (equal (fgl-ev-context-fix
  ;;                         (interp-st->equiv-contexts interp-st)
  ;;                         (fgl-object-eval ans env new-logicman))
  ;;                        (fgl-ev-context-fix
  ;;                         (interp-st->equiv-contexts interp-st)
  ;;                         (fgl-ev (cons (pseudo-fnsym-fix fn)
  ;;                                       (kwote-lst
  ;;                                        (fgl-objectlist-eval args env logicman)))
  ;;                                 nil)))))
  ;;               ((or (:fnname gl-interp-fn-definition)
  ;;                    (:fnname gl-rewrite-fncall))
  ;;                (:add-concl
  ;;                 (implies successp
  ;;                          (equal (fgl-ev-context-fix
  ;;                                  (interp-st->equiv-contexts interp-st)
  ;;                                  (fgl-object-eval ans env new-logicman))
  ;;                                 (fgl-ev-context-fix
  ;;                                  (interp-st->equiv-contexts interp-st)
  ;;                                  (fgl-ev (cons (pseudo-fnsym-fix fn)
  ;;                                                (kwote-lst
  ;;                                                 (fgl-objectlist-eval args env logicman)))
  ;;                                          nil))))))
  ;;               ((:fnname gl-rewrite-try-rule)
  ;;                (:add-concl
  ;;                 (implies (and successp
  ;;                               (fgl-ev-theoremp (acl2::rewrite-rule-term rule)))
  ;;                          (fgl-ev-context-equiv
  ;;                           (interp-st->equiv-contexts interp-st)
  ;;                           (fgl-object-eval ans env new-logicman)
  ;;                           (fgl-ev (cons (pseudo-fnsym-fix fn)
  ;;                                         (kwote-lst
  ;;                                          (fgl-objectlist-eval args env logicman)))
  ;;                                   nil)))))

  ;;               ((:fnname gl-rewrite-try-rules)
  ;;                (:add-concl
  ;;                 (implies (and successp
  ;;                               (fgl-ev-good-rewrite-rulesp rules))
  ;;                          (equal (fgl-ev-context-fix
  ;;                                  (interp-st->equiv-contexts interp-st)
  ;;                                  (fgl-object-eval ans env new-logicman))
  ;;                                 (fgl-ev-context-fix
  ;;                                  (interp-st->equiv-contexts interp-st)
  ;;                                  (fgl-ev (cons (pseudo-fnsym-fix fn)
  ;;                                                (kwote-lst
  ;;                                                 (fgl-objectlist-eval
  ;;                                                  (interp-st-top-scratch-gl-objlist interp-st)
  ;;                                                  env logicman)))
  ;;                                          nil))))))
  ;;               ((:fnname gl-rewrite-relieve-hyps)
  ;;                (:add-concl
  ;;                 (implies (and successp
  ;;                               (equal (interp-st->equiv-contexts interp-st) '(iff)))
  ;;                          (iff-forall-extensions
  ;;                           t (conjoin hyps) eval-alist))))
  ;;               ((:fnname gl-rewrite-relieve-hyp)
  ;;                (:add-concl
  ;;                 (implies (and successp
  ;;                               (equal (interp-st->equiv-contexts interp-st) '(iff)))
  ;;                          (iff-forall-extensions
  ;;                           t hyp eval-alist))))
  ;;               ((or (:fnname gl-interp-if/or)
  ;;                    (:fnname gl-interp-if))
  ;;                (:add-concl
  ;;                 (fgl-ev-context-equiv-forall-extensions
  ;;                  (interp-st->equiv-contexts interp-st)
  ;;                  (fgl-object-eval ans env new-logicman)
  ;;                  (pseudo-term-fncall 'if (list test then else))
  ;;                  eval-alist)))
  ;;               ((:fnname gl-interp-or)
  ;;                (:add-concl
  ;;                 (fgl-ev-context-equiv-forall-extensions
  ;;                  (interp-st->equiv-contexts interp-st)
  ;;                  (fgl-object-eval ans env new-logicman)
  ;;                  (pseudo-term-fncall 'if (list test test else))
  ;;                  eval-alist)))
  ;;               ((:fnname gl-maybe-interp)
  ;;                (:add-concl
  ;;                 (implies (gobj-bfr-eval test env logicman)
  ;;                          (and (fgl-ev-context-equiv-forall-extensions
  ;;                                (interp-st->equiv-contexts interp-st)
  ;;                                (fgl-object-eval ans env new-logicman)
  ;;                                x
  ;;                                eval-alist)
  ;;                               (not unreachable)))))
  ;;               ((:fnname gl-interp-maybe-simplify-if-test)
  ;;                (:add-concl
  ;;                 (implies (gobj-bfr-eval test env logicman)
  ;;                          (and (iff* (gobj-bfr-eval xbfr env new-logicman)
  ;;                                     (fgl-object-eval xobj env logicman))
  ;;                               (not unreachable)))))
  ;;               ((:fnname gl-interp-simplify-if-test)
  ;;                (:add-concl
  ;;                 (iff* (gobj-bfr-eval xbfr env new-logicman)
  ;;                       (fgl-object-eval xobj env logicman))))
  ;;               ((:fnname gl-interp-simplify-if-test-ite)
  ;;                (:add-concl
  ;;                 (implies (gl-object-case xobj :g-ite)
  ;;                          (iff* (gobj-bfr-eval xbfr env new-logicman)
  ;;                                (fgl-object-eval xobj env logicman)))))
  ;;               ((:fnname gl-interp-simplify-if-test-fncall)
  ;;                (:add-concl
  ;;                 (implies (gl-object-case xobj :g-apply)
  ;;                          (iff* (gobj-bfr-eval xbfr env new-logicman)
  ;;                                (fgl-object-eval xobj env logicman)))))
  ;;               ((or (:fnname gl-interp-merge-branches)
  ;;                    (:fnname gl-interp-merge-branches-rewrite)
  ;;                    (:fnname gl-interp-merge-branch-subterms))
  ;;                (:add-concl
  ;;                 (equal (fgl-ev-context-fix
  ;;                         (interp-st->equiv-contexts interp-st)
  ;;                         (fgl-object-eval ans env new-logicman))
  ;;                        (fgl-ev-context-fix
  ;;                         (interp-st->equiv-contexts interp-st)
  ;;                         (if* (gobj-bfr-eval testbfr env logicman)
  ;;                              (fgl-object-eval thenval env logicman)
  ;;                              (fgl-object-eval elseval env logicman)))))
  ;;                (:add-keyword :hints ((and stable-under-simplificationp
  ;;                                           '(:in-theory (enable if*))))))
  ;;               ((:fnname gl-interp-merge-branch-args)
  ;;                (:add-concl
  ;;                 (implies (and (not (interp-st->equiv-contexts interp-st))
  ;;                               (equal (len thenargs) (len elseargs)))
  ;;                          (equal (fgl-objectlist-eval args env new-logicman)
  ;;                                 (if* (gobj-bfr-eval testbfr env logicman)
  ;;                                      (fgl-objectlist-eval thenargs env logicman)
  ;;                                      (fgl-objectlist-eval elseargs env logicman))))))))
  ;;     :hints ((fgl-interp-default-hint 'gl-interp-term id nil world))
  ;;             ;; '(:expand (:lambdas)))
  ;;     ;; (prog2$ (cw "flag: ~x0~%" flag)
  ;;     ;;         '(:do-not '(generalize) :do-not-induct t))))
  ;;     ;; (and stable-under-simplificationp
  ;;     ;;              '(:in-theory (enable bfr-listp-when-not-member-witness)))
      
  ;;     :mutual-recursion gl-interp))


  (make-event
   (if (and (boundp-global 'gl-interp-term-subgoals state)
            (@ gl-interp-term-subgoals))
       '(value-triple :skipping-subgoal-generation)
     '(progn
        (make-event 
         (b* ((state (f-put-global 'gl-interp-term-subgoals nil state)))
           (value '(value-triple :invisible))))
        (make-event
         '(:or
           (with-output
             :off (event prove)
             :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
             (std::defret-mutual-generate
               ;; (std::defret-generate <fn>-unreachable-cond
               ;;   :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
               ;;                 ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
               ;;                 ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
               ;;                 (interp-st                     (interp-st-bfrs-ok interp-st))
               ;;                 ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
               ;;                 (state                         (fgl-ev-meta-extract-global-facts :state state0)))
               ;;   :rules ((t (:add-concl (implies (and (not (interp-st->errmsg interp-st))
               ;;                                        (interp-st-bvar-db-ok new-interp-st env)
               ;;                                        (logicman-pathcond-eval (gl-env->bfr-vals env)
               ;;                                                                (interp-st->pathcond interp-st)
               ;;                                                                (interp-st->logicman interp-st))
               ;;                                        (logicman-pathcond-eval (gl-env->bfr-vals env)
               ;;                                                                (interp-st->constraint interp-st)
               ;;                                                                (interp-st->logicman interp-st)))
               ;;                                   (not (equal (interp-st->errmsg new-interp-st) :unreachable))))
               ;;              ;; (:add-keyword
               ;;              ;;  :hints ('(:do-not-induct t)
               ;;              ;;          (let ((flag (find-flag-is-hyp clause)))
               ;;              ;;            (and flag
               ;;              ;;                 (prog2$ (cw "unreachable-cond flag: ~x0~%" flag)
               ;;              ;;                         '(:no-op t))))))
               ;;              )
               
               ;;         ((:fnname gl-rewrite-try-rules)
               ;;          (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))
               ;;         ((:fnname gl-interp-add-constraints-for-substs)
               ;;          (:add-hyp (not (pathcond-enabledp (interp-st->pathcond interp-st)))))))
               ;; (std::defret-generate <fn>-constraint-preserved
               ;;   :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
               ;;                 ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
               ;;                 ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
               ;;                 (interp-st                     (interp-st-bfrs-ok interp-st))
               ;;                 ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
               ;;                 (state                         (fgl-ev-meta-extract-global-facts :state state)))
               ;;   :rules ((t (:add-concl (implies (and (logicman-pathcond-eval (gl-env->bfr-vals env)
               ;;                                                                (interp-st->constraint interp-st)
               ;;                                                                (interp-st->logicman interp-st))
               ;;                                        (interp-st-bvar-db-ok new-interp-st env))
               ;;                                   (logicman-pathcond-eval (gl-env->bfr-vals env)
               ;;                                                           (interp-st->constraint new-interp-st)
               ;;                                                           (interp-st->logicman new-interp-st))))
               ;;              ;; (:add-keyword
               ;;              ;;  :hints ('(:do-not-induct t)
               ;;              ;;          (let ((flag (find-flag-is-hyp clause)))
               ;;              ;;            (and flag
               ;;              ;;                 (prog2$ (cw "constraint-preserved flag: ~x0~%" flag)
               ;;              ;;                         '(:no-op t))))))
               ;;              )
               ;;         ((:fnname gl-rewrite-try-rules)
               ;;          (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))
               ;;         ((:fnname gl-interp-add-constraints-for-substs)
               ;;          (:add-hyp (not (pathcond-enabledp (interp-st->pathcond interp-st)))))))
               (std::defret-generate <fn>-correct
                 :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                               ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                               ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                               (interp-st                     (interp-st-bfrs-ok interp-st))
                               ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x)))
                               (state                         (fgl-ev-meta-extract-global-facts :state state)))
                 :rules ((t (:add-hyp (and (logicman-pathcond-eval (gl-env->bfr-vals env)
                                                                   (interp-st->constraint interp-st)
                                                                   (interp-st->logicman interp-st))
                                           (interp-st-bvar-db-ok new-interp-st env)))
                            
                            (:add-bindings
                             ((new-logicman (interp-st->logicman new-interp-st))
                              (logicman (interp-st->logicman interp-st))
                              (new-stack (interp-st->stack new-interp-st))
                              (stack (interp-st->stack interp-st))
                              (major-alist (fgl-object-alist-eval (stack$a-bindings new-stack) env new-logicman))
                              (minor-alist (fgl-object-alist-eval (stack$a-minor-bindings stack) env logicman))
                              (?eval-alist (append minor-alist major-alist)))))

                         ((:fnname gl-rewrite-try-rules)
                          (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :gl-objlist)))

                         ((:fnname gl-interp-add-constraints-for-substs)
                          (:push-hyp (not (pathcond-enabledp (interp-st->pathcond interp-st)))))

                         (t (:add-concl (logicman-pathcond-eval (gl-env->bfr-vals env)
                                                                (interp-st->constraint new-interp-st)
                                                                new-logicman)))
                         (t
                          (:push-hyp
                           (logicman-pathcond-eval (gl-env->bfr-vals env)
                                                   (interp-st->pathcond interp-st)
                                                   logicman)))
                         
                         ;; ((:fnname gl-interp-add-constraints-for-substs)
                         ;;  (:pop-hyp))
                         (t (:push-hyp (not (interp-st->errmsg interp-st))))


                         (t (:add-concl ;; (implies (and (not (interp-st->errmsg interp-st))
                             ;;               (logicman-pathcond-eval (gl-env->bfr-vals env)
                             ;;                                       (interp-st->pathcond interp-st)
                             ;;                                       logicman))
                             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

                         (t (:pop-hyp)
                            (:push-hyp
                             (not (interp-st->errmsg new-interp-st))))
                         

                         
                         ((:fnname gl-interp-test)
                          (:add-concl
                           ;; (iff* (gobj-bfr-eval xbfr env new-logicman)
                           ;;       (fgl-ev x eval-alist))
                           (iff-forall-extensions
                            (gobj-bfr-eval xbfr env new-logicman) x eval-alist)))
                         ((or (:fnname gl-interp-term-equivs)
                              (:fnname gl-interp-term)
                              (:fnname gl-interp-time$)
                              (:fnname gl-interp-return-last))
                          (:add-concl
                           (fgl-ev-context-equiv-forall-extensions
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval xobj env new-logicman)
                            x eval-alist)))
                         ((:fnname gl-interp-arglist)
                          (:add-concl
                           ;; (equal (fgl-objectlist-eval arg-objs env new-logicman)
                           ;;        (fgl-ev-list x eval-alist))
                           (implies (equal (interp-st->equiv-contexts interp-st) nil)
                                    (equal-list-forall-extensions
                                     (fgl-objectlist-eval arg-objs env new-logicman)
                                     args eval-alist))))
                         ((:fnname gl-interp-bindinglist)
                          (:add-concl
                           ;; (equal (fgl-object-alist-eval (stack$a-minor-bindings new-stack) env new-logicman)
                           ;;        (fgl-ev-bindinglist-minmaj bindings
                           ;;                                   minor-alist
                           ;;                                   major-alist))
                           (implies (equal (interp-st->equiv-contexts interp-st) nil)
                                    (equal-bindinglist-forall-extensions
                                     (fgl-object-alist-eval (stack$a-minor-bindings new-stack) env new-logicman)
                                     bindings minor-alist major-alist))))
                         ((:fnname gl-interp-fncall)
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
                         ((or (:fnname gl-interp-fn-definition)
                              (:fnname gl-rewrite-fncall))
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
                         ((:fnname gl-rewrite-try-rule)
                          (:add-concl
                           (implies (and successp
                                         (fgl-ev-theoremp (acl2::rewrite-rule-term rule)))
                                    (fgl-ev-context-equiv
                                     (interp-st->equiv-contexts interp-st)
                                     (fgl-object-eval ans env new-logicman)
                                     (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                   (kwote-lst
                                                    (fgl-objectlist-eval args env logicman)))
                                             nil)))))

                         ((:fnname gl-rewrite-try-rules)
                          (:add-concl
                           (implies (and successp
                                         (fgl-ev-good-rewrite-rulesp rules))
                                    (equal (fgl-ev-context-fix
                                            (interp-st->equiv-contexts interp-st)
                                            (fgl-object-eval ans env new-logicman))
                                           (fgl-ev-context-fix
                                            (interp-st->equiv-contexts interp-st)
                                            (fgl-ev (cons (pseudo-fnsym-fix fn)
                                                          (kwote-lst
                                                           (fgl-objectlist-eval
                                                            (interp-st-top-scratch-gl-objlist interp-st)
                                                            env logicman)))
                                                    nil))))))
                         ((:fnname gl-rewrite-relieve-hyps)
                          (:add-concl
                           (implies (and successp
                                         (equal (interp-st->equiv-contexts interp-st) '(iff)))
                                    (iff-forall-extensions
                                     t (conjoin hyps) eval-alist))))
                         ((:fnname gl-rewrite-relieve-hyp)
                          (:add-concl
                           (implies (and successp
                                         (equal (interp-st->equiv-contexts interp-st) '(iff)))
                                    (iff-forall-extensions
                                     t hyp eval-alist))))
                         ((or (:fnname gl-interp-if/or)
                              (:fnname gl-interp-if))
                          (:add-concl
                           (fgl-ev-context-equiv-forall-extensions
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (pseudo-term-fncall 'if (list test then else))
                            eval-alist)))
                         ((:fnname gl-interp-or)
                          (:add-concl
                           (fgl-ev-context-equiv-forall-extensions
                            (interp-st->equiv-contexts interp-st)
                            (fgl-object-eval ans env new-logicman)
                            (pseudo-term-fncall 'if (list test test else))
                            eval-alist)))
                         ((:fnname gl-maybe-interp)
                          (:add-concl
                           (implies (gobj-bfr-eval test env logicman)
                                    (and (fgl-ev-context-equiv-forall-extensions
                                          (interp-st->equiv-contexts interp-st)
                                          (fgl-object-eval ans env new-logicman)
                                          x
                                          eval-alist)
                                         (not unreachable)))))
                         ((:fnname gl-interp-maybe-simplify-if-test)
                          (:add-concl
                           (implies (gobj-bfr-eval test env logicman)
                                    (and (iff* (gobj-bfr-eval xbfr env new-logicman)
                                               (fgl-object-eval xobj env logicman))
                                         (not unreachable)))))
                         ((:fnname gl-interp-simplify-if-test)
                          (:add-concl
                           (iff* (gobj-bfr-eval xbfr env new-logicman)
                                 (fgl-object-eval xobj env logicman))))
                         ((:fnname gl-interp-simplify-if-test-ite)
                          (:add-concl
                           (implies (gl-object-case xobj :g-ite)
                                    (iff* (gobj-bfr-eval xbfr env new-logicman)
                                          (fgl-object-eval xobj env logicman)))))
                         ((:fnname gl-interp-simplify-if-test-fncall)
                          (:add-concl
                           (implies (gl-object-case xobj :g-apply)
                                    (iff* (gobj-bfr-eval xbfr env new-logicman)
                                          (fgl-object-eval xobj env logicman)))))
                         ((or (:fnname gl-interp-merge-branches)
                              (:fnname gl-interp-merge-branches-rewrite)
                              (:fnname gl-interp-merge-branch-subterms))
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
                         ((:fnname gl-interp-merge-branch-args)
                          (:add-concl
                           (implies (and (not (interp-st->equiv-contexts interp-st))
                                         (equal (len thenargs) (len elseargs)))
                                    (equal (fgl-objectlist-eval args env new-logicman)
                                           (if* (gobj-bfr-eval testbfr env logicman)
                                                (fgl-objectlist-eval thenargs env logicman)
                                                (fgl-objectlist-eval elseargs env logicman))))))))
               :hints ((fgl-interp-default-hint 'gl-interp-term id nil world)
                       ;; '(:expand (:lambdas))
                       (b* ((flag (find-flag-is-hyp clause))
                            ((unless flag) (value nil))
                            (state (f-put-global 'gl-interp-term-subgoals
                                                 (cons clause (@ gl-interp-term-subgoals))
                                                 state)))
                         (value '(:by nil))))
               ;; (prog2$ (cw "flag: ~x0~%" flag)
               ;;         '(:do-not '(generalize) :do-not-induct t))))
               ;; (and stable-under-simplificationp
               ;;              '(:in-theory (enable bfr-listp-when-not-member-witness)))
               
               :mutual-recursion gl-interp))
           (value-triple :goals-saved))))))


  ;; (local
  ;;  (defun prettyify-clause-list (clauses let*-abstractionp wrld)
  ;;    (declare (xargs :mode :program))
  ;;    (if (atom clauses)
  ;;        nil
  ;;      (cons (prettyify-clause (car clauses) let*-abstractionp wrld)
  ;;            (prettyify-clause-list (cdr clauses) let*-abstractionp wrld)))))

  (local (defun gl-interp-clause-to-defthm (clause base-name let*-absp flag-index-alist hints wrld)
           (declare (xargs :mode :program))
           (b* ((flag (find-flag-is-hyp clause))
                (goal (acl2::prettyify-clause clause let*-absp wrld))
                ((unless flag)
                 (er hard? 'gl-interp-clause-to-defthm
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
                         (table gl-interp-clauses-table ',clause ',thmname))
                 flag-index-alist))))

  (local
   (defun gl-interp-clauses-to-defthms (clauses base-name let*-absp flag-index-alist hints wrld)
     (declare (xargs :mode :program))
     (b* (((when (atom clauses))
           nil)
          ((mv thm flag-index-alist)
           (gl-interp-clause-to-defthm (car clauses) base-name let*-absp flag-index-alist hints wrld)))
       (cons thm
             (gl-interp-clauses-to-defthms (cdr clauses) base-name let*-absp flag-index-alist hints wrld)))))

  (set-ignore-ok t)

  ;; (set-default-hints
  ;;  '((and stable-under-simplificationp
  ;;         '(:in-theory (enable if*)
  ;;           :do-not-induct t))))

  (with-output
    :off (event prove)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (make-event
     `(acl2::run-events-stop-on-failure
       ,(gl-interp-clauses-to-defthms
         (@ gl-interp-term-subgoals)
         'gl-interp-correct
         t nil
         '(("goal" :do-not-induct t :do-not '(generalize))
           (and stable-under-simplificationp
                (or (eq (find-flag-is-hyp clause) 'gl-interp-merge-branches)
                    (eq (find-flag-is-hyp clause) 'gl-interp-merge-branch-subterms))
                '(:in-theory (enable if*))))
         (w state)))))
       
  ;; (i-am-here)
  )









