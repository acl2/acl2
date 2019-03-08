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
(local (include-book "tools/trivial-ancestors-check" :dir :system))


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
  (b* ((constraint-db (interp-st->constraint-db interp-st))
       (constraint-insts (interp-st->constraint-inst-stack interp-st))
       (thenvals (interp-st->thenval-stack interp-st))
       (elsevals (interp-st->elseval-stack interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (bvar-db (interp-st->bvar-db interp-st))
                (stack (interp-st->stack interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (ok)
               (b* ((bfrstate (logicman->bfrstate)))
                 (and (bfr-listp (major-stack-bfrlist (stack-extract stack)))
                      (bfr-listp (constraint-db-bfrlist constraint-db))
                      (bfr-listp (constraint-instancelist-bfrlist constraint-insts))
                      (bfr-listp (gl-objectlist-bfrlist thenvals))
                      (bfr-listp (gl-objectlist-bfrlist elsevals))
                      (ec-call (logicman-pathcond-p-fn pathcond logicman))
                      (ec-call (logicman-pathcond-p-fn constraint-pathcond logicman))
                      (not (consp (bvar-db-bfrlist bvar-db)))
                      (logicman-check-nvars (next-bvar bvar-db) logicman)))
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
                    (bfr-listp (gl-objectlist-bfrlist (interp-st->thenval-stack interp-st)))
                    (bfr-listp (gl-objectlist-bfrlist (interp-st->elseval-stack interp-st)))
                    (implies (gl-objectlist-p (interp-st->thenval-stack interp-st))
                             (gl-bfr-objectlist-p (interp-st->thenval-stack interp-st)))
                    (implies (gl-objectlist-p (interp-st->elseval-stack interp-st))
                             (gl-bfr-objectlist-p (interp-st->elseval-stack interp-st)))
                    (bfr-listp (constraint-instancelist-bfrlist (interp-st->constraint-inst-stack interp-st)))
                    (interp-st-nvars-ok interp-st)
                    (logicman-check-nvars (next-bvar$a (interp-st->bvar-db interp-st))
                                          (interp-st->logicman interp-st)))))
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
                         (interp-st-get :bvar-db old))
                  (equal (interp-st-get :constraint new)
                         (interp-st-get :constraint old))
                  (equal (interp-st-get :constraint-inst-stack new)
                         (interp-st-get :constraint-inst-stack old))
                  (equal (interp-st-get :thenval-stack new)
                         (interp-st-get :thenval-stack old))
                  (equal (interp-st-get :elseval-stack new)
                         (interp-st-get :elseval-stack old)))
             (equal (interp-st-bfrs-ok new)
                    (interp-st-bfrs-ok old))))


  (defthm interp-st-bfrs-ok-of-logicman-extension
    (implies (and (interp-st-bfrs-ok interp-st)
                  (logicman-extension-p new-logicman (interp-st->logicman interp-st))
                  (equal (bfr-nvars new-logicman) (bfr-nvars (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->logicman new-logicman interp-st)))
    :hints(("Goal" :in-theory (enable logicman-check-nvars))))

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
                  (logicman-check-nvars (next-bvar new-bvar-db) (interp-st->logicman interp-st)))
             (interp-st-bfrs-ok (update-interp-st->bvar-db new-bvar-db interp-st))))

  (defthm interp-st-bfrs-ok-of-update-constraint-inst-stack
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (constraint-instancelist-bfrlist new-constraint-stack)
                             (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->constraint-inst-stack new-constraint-stack interp-st))))

  (defthm interp-st-bfrs-ok-of-update-thenval-stack
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (gl-objectlist-bfrlist new-thenval-stack)
                             (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->thenval-stack new-thenval-stack interp-st))))

  (defthm interp-st-bfrs-ok-of-update-elseval-stack
    (implies (And (interp-st-bfrs-ok interp-st)
                  (bfr-listp (gl-objectlist-bfrlist new-elseval-stack)
                             (logicman->bfrstate (interp-st->logicman interp-st))))
             (interp-st-bfrs-ok (update-interp-st->elseval-stack new-elseval-stack interp-st))))

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

(local (define bfr-listp-witness (x (bfrstate bfrstate-p))
         (if (atom x)
             'not-a-bfr
           (if (bfr-p (car x))
               (bfr-listp-witness (cdr x) bfrstate)
             (car x)))
         ///
         (local (defthm not-a-bfr-is-not-a-bfr
                  (not (bfr-p 'not-a-bfr))
                  :hints(("Goal" :in-theory (enable bfr-p)))))

         (defthm bfr-listp-witness-not-bfr-p
           (not (bfr-p (bfr-listp-witness x bfrstate) bfrstate)))

         (defthmd bfr-listp-when-not-member-witness
           (implies (not (member (bfr-listp-witness x bfrstate) x))
                    (bfr-listp x bfrstate))
           :hints(("Goal" :in-theory (enable bfr-listp))))
         
         (local (defthm member-bfr-list-when-not-bfr-p
                  (implies (and (bfr-listp x bfrstate)
                                (not (bfr-p v bfrstate)))
                           (not (member v x)))))

         (defthm not-member-bfr-listp-witness-when-bfr-listp
           (implies (bfr-listp x bfrstate)
                    (not (member (bfr-listp-witness y bfrstate) x))))))


(defsection bfrlist-of-gl-object-accessors
  (local (in-theory (enable* gl-object-bfrlist-when-thms)))

  (defthm bfrlist-of-g-ite-accessors
    (implies (and (gl-object-case x :g-ite)
                  (not (member v (gl-object-bfrlist x))))
             (b* (((g-ite x)))
               (and (not (member v (gl-object-bfrlist x.test)))
                    (not (member v (gl-object-bfrlist x.then)))
                    (not (member v (gl-object-bfrlist x.else)))))))

  (defthm bfrlist-of-g-boolean-accessor
    (implies (and (gl-object-case x :g-boolean)
                  (not (member v (gl-object-bfrlist x))))
             (b* (((g-boolean x)))
               (not (equal v x.bool)))))

  (defthm bfrlist-of-g-integer-accessor
    (implies (and (gl-object-case x :g-integer)
                  (not (member v (gl-object-bfrlist x))))
             (b* (((g-integer x)))
               (not (member v x.bits)))))

  (defthm bfrlist-of-g-apply-accessor
    (implies (and (gl-object-case x :g-apply)
                  (not (member v (gl-object-bfrlist x))))
             (b* (((g-apply x)))
               (not (member v (gl-objectlist-bfrlist x.args))))))

  (defthm bfrlist-of-g-cons-accessor
    (implies (and (gl-object-case x :g-cons)
                  (not (member v (gl-object-bfrlist x))))
             (b* (((g-cons x)))
               (and (not (member v (gl-object-bfrlist x.car)))
                    (not (member v (gl-object-bfrlist x.cdr)))))))

  (defthm member-gl-objectlist-bfrlist-of-cdr
    (implies (not (member v (gl-objectlist-bfrlist x)))
             (not (member v (gl-objectlist-bfrlist (cdr x)))))
    :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist))))

  (defthm member-gl-object-bfrlist-of-car
    (implies (not (member v (gl-objectlist-bfrlist x)))
             (not (member v (gl-object-bfrlist (car x)))))
    :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist)))))



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


(define gl-interp-store-debug-info (msg obj interp-st state)
  :returns (new-state)
  (b* ((stack-obj (stobj-let ((stack (interp-st->stack interp-st)))
                             (obj)
                             (stack-extract stack)
                             obj))
       (state (f-put-global 'gl-interp-error-message msg state))
       (state (f-put-global 'gl-interp-error-debug-obj obj state))
       (state (f-put-global 'gl-interp-error-stack stack-obj state)))
    state)
  ///
  (defret w-of-<fn>
    (equal (w new-state) (w state))))

(defmacro gl-interp-error (&key msg debug-obj (nvals '1))
  `(b* ((msg ,msg)
        (debug-obj ,debug-obj)
        (state (gl-interp-store-debug-info msg debug-obj interp-st state)))
     (mv msg ,@(acl2::repeat nvals nil) interp-st state)))
  


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
        (magic-ev-fncall fn (g-concretelist-vals args) state t nil)))
    (mv (not err) (g-concrete ans)))
  ///
  (defret gl-object-bfrlist-of-<fn>
    (equal (gl-object-bfrlist ans) nil)))


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
             (equal (base-apply-ev x a) t))))



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
        (gl-interp-error :msg (gl-msg "Bad syntax-bind form: args ~x0, ~x1." synp-arg x)))
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
    (mv nil val interp-st state))
  ///
  (local (defthm bfrlist-of-interp-st-add-binding
           (implies (and (not (member v (major-stack-bfrlist stack)))
                         (not (member v (gl-object-bfrlist val))))
                    (not (member v (major-stack-bfrlist (stack$a-add-binding var val stack)))))
           :hints (("goal" :expand ((major-stack-bfrlist stack))
                    :in-theory (enable major-frame-bfrlist
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
                              (interp-st->logicman new-interp-st))))))


(define gl-interp-or-test-equiv-contexts ((contexts equiv-contextsp))
  :returns (new-contexts equiv-contextsp)
  (and (equal contexts '(iff)) '(iff)))

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

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfr-p test)
                  (interp-st-bfrs-ok interp-st))
             (interp-st-bfrs-ok new-interp-st)))

  (defret pathcond-rewind-of-<fn>
    (implies (and (not contra)
                  (equal mode (logicman->mode (interp-st->logicman interp-st))))
             (equal (pathcond-rewind mode (interp-st->pathcond new-interp-st))
                    (pathcond-fix (interp-st->pathcond interp-st))))))
             


(define interp-st-pathcond-rewind (interp-st)
  :guard (stobj-let ((pathcond (interp-st->pathcond interp-st))
                     (logicman (interp-st->logicman interp-st)))
                    (ok)
                    (< 0 (pathcond-rewind-stack-len (lbfr-mode) pathcond))
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
             (iff (base-gl-object-eval negated-arg env logicman)
                  (not (base-gl-object-eval x env logicman))))
    :hints(("Goal" :expand ((base-gl-objectlist-eval (g-apply->args x) env)
                            (base-gl-objectlist-eval (cdr (g-apply->args x)) env)
                            (base-gl-objectlist-eval (cddr (g-apply->args x)) env))
            :in-theory (enable base-apply))))

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
  


(define gl-rewrite-relieve-hyp-synp ((synp-type symbolp)
                                     (form pseudo-termp)
                                     (vars)
                                     (untrans-form)
                                     interp-st
                                     state)
  :returns (mv err successp
               new-interp-st
               new-state)
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
                      :hints(("Goal" :in-theory (enable gl-bfr-object-alist-p-implies-gl-object-alist-p))))))
  (b* ((bindings (append (interp-st-minor-bindings interp-st)
                         (interp-st-bindings interp-st)))
       ((mv ok val) (acl2::magic-ev form bindings state t t))
       ((unless ok)
        (gl-interp-error
         :msg (gl-msg "Synp error: ~x0 failed to evaluate -- translated: ~x1" untrans-form form)))
       ((when (eq synp-type 'syntaxp))
        (mv nil val interp-st state))
       ;; bind-free...
       ((unless val)
        ;; No error -- bind-free evaluated to NIL which means just don't do the rewrite.
        (mv nil nil interp-st state))
       ((unless (gl-bfr-object-alist-p val (interp-st-bfr-state)))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to a non-GL object alist: ~x1" untrans-form val)))
       (newly-bound-vars (alist-keys bindings))
       ((when (and (symbol-listp vars)
                   (not (subsetp-eq vars newly-bound-vars))))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to an alist not ~
                     containing the required vars ~x1: ~x2" untrans-form val vars)))
       ;; Consider allowing already-bound variables to be bound in the new
       ;; bindings, and just omitting them from the final bindings.  Might be
       ;; convenient in case we want to bind a variable in different places for
       ;; different cases.  
       ((when (intersectp-eq (alist-keys val) newly-bound-vars))
        (gl-interp-error
         :msg (gl-msg "Bind-free error: ~x0 evaluated to a non-GL object alist: ~x1" untrans-form val)))
       
       (interp-st (interp-st-set-bindings (append val (interp-st-bindings interp-st)) interp-st)))
    (mv nil t interp-st state))
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
             (interp-st-bfrs-ok new-interp-st))))



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


(defthm base-apply-ev-lst-of-kwote-lst
  (equal (base-apply-ev-lst (kwote-lst x) a)
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
  :returns (mv (fn pseudo-fnsym-p)
               (args gl-objectlist-p))
  (gl-object-case x
    ;; :g-boolean (mv 'bool (list (gl-object-fix x)))
    ;; :g-integer (mv 'int (list (gl-object-fix x)))
    ;; :g-concrete (mv 'concrete (list (gl-object-fix x)))
    :g-apply (mv x.fn x.args)
    :g-cons (mv 'cons (list x.car x.cdr))
    :otherwise (mv nil nil))
  ///

  (defret eval-when-gl-object-recognize-merge-fncall
    (implies fn
             (equal (base-apply-ev (cons fn
                                         (kwote-lst (base-gl-objectlist-eval args env)))
                                   a)
                    (base-gl-object-eval x env)))
    :hints(("Goal" :in-theory (enable base-apply base-gl-objectlist-eval
                                      base-apply-ev-of-fncall-args))))

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
;;              (equal (base-gl-object-eval x env)
;;                     (base-apply (gl-fncall-object->fn x)
;;                                 (base-gl-objectlist-eval args env))))
;;     :hints(("Goal" :in-theory (enable base-apply base-gl-objectlist-eval)))))

;; (defthm-base-gl-object-eval-flag
;;   (defthm base-gl-object-eval-of-gl-bfr-object-fix
;;     (equal (base-gl-object-eval (gl-bfr-object-fix x (logicman->bfrstate logicman))
;;                                 env logicman)
;;            (base-gl-object-eval x env logicman))
;;     :hints ('(:expand ((base-gl-object-eval x env logicman)
;;                        (gl-bfr-object-fix x (logicman->bfrstate logicman)))))
;;     :flag base-gl-object-eval)
;;   (defthm base-gl-objectlist-eval-of-gl-bfr-object-fix
;;     (equal (base-gl-objectlist-eval (gl-bfr-objectlist-fix x (logicman->bfrstate logicman))
;;                                 env logicman)
;;            (base-gl-objectlist-eval x env logicman))
;;     :hints ('(:expand ((base-gl-objectlist-eval x env logicman)
;;                        (gl-bfr-objectlist-fix x (logicman->bfrstate logicman)))))
;;     :flag base-gl-objectlist-eval))

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
    (equal (base-gl-object-eval obj env new-logicman)
           (if (gobj-bfr-eval test env)
               (base-gl-object-eval then env logicman)
             (base-gl-object-eval else env logicman)))
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
  :returns (mv successp
               (ans gl-object-p)
               interp-st
               state)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-integer (mv t (gl-object-fix x) interp-st state)
          :otherwise (mv nil nil interp-st state)))
    (mv nil nil interp-st state)))

(define gl-endint-primitive ((args gl-objectlist-p) interp-st state)
  :returns (mv successp
               (ans gl-object-p)
               interp-st
               state)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-boolean (mv t (g-integer (list x.bool)) interp-st state)
          :otherwise (mv nil nil interp-st state)))
    (mv nil nil interp-st state)))

(define gl-intcons-primitive ((args gl-objectlist-p) interp-st state)
  :returns (mv successp
               (ans gl-object-p)
               interp-st
               state)
  (if (eql (len args) 2)
      (b* (((list car cdr) args))
        (gl-object-case car
          :g-boolean (gl-object-case cdr
                       :g-integer (mv t (g-integer (cons car.bool cdr.bits)) interp-st state)
                       :otherwise (mv nil nil interp-st state))
          :otherwise (mv nil nil interp-st state)))
    (mv nil nil interp-st state)))

(define gl-intcar-primitive ((args gl-objectlist-p) interp-st state)
  :returns (mv successp
               (ans gl-object-p)
               interp-st
               state)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-integer (mv t (g-boolean (car x.bits)) interp-st state)
          :otherwise (mv nil nil interp-st state)))
    (mv nil nil interp-st state)))

(define gl-intcdr-primitive ((args gl-objectlist-p) interp-st state)
  :returns (mv successp
               (ans gl-object-p)
               interp-st
               state)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-integer (mv t (g-integer (cdr x.bits)) interp-st state)
          :otherwise (mv nil nil interp-st state)))
    (mv nil nil interp-st state)))

(define gl-bool-primitive ((args gl-objectlist-p) interp-st state)
  :returns (mv successp
               (ans gl-object-p)
               interp-st
               state)
  (if (eql (len args) 1)
      (let ((x (car args)))
        (gl-object-case x
          :g-boolean (mv t (gl-object-fix x) interp-st state)
          :otherwise (mv nil nil interp-st state)))
    (mv nil nil interp-st state)))

(define gl-primitive-fncall ((fn pseudo-fnsym-p)
                             (args gl-objectlist-p)
                             (dont)
                             interp-st
                             state)
  :returns (mv successp
               (ans gl-object-p)
               new-interp-st
               state)
  (if dont
      (mv nil nil interp-st state)
    (case (pseudo-fnsym-fix fn)
      (int (gl-int-primitive args interp-st state))
      ((intcons intcons*) (gl-intcons-primitive args interp-st state))
      (endint (gl-endint-primitive args interp-st state))
      (intcar (gl-intcar-primitive args interp-st state))
      (intcdr (gl-intcdr-primitive args interp-st state))
      (bool (gl-bool-primitive args interp-st state))
      (otherwise (mv nil nil interp-st state))))
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
                                      bfr-listp-when-not-member-witness)))))
                                      
      



(define glcp-unify-term/gobj-list-prefix ((pat pseudo-term-listp)
                                        (x gl-objectlist-p)
                                        (alist gl-object-alist-p))
  ;; Same as glcp-unify-term/gobj-list but doesn't complain about extra or missing elements of x.
  ;; Equivalent to (glcp-unify-term/gobj-list pat (take (len pat) x) alist).
  (b* (((when (atom pat)) (mv t (gl-object-alist-fix alist)))
       ((mv ok alist) (glcp-unify-term/gobj (car pat) (car x) alist))
       ((unless ok) (mv nil nil)))
    (glcp-unify-term/gobj-list-prefix (cdr pat) (cdr x) alist))
  ///
  (defthm glcp-unify-term/gobj-list-prefix-elim
    (equal (glcp-unify-term/gobj-list-prefix pat x alist)
           (glcp-unify-term/gobj-list pat (take (len pat) x) alist))
    :hints(("Goal" :induct (glcp-unify-term/gobj-list-prefix pat x alist)
            :expand ((:free (x) (glcp-unify-term/gobj-list pat x alist))
                     (take (len pat) x))))))



(define gl-interp-finish-simplify-if-test-ite ((test-bfr interp-st-bfr-p)
                                               (then-bfr interp-st-bfr-p)
                                               (else-bfr interp-st-bfr-p)
                                               (then-unreachable)
                                               (else-unreachable)
                                               interp-st)
  :returns (mv err
               (ite (interp-st-bfr-p ite new-interp-st))
               new-interp-st)
  (b* (((when then-unreachable)
        (if else-unreachable
            (mv :unreachable nil interp-st)
          (mv nil (interp-st-bfr-fix else-bfr) interp-st)))
       ((when else-unreachable)
        (mv nil (interp-st-bfr-fix then-bfr) interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (ite logicman)
               (bfr-ite test-bfr then-bfr else-bfr)
               (mv nil ite interp-st)))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
             (interp-st-bfrs-ok new-interp-st)))

  (defret lbfr-p-of-<fn>
    (lbfr-p ite (interp-st->logicman new-interp-st))))

















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

(defthm gl-object-alist-p-of-stack$a-bindings
  (gl-object-alist-p (stack$a-bindings stack)))

(defthm gl-object-alist-p-of-stack$a-minor-bindings
  (gl-object-alist-p (stack$a-minor-bindings stack)))

(defthm gl-object-alist-p-of-stack$a-scratch
  (gl-objectlist-p (stack$a-scratch stack)))

(local (in-theory (disable (tau-system) len default-car default-cdr
                           STACK$A-PUSH-BOOL-SCRATCH
                           STACK$A-POP-SCRATCH
                           STACK$A-PUSH-SCRATCH
                           STACK$A-POP-BOOL-SCRATCH
                           STACK$A-SET-BINDINGS
                           STACK$A-SET-DEBUG
                           STACK$A-SET-MINOR-DEBUG
                           STACK$A-SET-MINOR-BINDINGS
                           STACK$A-POP-FRAME
                           STACK$A-PUSH-FRAME
                           STACK$A-PUSH-MINOR-FRAME
                           STACK$A-BOOL-SCRATCH
                           STACK$A-POP-MINOR-FRAME
                           STACK$A-ADD-MINOR-BINDINGS
                           STACK$A-MINOR-BINDINGS
                           STACK$A-SCRATCH
                           STACK$A-BINDINGS
                           stack$a-pushlist-scratch
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
        :returns (mv err
                     xbfr
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
                                     (interp-st interp-st-bfrs-ok)
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
                              (interp-st interp-st-bfrs-ok)
                              state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020 (pseudo-term-binding-count x) 20)
        :returns (mv err
                     (xobj gl-object-p)
                     new-interp-st
                     new-state)
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
                 (gl-interp-bindinglist x-bindings interp-st state)))

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
               
               (scratch (interp-st-scratch interp-st))
               ((interp-st-bind
                 (equiv-contexts nil))
                ((gl-interp-recursive-call err interp-st state)
                 ;; pushes the results from the args onto the scratch frame
                 (gl-interp-arglist x.args interp-st state)))

               ((when err)
                ;; pop off any arguments that were added to scratch before the error
                (b* ((interp-st (interp-st-pop-scratch (- (len (interp-st-scratch interp-st))
                                                          (len scratch))
                                                       interp-st)))
                  (mv err nil interp-st state))))
            (gl-interp-fncall x.fn (len x.args) interp-st state))))

      (define gl-interp-arglist ((args pseudo-term-listp)
                                 (interp-st interp-st-bfrs-ok)
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

      (define gl-interp-bindinglist ((bindings cmr::bindinglist-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (cmr::bindinglist-count bindings)
                       20)
        :returns (mv err
                     new-interp-st
                     new-state)
        (b* (((when (atom bindings)) (mv nil interp-st state))
             ((cmr::binding x1) (car bindings))
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
                                (interp-st interp-st-bfrs-ok)
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
              (gl-interp-error
               :msg (gl-msg "The recursion limit ran out.")))
             (interp-st (interp-st-pushlist-scratch args interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((gl-interp-recursive-call err successp ans interp-st state)
               (gl-rewrite-fncall fn arity fn-mode.dont-rewrite interp-st state)))
             ((when err)
              (b* ((interp-st (interp-st-pop-scratch arity interp-st)))
                (mv err nil interp-st state)))
             ((when successp)
              (b* ((interp-st (interp-st-pop-scratch arity interp-st)))
                (mv nil ans interp-st state)))
             (args (take arity (interp-st-scratch interp-st)))
             ((mv successp ans interp-st state)
              (gl-primitive-fncall fn args fn-mode.dont-primitive-exec interp-st state))
             ((when successp)
              (b* ((interp-st (interp-st-pop-scratch arity interp-st)))
                (mv nil ans interp-st state)))
             (args (take arity (interp-st-scratch interp-st)))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv err successp ans interp-st state)
               (gl-interp-fn-definition fn args fn-mode.dont-expand-def interp-st state)))
             (scratch (interp-st-scratch interp-st))
             (interp-st (interp-st-pop-scratch arity interp-st))
             ((when err)
              (mv err nil interp-st state))
             ((when successp)
              (mv nil ans interp-st state))
             (args (take arity scratch)))
          (mv nil (g-apply fn args) interp-st state)))

      (define gl-interp-fn-definition ((fn pseudo-fnsym-p)
                                       (args gl-objectlist-p)
                                       (dont)
                                       (interp-st interp-st-bfrs-ok)
                                       state)
        :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
        :returns (mv err successp
                     (ans gl-object-p)
                     new-interp-st
                     new-state)
        (b* (((when dont)
              (mv nil nil nil interp-st state))
             ((mv ok formals body)
              (acl2::fn-get-def fn state))
             ((unless ok)
              (mv nil nil nil interp-st state))
             ((unless (eql (len formals) (len args)))
              (gl-interp-error
               :msg (gl-msg "Error interpreting a call of ~x0: it was given ~x1 arguments but has ~x2 formals."
                            fn (len args) (len formals))
               :nvals 2))
             (interp-st (interp-st-push-frame (pairlis$ formals args) interp-st))
             (interp-st (interp-st-set-debug fn interp-st))
             ((mv err ans interp-st state)
              (gl-interp-term-equivs body interp-st state))
             (interp-st (interp-st-pop-frame interp-st)))
          (mv err (not err) ans interp-st state)))


      (define gl-rewrite-fncall ((fn pseudo-fnsym-p)
                                 (arity natp)
                                 (dont)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
        ;; :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
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
              (gl-interp-error
               :msg (gl-msg "The recursion limit ran out.")
               :nvals 2)))
          (gl-rewrite-try-rules rules fn arity interp-st state)))

      (define gl-rewrite-try-rules ((rules pseudo-rewrite-rule-listp)
                                    (fn pseudo-fnsym-p)
                                    (arity natp)
                                    (interp-st interp-st-bfrs-ok)
                                    state)
        ;; :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
        :measure (list (nfix (interp-st->reclimit interp-st)) 10000 (len rules) 0)
        :returns (mv err successp
                     (ans gl-object-p)
                     new-interp-st
                     new-state)
        (b* (((when (atom rules))
              (mv nil nil nil interp-st state))
             ((gl-interp-recursive-call err successp ans interp-st state)
              (gl-rewrite-try-rule (car rules) fn arity interp-st state))
             ((when (or err successp))
              (mv err successp ans interp-st state)))
          (gl-rewrite-try-rules (cdr rules) fn arity interp-st state)))

      (define gl-rewrite-try-rule ((rule pseudo-rewrite-rule-p)
                                   (fn pseudo-fnsym-p)
                                   (arity natp)
                                   (interp-st interp-st-bfrs-ok)
                                   state)
        ;; :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
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
                             (pseudo-term-case rule.lhs
                               :fncall (and (eq rule.lhs.fn (pseudo-fnsym-fix fn))
                                            (eql (len rule.lhs.args) (lnfix arity)))
                               :otherwise nil)))
              (gl-interp-error
               :msg (gl-msg "Malformed rewrite rule: ~x0~%" rule)
               :nvals 2))
             ((unless (or (eq rule.equiv 'equal)
                          ;; bozo check refinements
                          (member rule.equiv (interp-st->equiv-contexts interp-st))))
              (mv nil nil nil interp-st state))
             (rule.lhs.args (pseudo-term-call->args rule.lhs))
             ((mv unify-ok bindings) (glcp-unify-term/gobj-list-prefix rule.lhs.args
                                                                       (interp-st-scratch interp-st)
                                                                       nil))
             ((unless unify-ok) (mv nil nil nil interp-st state))
             ((unless (mbt (pseudo-term-listp rule.hyps)))
              (gl-interp-error
               :msg (gl-msg "Malformed rewrite rule: ~x0~%" rule)
               :nvals 2))
             (backchain-limit (interp-st->backchain-limit interp-st))
             ((when (and** rule.hyps (eql 0 backchain-limit)))
              (mv nil nil nil interp-st state))
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
              ((gl-interp-recursive-call err successp interp-st state)
               (gl-rewrite-relieve-hyps rule.hyps interp-st state)))

             ((unless successp)
              (b* ((interp-st (interp-st-pop-frame interp-st)))
                (mv err nil nil interp-st state)))

             (concl-flags (!interp-flags->intro-synvars t flags))
             ((interp-st-bind
               (flags concl-flags flags))
              ((mv err val interp-st state)
               (gl-interp-term-equivs rule.rhs interp-st state)))

             (interp-st (interp-st-pop-frame interp-st)))

          (mv err (not err) val interp-st state)))
      
      (define gl-rewrite-relieve-hyps ((hyps pseudo-term-listp)
                                       (interp-st interp-st-bfrs-ok)
                                       state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 9000
                       (pseudo-term-list-binding-count hyps) 0)
        :returns (mv err successp
                     new-interp-st
                     new-state)
        (b* (((when (atom hyps))
              (mv nil t interp-st state))
             ((gl-interp-recursive-call err ok interp-st state)
              (gl-rewrite-relieve-hyp (car hyps) interp-st state))
             ((when (or err (not ok)))
              (mv err ok interp-st state)))
          (gl-rewrite-relieve-hyps (cdr hyps) interp-st state)))

      (define gl-rewrite-relieve-hyp ((hyp pseudo-termp)
                                      (interp-st interp-st-bfrs-ok)
                                      state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 9000
                       (pseudo-term-binding-count hyp) 0)
        :returns (mv err successp
                     new-interp-st
                     new-state)
        (b* (((mv synp-type untrans-form trans-term vars)
              (gl-interp-match-synp hyp))
             ((when synp-type)
              (gl-rewrite-relieve-hyp-synp synp-type trans-term vars untrans-form interp-st state))
             ((mv err test-bfr interp-st state)
              (gl-interp-test hyp interp-st state)))
          (mv err (eq test-bfr t) interp-st state)))

      (define gl-interp-time$ ((timing-arg pseudo-termp)
                               (x pseudo-termp)
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st)) 2020
                       (+ (pseudo-term-binding-count timing-arg)
                          (pseudo-term-binding-count x))
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
          (acl2::time$1 time$-arg
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
                               (interp-st interp-st-bfrs-ok)
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
                            (interp-st interp-st-bfrs-ok)
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
              (gl-maybe-interp (interp-st-bfr-not testbfr) else interp-st state))
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
                            (interp-st interp-st-bfrs-ok)
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
             ((interp-st-bind
               (equiv-contexts or-test-equiv-contexts equiv-contexts))
              ((gl-interp-recursive-call err testval interp-st state)
               (gl-interp-term-equivs test interp-st state)))
             ((when err) (mv err nil interp-st state))
             (interp-st (interp-st-push-scratch testval interp-st))
             ((gl-interp-recursive-call err testbfr interp-st state)
              (gl-interp-simplify-if-test testval interp-st state))
             ((when err)
              (b* ((interp-st (interp-st-pop-scratch 1 interp-st)))
                (mv err nil interp-st state)))
             (interp-st (interp-st-push-bool-scratch testbfr interp-st))
             ((gl-interp-recursive-call err else-unreachable elseval interp-st state)
              ;; pushes val onto scratch if not unreachable
              (gl-maybe-interp (interp-st-bfr-not testbfr) else interp-st state))
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
                               (interp-st interp-st-bfrs-ok)
                               state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2020
                       (pseudo-term-binding-count x)
                       60)
        :returns (mv err
                     unreachable
                     (ans gl-object-p)
                     new-interp-st
                     new-state)
        (b* (((mv contra interp-st)
              (interp-st-pathcond-assume test interp-st))
             ((when contra)
              (mv nil t nil interp-st state))
             ((mv err ans interp-st state)
              (gl-interp-term-equivs x interp-st state))
             (interp-st (interp-st-pathcond-rewind interp-st))
             ((when (eq err :unreachable))
              (mv nil t nil interp-st state)))
          (mv err nil ans interp-st state)))

      (define gl-interp-maybe-simplify-if-test ((test interp-st-bfr-p)
                                                (xobj gl-object-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
        :guard (interp-st-bfr-listp (gl-object-bfrlist xobj))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       0
                       (gl-object-count xobj)
                       60)
        :returns (mv err
                     unreachable
                     xbfr
                     new-interp-st
                     new-state)
        (b* (((mv contra interp-st)
              (interp-st-pathcond-assume test interp-st))
             ((when contra)
              (mv nil t nil interp-st state))
             (reclimit (interp-st->reclimit interp-st))
             ((when (zp reclimit))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.") :nvals 2))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv err ans interp-st state)
               (gl-interp-simplify-if-test xobj interp-st state)))
             (interp-st (interp-st-pathcond-rewind interp-st))
             ((when (eq err :unreachable))
              (mv nil t nil interp-st state)))
          (mv err nil ans interp-st state)))

      (define gl-interp-simplify-if-test ((xobj gl-object-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)
        :guard (interp-st-bfr-listp (gl-object-bfrlist xobj))
        :returns (mv err
                     xbfr
                     new-interp-st
                     new-state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (gl-object-count xobj)
                       40)
        (gl-object-case xobj
          :g-concrete (mv nil (bool-fix xobj.val) interp-st state)
          :g-boolean (mv nil xobj.bool interp-st state)
          :g-integer (mv nil t interp-st state)
          :g-cons (mv nil t interp-st state)
          :g-var (b* (((mv bfr interp-st)
                       (interp-st-add-term-bvar-unique xobj interp-st state)))
                   (mv nil bfr interp-st state))
          :g-ite (gl-interp-simplify-if-test-ite xobj interp-st state)
          :g-apply (gl-interp-simplify-if-test-fncall xobj interp-st state)))

      ;; BOZO should we have a version of this for OR?
      (define gl-interp-simplify-if-test-ite ((xobj gl-object-p)
                                              (interp-st interp-st-bfrs-ok)
                                              state)
        :guard (and (gl-object-case xobj :g-ite)
                    (interp-st-bfr-listp (gl-object-bfrlist xobj)))
        :returns (mv err
                     xbfr
                     new-interp-st
                     new-state)
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (gl-object-count xobj)
                       30)
        (b* (((unless (mbt (gl-object-case xobj :g-ite)))
              (gl-interp-error :msg (gl-msg "Impossible case")))
             ((g-ite xobj))
             (interp-st (interp-st-push-scratch xobj.else interp-st))
             (interp-st (interp-st-push-scratch xobj.then interp-st))
             ((gl-interp-recursive-call err test-bfr interp-st state)
              (gl-interp-simplify-if-test xobj.test interp-st state))
             ((when err)
              (b* ((interp-st (interp-st-pop-scratch 2 interp-st)))
                (mv err nil interp-st state)))
             (xobj.then (car (interp-st-scratch interp-st)))
             (interp-st (interp-st-push-bool-scratch test-bfr interp-st))
             (interp-st (interp-st-pop-scratch 1 interp-st))
             ((gl-interp-recursive-call err then-unreachable then-bfr interp-st state)
              (gl-interp-maybe-simplify-if-test test-bfr xobj.then interp-st state))
             ((when err)
              (b* ((interp-st (interp-st-pop-bool-scratch 1 interp-st))
                   (interp-st (interp-st-pop-scratch 1 interp-st)))
                (mv err nil interp-st state)))
             (test-bfr (car (interp-st-bool-scratch interp-st)))
             (xobj.else (car (interp-st-scratch interp-st)))
             (interp-st (interp-st-push-bool-scratch then-bfr interp-st))
             (interp-st (interp-st-pop-scratch 1 interp-st))
             ((mv err else-unreachable else-bfr interp-st state)
              (gl-interp-maybe-simplify-if-test test-bfr xobj.else interp-st state))
             ((when err)
              (b* ((interp-st (interp-st-pop-bool-scratch 2 interp-st)))
                (mv err nil interp-st state)))
             (then-bfr (car (interp-st-bool-scratch interp-st)))
             (test-bfr (cadr (interp-st-bool-scratch interp-st)))
             (interp-st (interp-st-pop-bool-scratch 2 interp-st))
             ((mv err bfr interp-st)
              (gl-interp-finish-simplify-if-test-ite
               test-bfr then-bfr else-bfr then-unreachable else-unreachable interp-st)))
          (mv err bfr interp-st state)))
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
        :returns (mv err
                     xbfr
                     new-interp-st
                     new-state)
        (b* (((mv not-matched neg-arg)
              (gl-apply-match-not xobj))
             ((when not-matched)
              (b* (((mv err bfr interp-st state)
                    (gl-interp-simplify-if-test neg-arg interp-st state))
                   ((when err)
                    (mv err nil interp-st state)))
                (mv nil (interp-st-bfr-not bfr) interp-st state)))
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
             ((when (zp reclimit))
              (gl-interp-error
               :msg (gl-msg "The recursion limit ran out.")))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit)
               (equiv-contexts '(iff)))
              ((gl-interp-recursive-call err successp ans interp-st state)
               (gl-rewrite-fncall xobj.fn xobj.args fn-mode.dont-rewrite-under-if-test interp-st state)))
             ((when err)
              (mv err nil interp-st state))
             ((when successp)
              (b* (((interp-st-bind
                     (reclimit (1- reclimit) reclimit))
                    ((mv err ans interp-st state)
                     (gl-interp-simplify-if-test ans interp-st state))))
                (mv err ans interp-st state)))

             (look (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
                              (look)
                              (get-term->bvar xobj bvar-db)
                              look))
             ((when look)
              (b* ((bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
                                   (bfr)
                                   (bfr-var look)
                                   bfr)))
                (mv nil bfr interp-st state)))

             ((unless (interp-flags->intro-bvars (interp-st->flags interp-st)))
              ;; Note: we only return intro-bvars-fail when this flag is set to
              ;; false, which it is not at the top level.  So when we set the flag
              ;; to true (as we do in relieve-hyp and add-bvar-constraint-substs,
              ;; e.g.) we check for this error specifically and catch it.
              ;; Otherwise we expect callers not to set intro-bvars to nil and then
              ;; they won't have to deal with this error specially.
              (mv :intro-bvars-fail nil interp-st state))

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

             (interp-st (interp-st-push-bool-scratch bfr interp-st))

             ((mv err interp-st state)
              (gl-interp-add-constraints xobj interp-st state))

             (bfr (car (interp-st-bool-scratch interp-st)))
             (interp-st (interp-st-pop-bool-scratch 1 interp-st))

             ((when err)
              (mv err nil interp-st state)))
          (mv nil bfr interp-st state)))


      (define gl-interp-add-constraints ((xobj gl-object-p)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
        :guard (and (gl-object-case xobj :g-apply)
                    (interp-st-bfr-listp (gl-object-bfrlist xobj)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000
                       (gl-object-count xobj)
                       15)
        :returns (mv err
                     new-interp-st
                     new-state)
        (b* ((constraint-db (interp-st->constraint-db interp-st))
             ((mv constraint-substs constraint-db)
              (gbc-process-new-lit xobj constraint-db state))
             (interp-st (update-interp-st->constraint-db constraint-db interp-st))
             ((unless constraint-substs)
              (mv nil interp-st state))
             ;; Disable the pathcond so that constraint thms are simulated in an empty (universal) context.
             ((mv pathcond-enabledp interp-st) (stobj-let ((pathcond (interp-st->pathcond interp-st)))
                                                          (enabledp pathcond)
                                                          (b* ((enabledp (pathcond-enabledp pathcond))
                                                               (pathcond (update-pathcond-enabledp nil pathcond)))
                                                            (mv enabledp pathcond))
                                                          (mv enabledp interp-st)))
             (reclimit (interp-st->reclimit interp-st))
             ((when (zp reclimit))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.") :nvals 0))
             (interp-st (update-interp-st->constraint-inst-stack
                         (append constraint-substs (interp-st->constraint-inst-stack interp-st))
                         interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv err interp-st state)
               (gl-interp-add-constraints-for-substs (len constraint-substs) interp-st state)))
             (interp-st (stobj-let ((pathcond (interp-st->pathcond interp-st)))
                                   (pathcond)
                                   (update-pathcond-enabledp pathcond-enabledp pathcond)
                                   interp-st)))
          (mv err interp-st state)))
      


      (define gl-interp-add-constraints-for-substs ((n natp)
                                                    (interp-st interp-st-bfrs-ok)
                                                    state)
        :guard (<= n (len (interp-st->constraint-inst-stack interp-st)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       10000
                       (nfix n)
                       10)
        :returns (mv err
                     new-interp-st
                     new-state)
        (b* (((when (zp n)) (mv nil interp-st state))
             ((constraint-instance sub1) (car (interp-st->constraint-inst-stack interp-st)))
             (interp-st (update-interp-st->constraint-inst-stack
                         (cdr (interp-st->constraint-inst-stack interp-st))
                         interp-st))
             (thm-body (meta-extract-formula sub1.thmname state))
             ((unless (pseudo-termp thm-body))
              (gl-interp-add-constraints-for-substs (1- n) interp-st state))
             (interp-st (interp-st-push-frame sub1.subst interp-st))
             ((gl-interp-recursive-call err bfr interp-st state)
              (gl-interp-test thm-body interp-st state))
             (interp-st (interp-st-pop-frame interp-st))
             ((when err)
              (mv err interp-st state))
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
          (gl-interp-add-constraints-for-substs (1- n) interp-st state)))
      

      (define gl-interp-merge-branches ((testbfr interp-st-bfr-p)
                                        (thenval gl-object-p)
                                        (elseval gl-object-p)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
        :guard (and (interp-st-bfr-listp (gl-object-bfrlist thenval))
                    (interp-st-bfr-listp (gl-object-bfrlist elseval)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       2000 0 0)
        :returns (mv err
                     (ans gl-object-p)
                     new-interp-st
                     new-state)
        (b* ((thenval (gl-object-fix thenval))
             (elseval (gl-object-fix elseval))
             ((when (eq testbfr t)) (mv nil thenval interp-st state))
             ((when (eq testbfr nil)) (mv nil elseval interp-st state))
             ((when (hons-equal thenval elseval)) (mv nil thenval interp-st state)))
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
        :returns (mv err
                     (ans gl-object-p)
                     new-interp-st
                     new-state)
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
             ((when (zp reclimit))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.")))
             (interp-st (interp-st-push-scratch elseval interp-st))
             (interp-st (interp-st-push-scratch thenval interp-st))
             (interp-st (interp-st-push-scratch (g-boolean testbfr) interp-st))
             (interp-st (interp-st-push-bool-scratch testbfr interp-st))
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((mv err successp ans interp-st state)
               (gl-rewrite-try-rules rules 'if 3 interp-st state)))
             (scratch (interp-st-scratch interp-st))
             (testbfr (car (interp-st-bool-scratch interp-st)))
             (interp-st (interp-st-pop-scratch 3 interp-st))
             (interp-st (interp-st-pop-bool-scratch 1 interp-st))
             ((when err)
              (mv err nil interp-st state))
             ((when successp)
              (mv nil ans interp-st state))
             (elseval (third scratch))
             (thenval (second scratch)))
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
        :returns (mv err
                     (ans gl-object-p)
                     new-interp-st
                     new-state)
        (b* (((mv thenfn thenargs) (gl-object-recognize-merge-fncall thenval))
             ((mv elsefn elseargs) (gl-object-recognize-merge-fncall elseval))
             ((unless (and** thenfn
                             (eq thenfn elsefn)
                             (eql (len thenargs) (len elseargs))))
              (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (obj logicman)
                         (gl-object-basic-merge testbfr thenval elseval)
                         (mv nil obj interp-st state)))
             ;; BOZO sad:
             (reclimit (interp-st->reclimit interp-st))
             ((when (zp reclimit))
              (gl-interp-error :msg (gl-msg "The recursion limit ran out.")))

             (scratch (interp-st-scratch interp-st))
             (thenval-stack (interp-st->thenval-stack interp-st))
             (elseval-stack (interp-st->elseval-stack interp-st))
             (interp-st (update-interp-st->thenval-stack (append thenargs thenval-stack) interp-st))
             (interp-st (update-interp-st->elseval-stack (append elseargs elseval-stack) interp-st))
             (interp-st (interp-st-push-bool-scratch testbfr interp-st))
             ;; pops args off thenval/elseval-stack, pushes onto scratch
             ((interp-st-bind
               (reclimit (1- reclimit) reclimit))
              ((gl-interp-recursive-call err interp-st state)
               (gl-interp-merge-branch-args (len thenargs) interp-st state)))
             (interp-st (interp-st-pop-bool-scratch 1 interp-st))
             ((when err)
              ;; pop off any args pushed on before error
              (b* ((interp-st (interp-st-pop-scratch (- (len (interp-st-scratch interp-st))
                                                        (len scratch))
                                                     interp-st))
                   ;; (new-thenval-stack (interp-st->thenval-stack interp-st))
                   ;; (interp-st (update-interp-st->thenval-stack
                   ;;             (nthcdr (- (len new-thenval-stack)
                   ;;                        (len thenval-stack))
                   ;;                     new-thenval-stack)
                   ;;             interp-st))
                   ;; (new-elseval-stack (interp-st->elseval-stack interp-st))
                   ;; (interp-st (update-interp-st->elseval-stack
                   ;;             (nthcdr (- (len new-elseval-stack)
                   ;;                        (len elseval-stack))
                   ;;                     new-elseval-stack)
                   ;;             interp-st))
                   )
                (mv err nil interp-st state))))
          (gl-interp-fncall thenfn (len thenargs) interp-st state)))

      (define gl-interp-merge-branch-args (;; (testbfr interp-st-bfr-p)
                                           (n natp)
                                           ;; (thenargs gl-objectlist-p)
                                           ;; (elseargs gl-objectlist-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
        ;; :guard (and (eql (len thenargs) (len elseargs))
        ;;             (interp-st-bfr-listp (gl-objectlist-bfrlist thenargs))
        ;;             (interp-st-bfr-listp (gl-objectlist-bfrlist elseargs)))
        :measure (list (nfix (interp-st->reclimit interp-st))
                       3000 n 0)
        :returns (mv err
                     new-interp-st
                     new-state)
        (b* (((when (zp n))
              (mv nil interp-st state))
             (thenstack (interp-st->thenval-stack interp-st))
             (thenval (car thenstack))
             (interp-st (update-interp-st->thenval-stack (cdr thenstack) interp-st))
             (elsestack (interp-st->elseval-stack interp-st))
             (elseval (car elsestack))
             (interp-st (update-interp-st->elseval-stack (cdr elsestack) interp-st))
             
             ((gl-interp-recursive-call err ans interp-st state)
              (gl-interp-merge-branches (car (interp-st-bool-scratch interp-st))
                                        thenval elseval interp-st state))
             ((when err)
              (b* ((interp-st (update-interp-st->thenval-stack
                               (nthcdr (1- n) (interp-st->thenval-stack interp-st))
                               interp-st))
                   (interp-st (update-interp-st->elseval-stack
                               (nthcdr (1- n) (interp-st->elseval-stack interp-st))
                               interp-st)))
                (mv err interp-st state)))
             (interp-st (interp-st-push-scratch ans interp-st)))
          (gl-interp-merge-branch-args (1- n) interp-st state))))))





(local
 (defthm major-stack-bfrlist-of-stack$a-push-scratch
   (set-equiv (major-stack-bfrlist (stack$a-push-scratch obj stack))
              (append (gl-object-bfrlist obj)
                      (major-stack-bfrlist stack)))
   :hints(("Goal" :in-theory (enable major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-stack-bfrlist
                                     minor-frame-bfrlist
                                     stack$a-push-scratch)))))


(local (defthm gl-objectlist-bfrlist-of-append
         (equal (gl-objectlist-bfrlist (append x y))
                (append (gl-objectlist-bfrlist x)
                        (gl-objectlist-bfrlist y)))
         :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist append)))))

(local
 (defthm major-stack-bfrlist-of-stack$a-pushlist-scratch
   (set-equiv (major-stack-bfrlist (stack$a-pushlist-scratch objs stack))
                    (append (gl-objectlist-bfrlist objs)
                            (major-stack-bfrlist stack)))
   :hints(("Goal" :in-theory (enable major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-stack-bfrlist
                                     minor-frame-bfrlist
                                     stack$a-pushlist-scratch)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-push-bool-scratch
   (set-equiv (major-stack-bfrlist (stack$a-push-bool-scratch obj stack))
                    (cons obj
                          (major-stack-bfrlist stack)))
   :hints(("Goal" :in-theory (enable stack$a-push-bool-scratch
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist
                                     acl2::set-unequal-witness-rw)
           :do-not-induct t))))

(local (defthm member-nthcdr
         (implies (not (member v x))
                  (not (member v (nthcdr n x))))))



(local (defthm member-gl-objectlist-bfrlist-of-nthcdr
         (implies (not (member v (gl-objectlist-bfrlist x)))
                  (not (member v (gl-objectlist-bfrlist (nthcdr n x)))))
         :hints(("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm major-stack-bfrlist-of-stack$a-pop-bool-scratch
   (implies (not (member v (major-stack-bfrlist stack)))
            (not (member v (major-stack-bfrlist (stack$a-pop-bool-scratch n stack)))))
   :hints(("Goal" :in-theory (enable stack$a-pop-bool-scratch
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :expand ((major-stack-bfrlist stack)
                    (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-pop-scratch
   (implies (not (member v (major-stack-bfrlist stack)))
            (not (member v (major-stack-bfrlist (stack$a-pop-scratch n stack)))))
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
                                       major-stack-bfrlist
                                       major-frame-bfrlist)
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
   (defthm gl-objectlist-bfrlist-of-stack$a-scratch
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (gl-objectlist-bfrlist (stack$a-scratch stack)))))
     :hints(("Goal" :in-theory (enable stack$a-scratch
                                       major-stack-bfrlist
                                       major-frame-bfrlist
                                       minor-stack-bfrlist
                                       minor-frame-bfrlist)
             :expand ((major-stack-bfrlist stack)
                      (minor-stack-bfrlist (major-frame->minor-stack (car stack))) )
             :do-not-induct t))))

(local
   (defthm bfrlist-of-stack$a-bool-scratch
     (implies (not (member v (major-stack-bfrlist stack)))
              (not (member v (stack$a-bool-scratch stack))))
     :hints(("Goal" :in-theory (enable stack$a-bool-scratch
                                       major-stack-bfrlist
                                       major-frame-bfrlist
                                       minor-stack-bfrlist
                                       minor-frame-bfrlist)
             :expand ((major-stack-bfrlist stack)
                      (minor-stack-bfrlist (major-frame->minor-stack (car stack))) )
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

(local (defthm bfr-listp-of-bool-scratch-when-stack-ok
         (implies (bfr-listp (major-stack-bfrlist stack))
                  (bfr-listp (stack$a-bool-scratch stack)))
         :hints(("Goal" :in-theory (enable stack$a-bool-scratch)
                 :expand ((major-stack-bfrlist stack)
                          (major-frame-bfrlist (car stack))
                          (minor-stack-bfrlist (major-frame->minor-stack (car stack)))
                          (minor-frame-bfrlist (car (major-frame->minor-stack (car stack)))))
                 :do-not-induct t))))

(local (defthm bfr-listp-bfrlist-of-scratch-when-stack-ok
         (implies (bfr-listp (major-stack-bfrlist stack))
                  (bfr-listp (gl-objectlist-bfrlist (stack$a-scratch stack))))
         :hints(("Goal" :in-theory (enable stack$a-scratch
                                           major-frame-bfrlist
                                           minor-frame-bfrlist)
                 :expand ((major-stack-bfrlist stack)
                          (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
                 :do-not-induct t))))


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
  :hints(("Goal" :in-theory (enable bfr-p aig-p acl2::ubddp))))


(local (in-theory (disable member-equal)))

(local (defun find-flag-is-hyp (clause)
         (if (atom clause)
             nil
           (let ((lit (car clause)))
             (case-match lit
               (('not ('acl2::flag-is ('quote val))) val)
               (& (find-flag-is-hyp (cdr clause))))))))

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

(local (in-theory (enable stack-peek-scratch)))

(progn
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate interp-st-bfrs-ok-of-<fn>
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
                    ((gl-object-p x)               (interp-st-bfr-listp (gl-object-bfrlist x)))
                    ((gl-objectlist-p x)           (interp-st-bfr-listp (gl-objectlist-bfrlist x)))
                    (interp-st                     (interp-st-bfrs-ok interp-st))
                    ((constraint-instancelist-p x) (interp-st-bfr-listp (constraint-instancelist-bfrlist x))))
      :return-concls ((xbfr                        (interp-st-bfr-p xbfr new-interp-st))
                      ((gl-object-p x)             (interp-st-bfr-listp (gl-object-bfrlist x) new-interp-st))
                      (new-interp-st               (interp-st-bfrs-ok new-interp-st)))
      :rules ((t (:add-keyword :hints ('(:do-not-induct t)
                                       (let ((flag (find-flag-is-hyp clause)))
                                         (and flag
                                              (prog2$ (cw "flag: ~x0~%" flag)
                                                      '(:no-op t))))))))
      :hints ((acl2::just-expand-mrec-default-hint 'gl-interp-term id nil world)))))







