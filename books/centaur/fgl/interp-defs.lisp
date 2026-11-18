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

; Interpreter definitions and shared basic invariants.
; Include interp.lisp for the complete interpreter correctness result.
;
; Retain the original interpreter's CMUCL exclusion: its stack-binding
; extension proofs exhausted the CMUCL dynamic heap (September 2023).
; cert-param: non-cmucl

(in-package "FGL")


(include-book "object-ops")
(include-book "easy-termp")
(include-book "interp-st-pathcond")
(include-book "bfr-arithmetic")
(include-book "bvar-db-equivs")
(include-book "centaur/meta/bindinglist" :dir :system)
(include-book "system/f-put-global" :dir :system)
(include-book "primitives-stub")
(include-book "sat-stub")
(include-book "trace")
(include-book "congruence")
(local (include-book "std/util/defret-mutual-generate" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/meta/resolve-flag-cp" :dir :system))
(local (include-book "centaur/meta/urewrite" :dir :system))
(local (include-book "centaur/meta/let-abs" :dir :system))
(local (include-book "centaur/meta/flatten-clause" :dir :system))

;; Preserve the client's existing theory; enable the shared private facts below
;; at the points where they are used.
(local (deftheory before-interp-proof-support (current-theory :here)))
(local (include-book "interp-proof-support"))
(local (in-theory (theory 'before-interp-proof-support)))


(std::make-returnspec-config :hints-sub-returnnames t)


(local (std::add-default-post-define-hook :fix))


(local (in-theory (e/d (acl2::kwote-lst-redef)
		       (kwote-lst))))


;; NOTE: All these rules should be superfluous, but they might significantly speed up proofs.
(local (in-theory (e/d (interp-st-bfrs-ok-of-update-reclimit
                        interp-st-bfrs-ok-of-update-equiv-contexts
                        interp-st->logicman-of-update-reclimit
                        interp-st->logicman-of-update-equiv-contexts
                        interp-st->logicman-of-update-stack
                        interp-st->logicman-of-update-errmsg)
                       (w))))


(define fgl-hide-term-p ((x pseudo-termp))
  (pseudo-term-case x
    :fncall (eq x.fn 'fgl-hide)
    :otherwise nil))


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


(local (in-theory (enable assoc-when-key)))


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
       ((unless (fgl-bfr-object-p val (interp-st-bfrstate)))
        (fgl-interp-error
         :msg (fgl-msg "Syntax-bind error: ~x0 evaluted to an illformed symbolic object, saved as debug object."
		       (pseudo-term-quote->val untrans))
         :debug-obj val)))
    (fgl-interp-value val))
  ///

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


;; (define interp-st-checkpoint-p (chp interp-st)
;;   :enabled t
;;   (stobj-let ((pathcond (interp-st->pathcond interp-st))
;;               (logicman (interp-st->logicman interp-st)))
;;              (ok)
;;              (pathcond-checkpoint-p chp (logicman->mode logicman) pathcond)
;;              ok))


(local (in-theory (e/d (pseudo-var-list-p-of-append
                        major-stack-bfrlist-of-stack$a-set-bindings)
                       (pseudo-termp
                        acl2::magic-ev))))


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
       ((unless (fgl-bfr-object-bindings-p val (interp-st-bfrstate)))
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
;; function.


(defthm logicman-get-of-bfr-ite-bss-fn
  (implies (and (not (equal (logicman-field-fix key) :aignet))
                (not (equal (logicman-field-fix key) :strash)))
	   (equal (logicman-get key (mv-nth 1 (bfr-ite-bss-fn c v1 v0 logicman)))
		  (logicman-get key logicman)))
  :hints(("Goal" :in-theory (enable bfr-ite-bss-fn
				    bfr-ite-bss-fn-aux))))


(define interp-st-object-basic-merge ((test interp-st-bfr-p)
                                      (then fgl-object-p)
                                      (else fgl-object-p)
                                      (make-ites-p)
                                      &optional (interp-st 'interp-st))
  :measure (acl2::two-nats-measure (+ (fgl-object-count then)
				      (fgl-object-count else))
				   (+ (acl2-count (g-concrete->val then))
				      (acl2-count (g-concrete->val else))))

  :guard (and (fgl-bfr-object-p then (interp-st-bfrstate))
	      (fgl-bfr-object-p else (interp-st-bfrstate)))


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
	       new-interp-st)

  (b* ((bfrstate (interp-st-bfrstate))
       (then (fgl-bfr-object-fix then))
       (else (fgl-bfr-object-fix else))
       ((when (equal (fgl-object-fix then)
		     (fgl-object-fix else)))
        (mv t (fgl-bfr-object-fix then) interp-st))
       ((when (and (gobj-syntactic-booleanp then)
		   (gobj-syntactic-booleanp else)))
        (b* (((mv bfr interp-st)
	      (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (bfr logicman)
                         (bfr-ite (bfr-fix test)
				  (gobj-syntactic-boolean->bool then)
				  (gobj-syntactic-boolean->bool else)
				  logicman)
                         (mv bfr interp-st)))
	     ((mv bfr interp-st) (interp-st-pathcond-fix-bfr bfr interp-st)))
	  (mv t (mk-g-boolean bfr) interp-st)))
       ((when (and (gobj-syntactic-integerp then)
		   (gobj-syntactic-integerp else)))
        (b* (((mv bfr interp-st)
	      (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (bfr logicman)
                         (bfr-ite-bss-fn (bfr-fix test)
                                         (gobj-syntactic-integer->bits then)
                                         (gobj-syntactic-integer->bits else)
                                         logicman)
                         (mv bfr interp-st))))
	  (mv t (mk-g-integer bfr) interp-st)))
       ((when (and (gobj-syntactic-consp then)
		   (gobj-syntactic-consp else)))
        (b* ((test (bfr-fix test))
	     ((mv car-ok car interp-st)
	      (interp-st-object-basic-merge test
					    (gobj-syntactic-list->car then)
					    (gobj-syntactic-list->car else)
					    make-ites-p
					    interp-st))
	     ((unless car-ok)
	      (mv nil nil interp-st))
	     ((mv cdr-ok cdr interp-st)
	      (interp-st-object-basic-merge test
					    (gobj-syntactic-list->cdr then)
					    (gobj-syntactic-list->cdr else)
					    make-ites-p
					    interp-st))
	     ((unless cdr-ok)
	      (mv nil nil interp-st)))
	  (mv t (mk-g-cons car cdr) interp-st))))
    (mv make-ites-p
	(if make-ites-p (g-ite (mk-g-boolean (bfr-fix test)) then else) nil)
	interp-st))
  ///
  (local (in-theory (disable member-equal
			     bfr-listp-when-not-member-witness
			     fgl-bfr-object-fix-when-fgl-bfr-object-p
			     (:d interp-st-object-basic-merge))))

  (deffixequiv interp-st-object-basic-merge
    :hints (("goal" :induct (interp-st-object-basic-merge test then else make-ites-p interp-st)
	     :expand ((:free (then) (interp-st-object-basic-merge test then else make-ites-p interp-st))
		      (:free (else) (interp-st-object-basic-merge test then else make-ites-p interp-st))))))


  (local (defthm bfr-listp-fgl-object-bfrlist-of-fgl-bfr-object-fix
	   (bfr-listp (fgl-object-bfrlist (fgl-bfr-object-fix x)))
	   :hints (("goal" :use ((:instance return-type-of-fgl-bfr-object-fix.new-x))
		    :in-theory (disable return-type-of-fgl-bfr-object-fix.new-x)))))

  (defret logicman-extension-p-of-<fn>
    (implies (logicman-extension-p (interp-st->logicman interp-st) old-logicman)
	     (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman))
    :hints (("goal" :expand (<call>) :induct <call>)))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars (interp-st->logicman new-interp-st))
	   (bfr-nvars (interp-st->logicman interp-st)))
    :hints (("goal" :expand (<call>) :induct <call>)))

  (local
   (defret interp-st-bfrs-ok-of-<fn>-free
     (implies (and (interp-st-bfr-p test)
		   (interp-st-bfrs-ok interp-st)
		   (logicman-extension-p logicman (interp-st->logicman interp-st)))
	      (lbfr-p ans logicman))
     :fn interp-st-pathcond-fix-bfr))

  (local
   (defret interp-st-bfrs-ok-of-<fn>-free
     (implies (and (interp-st-bfr-listp x)
		   (interp-st-bfrs-ok interp-st)
		   (logicman-extension-p logicman (interp-st->logicman interp-st)))
	      (lbfr-listp ans logicman))
     :fn interp-st-pathcond-fix-bfr-list))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (interp-st-bfrs-ok new-interp-st))
    :hints (("goal" :expand (<call>) :induct <call>)))

  (defret bfr-listp-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (bfr-listp (fgl-object-bfrlist obj) (logicman->bfrstate (interp-st->logicman new-interp-st))))
    :hints (("goal" :expand (<call>) :induct <call>)
	    (and stable-under-simplificationp
		 '(:in-theory (enable bfr-listp-when-not-member-witness)))))

  (verify-guards interp-st-object-basic-merge-fn
    :hints ((and stable-under-simplificationp
		 '(:in-theory (enable bfr-listp-when-not-member-witness)))))

  (local (defthm bfr-list-eval-of-bfr-ite-bss-fn
	   (B* (((MV VV NEW-MAN)
		 (BFR-ITE-BSS-FN C V1 V0 LOGICMAN)))
	     (IMPLIES
	      (AND (LBFR-P C LOGICMAN)
		   (LBFR-LISTP V1 LOGICMAN)
		   (LBFR-LISTP V0 LOGICMAN))
	      (AND
	       (EQUAL
		(BOOLS->INT (BFR-LIST-EVAL VV ENV NEW-MAN))
		(IF (BFR-EVAL C ENV LOGICMAN)
		    (BOOLS->INT (BFR-LIST-EVAL V1 ENV LOGICMAN))
		    (BOOLS->INT (BFR-LIST-EVAL V0 ENV LOGICMAN)))))))
	   :hints (("goal" :use ((:instance bfr-eval-of-bfr-ite-bss-fn
				  (env (fgl-env nil env))))
		    :in-theory (e/d (gobj-bfr-list-eval-is-bfr-list-eval
				     gobj-bfr-eval)
				    (bfr-eval-of-bfr-ite-bss-fn))))))

  (defret interp-st->pathcond-of-<fn>
    (pathcond-equiv (interp-st->pathcond new-interp-st)
		    (interp-st->pathcond interp-st))
    :hints(("Goal" :expand (<call>) :induct <call>)))

  (defret interp-st->constraint-of-<fn>
    (pathcond-equiv (interp-st->constraint new-interp-st)
		    (interp-st->constraint interp-st))
    :hints(("Goal" :expand (<call>) :induct <call>)))

  (defret eval-of-interp-st-object-basic-merge
    (implies (and okp
		  (logicman-pathcond-eval (fgl-env->bfr-vals env)
					  (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env)
					  (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  (interp-st-bfrs-ok interp-st))
	     (equal (fgl-object-eval obj env (interp-st->logicman new-interp-st))
		    (if (gobj-bfr-eval test env (interp-st->logicman interp-st))
			(fgl-object-eval then env (interp-st->logicman interp-st))
		      (fgl-object-eval else env (interp-st->logicman interp-st)))))
    :hints(("Goal" :expand (<call>) :induct <call>
	    :in-theory (enable gobj-bfr-eval gobj-bfr-list-eval-is-bfr-list-eval
			       fgl-object-eval-when-gobj-syntactic-consp))))

  (local (defthm fgl-bfr-objectlist-of-fgl-bfr-object-fix
	   (bfr-listp (fgl-object-bfrlist (fgl-bfr-object-fix x bfrstate)) bfrstate)
	   :hints (("goal" :use ((:instance fgl-bfr-object-p-when-fgl-object-p
				  (x (fgl-bfr-object-fix x bfrstate))))))))

  ;; (deffixequiv fgl-object-basic-merge
  ;;   :hints (("goal" :induct (fgl-object-basic-merge test then else logicman)
  ;;            :expand ((:free (then) (fgl-object-basic-merge test then else logicman))
  ;;                     (:free (else) (fgl-object-basic-merge test then else logicman))))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :aignet))
		  (not (equal (logicman-field-fix key) :strash)))
	     (equal (logicman-get key (interp-st->logicman new-interp-st))
		    (logicman-get key (interp-st->logicman interp-st))))
    :hints(("Goal" :expand (<call>) :induct <call>)))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :pathcond))
		  (not (equal (interp-st-field-fix key) :constraint))
		  (not (equal (interp-st-field-fix key) :logicman)))
	     (equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st)))
    :hints(("Goal" :expand (<call>) :induct <call>)))


  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	  (nth *pathcond-enabledp* (interp-st->pathcond interp-st)))
    :hints(("Goal" :expand (<call>) :induct <call>))))


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
	       (b* (((mv ite interp-st) (interp-st-pathcond-fix-bfr ite interp-st)))
		 (mv ite interp-st state))))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (interp-st-bfrs-ok new-interp-st)))

  (defret lbfr-p-of-<fn>
    (lbfr-p ite (interp-st->logicman new-interp-st)))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
		  (not (equal (interp-st-field-fix key) :errmsg))
		  (not (equal (interp-st-field-fix key) :pathcond))
		  (not (equal (interp-st-field-fix key) :constraint)))
	     (equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st))))


  (defret interp-st->pathcond-of-<fn>
    (pathcond-equiv (interp-st->pathcond new-interp-st)
		    (interp-st->pathcond interp-st)))

  (defret interp-st->constraint-of-<fn>
    (pathcond-equiv (interp-st->constraint new-interp-st)
		    (interp-st->constraint interp-st)))

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
			   (gobj-bfr-eval test-bfr env (interp-st->logicman interp-st)))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env)
					  (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env)
					  (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  (interp-st-bfrs-ok interp-st))
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
    (equal (w new-state) (w state)))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	  (nth *pathcond-enabledp* (interp-st->pathcond interp-st)))))


(local (in-theory (e/d (len-equal-0
                        pseudo-term-bindinglist-count-when-consp
                        len-of-cons
                        and*-hyp
                        len-is
                        open-len-is
                        equal-len-hyp
                        mv-nth-of-cons
                        len-cdr-less-when-consp
                        stack$a-open-nth-scratch)
                       ((tau-system)
                        len
                        default-car
                        default-cdr
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
                        append
                        get-term->bvar$c-updater-independence))))


(defun fgl-interp-fncall-special-case-fn (cases)
  (b* (((when (atom cases))
        '((otherwise (fgl-interp-value nil nil))))
       ((list (list fn arity explicit-successp) term) (car cases)))
    (cons `(,fn
            (if (eql (len args) ,arity)
                ,(if explicit-successp
                     term
                   `(b* (((fgl-interp-value ans) ,term))
		      (fgl-interp-value t ans)))
	      (fgl-interp-error :msg (fgl-msg "Bad arity in special fncall: ~x0"
					      (cons (pseudo-fnsym-fix fn) (pseudo-term-list-fix args)))
                                :nvals 2)))
          (fgl-interp-fncall-special-case-fn (cdr cases)))))


(defmacro fgl-interp-fncall-special-case (fn &rest cases)
  `(case ,fn
     . ,(fgl-interp-fncall-special-case-fn cases)))


(set-state-ok t)


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
  (b* (((mv err rules) (fgl-function-rules fn
					   (interp-st->rewrite-rules interp-st)
					   (w state)))
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
			   (rules-ev-falsify fgl-ev-falsify)
			   (rules-ev-theoremp fgl-ev-theoremp)))
	     :in-theory (enable fgl-good-fgl-rules-p
				fgl-ev-when-theoremp
				fgl-ev-theoremp
				fgl-ev-of-nonsymbol-atom
				fgl-ev-of-bad-fncall
				fgl-ev-of-fncall-args))
	    (and stable-under-simplificationp
		 (case-match clause
		   ((('equal (fn . &) &))
		    (and (symbolp fn)
			 `(:in-theory (enable ,fn))))
		   (& '(:use fgl-ev-meta-extract-global-badguy))))
	    (and stable-under-simplificationp
		 '(:in-theory (enable fgl-ev-theoremp))))))


(define interp-st-branch-merge-fn-rules ((fn pseudo-fnsym-p) interp-st state)
  :returns (mv (rules fgl-rulelist-p) new-interp-st)
  (b* (((mv err rules) (fgl-branch-merge-rules fn
					       (interp-st->branch-merge-rules interp-st)
					       (w state)))
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
			   (rules-ev-falsify fgl-ev-falsify)
			   (rules-ev-theoremp fgl-ev-theoremp)))
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


(define interp-st-branch-merge-fnlist-rules ((fns pseudo-fnsymlist-p) interp-st state)
  :returns (mv (rules fgl-rulelist-p) new-interp-st)
  :prepwork ((local (defthm true-listp-when-fgl-rulelist-p
		      (implies (fgl-rulelist-p x) (true-listp x))))
	     (local (defthm fgl-rulelist-p-of-append
		      (implies (and (fgl-rulelist-p x)
				    (fgl-rulelist-p y))
			       (fgl-rulelist-p (append x y)))
		      :hints(("Goal" :in-theory (enable fgl-rulelist-p))))))
  (b* (((when (atom fns)) (mv nil interp-st))
       ((mv rules1 interp-st) (interp-st-branch-merge-fn-rules (car fns) interp-st state))
       ((mv rules2 interp-st) (interp-st-branch-merge-fnlist-rules (cdr fns) interp-st state)))
    (mv (append rules1 rules2) interp-st))
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
	     (fgl-good-fgl-rules-p rules))))


(define interp-st-if-rules ((thenfns pseudo-fnsymlist-p) (elsefns pseudo-fnsymlist-p) interp-st state)
  :returns (mv (then-rules fgl-rulelist-p)
	       (else-rules fgl-rulelist-p)
	       (if-rules fgl-rulelist-p)
	       new-interp-st)
  (b* (((mv then-rules interp-st) (interp-st-branch-merge-fnlist-rules thenfns interp-st state))
       ((mv else-rules interp-st) (interp-st-branch-merge-fnlist-rules elsefns interp-st state))
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


(local (in-theory (enable fgl-interp-bfr-listp-rules)))
(local (in-theory (disable member-equal)))


(local (in-theory (enable fgl-interp-scratch-isomorphic-rules)))


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
    :prepwork ((local (in-theory (enable bfr-listp-when-not-member-witness)))
	       (local (in-theory (disable bvar-db-wfp$c-updater-independence))))
    (b* ((interp-st (interp-st-prof-push (fgl-rule->rune rule) interp-st))
         (rule (fgl-rule-fix rule))
         ((fgl-interp-value successp ans)
	  (fgl-primitive-fncall-stub (fgl-rule-primitive->name rule) fn args interp-st state))
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
					    (interp-st->logicman interp-st))
		    (interp-st-bvar-db-ok new-interp-st env)
		    (not (interp-st->errmsg new-interp-st)))
	       (equal (fgl-ev-context-fix contexts
					  (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
		      (fgl-ev-context-fix contexts
					  (fgl-object-eval (g-apply fn args) env (interp-st->logicman interp-st))))))

    (defret return-values-correct-of-<fn>
      (equal (list . <values>)
	     <call>))))


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


(local (defthm fgl-equivp-correct-for-fgl-ev
         (implies (and (fgl-ev-meta-extract-global-facts)
		       (fgl-equivp fn (w state)))
		  (fgl-ev (cmr::equiv-rel-term fn) a))
         :hints (("goal" :use ((:functional-instance fgl-equivp-correct
				(rules-ev fgl-ev)
				(rules-ev-list fgl-ev-list)
				(rules-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
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
				(rules-ev-falsify fgl-ev-falsify)))))))


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
				  (obj obj) (st st)))
		    :in-theory (enable fgl-ev-theoremp)))))

  (local (defthm fgl-ev-when-falsify
	   (implies (fgl-ev x (fgl-ev-falsify x))
		    (fgl-ev x a))
	   :hints (("goal" :use fgl-ev-falsify))))

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


(defret stack-equiv-except-top-bindings-of-fgl-rewrite-relieve-hyp-synp
  (implies (equal logicman (interp-st->logicman new-interp-st))
	   (stack-equiv-except-top-bindings
	    (fgl-major-stack-concretize
	     (interp-st->stack new-interp-st)
	     env logicman)
	    (fgl-major-stack-concretize
	     (interp-st->stack interp-st)
	     env (interp-st->logicman interp-st))))
  :hints(("Goal" :in-theory (enable stack-equiv-except-top-bindings
                                    fgl-rewrite-relieve-hyp-synp
				    stack$a-set-bindings
				    fgl-major-stack-concretize
				    fgl-major-frame-concretize)))
  :fn fgl-rewrite-relieve-hyp-synp)


(define fgl-rewrite-relieve-hyp-match-assums-index ((idx natp)
                                                    (hyp pseudo-termp)
                                                    (negatedp)
                                                    (interp-st interp-st-bfrs-ok))
  :guard (stobj-let ((logicman (interp-st->logicman interp-st))
		     (bvar-db (interp-st->bvar-db interp-st)))
		    (ok)
		    (and (bfr-varname-p idx)
                         (<= (base-bvar bvar-db) idx))
		    ok)
  :guard-hints (("goal" :in-theory (enable bfr-varname-p
					   interp-st-pathcond-assume)))
  :returns (mv successp new-interp-st)
  (b* ((term (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
                        (term) (get-bvar->term idx bvar-db) term))
       ((mv unify-ok bindings)
        ;; minor bindings should be irrelevant because we only do this at the toplevel of a hyp
        (fgl-unify-term/gobj hyp term (interp-st-bindings interp-st)
			     (interp-st-bfrstate)))
       ((unless unify-ok)
        (mv nil interp-st))
       (bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
		       (bfr) (bfr-var idx) bfr))
       ((mv contra interp-st)
        (interp-st-pathcond-assume (if negatedp bfr (interp-st-bfr-not bfr)) interp-st))
       ((unless contra)
        (b* ((interp-st (interp-st-pathcond-rewind interp-st)))
	  (mv nil interp-st)))
       ;; Negation of the variable is contradicted by the path condition, which
       ;; means the variable represents a curently valid assumption.  So set
       ;; the bindings and continue.
       (interp-st (interp-st-set-bindings bindings interp-st)))
    (mv t interp-st))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
		  (bfr-varname-p idx (interp-st->logicman interp-st))
		  (<= (base-bvar (interp-st->bvar-db interp-st)) (nfix idx)))
	     (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable bfr-varname-p))))

  (defret interp-st-get-of-<fn>
    (implies (not (member-equal (interp-st-field-fix key)
				'(:pathcond :constraint :stack)))
	     (Equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st)))
    :hints(("Goal" :in-theory (enable interp-st-pathcond-assume
				      interp-st-pathcond-rewind))))

  (defret interp-st-scratch-isomorphic-of-<fn>
    (interp-st-scratch-isomorphic new-interp-st interp-st))

  (defret <fn>-preserves-pathcond-enabledp
    (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	 (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-preserves-pathcond-stack-length
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (equal (pathcond-rewind-stack-len
		     mode
		     (interp-st->pathcond new-interp-st))
		    (pathcond-rewind-stack-len
		     mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond-rewind-ok
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
		  (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond
    (implies (interp-st-bfrs-ok interp-st)
	     (equal (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond new-interp-st)
		     (interp-st->logicman interp-st))
		    (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond interp-st)
		     (interp-st->logicman interp-st)))))

  (defret <fn>-preserves-pathcond-eval
    (implies (interp-st-bfrs-ok interp-st)
	     (equal (logicman-pathcond-eval
		     env
		     (interp-st->pathcond new-interp-st)
		     (interp-st->logicman interp-st))
		    (logicman-pathcond-eval
		     env
		     (interp-st->pathcond interp-st)
		     (interp-st->logicman interp-st)))))

  (defret <fn>-constraint-same
    (implies (interp-st-bfrs-ok interp-st)
	     (iff (logicman-pathcond-eval
		   env
		   (interp-st->constraint new-interp-st)
		   (interp-st->logicman interp-st))
		  (logicman-pathcond-eval
		   env
		   (interp-st->constraint interp-st)
		   (interp-st->logicman interp-st)))))

  (defret <fn>-stack-equiv-except-top-bindings
    (stack-equiv-except-top-bindings
     (interp-st->stack new-interp-st)
     (interp-st->stack interp-st))))


(define fgl-rewrite-relieve-hyp-match-assums-indices ((indices nat-listp)
                                                      (hyp pseudo-termp)
                                                      (negatedp)
                                                      (interp-st interp-st-bfrs-ok))
  :guard (interp-st-bvar-list-okp indices interp-st)
  :guard-hints (("goal" :in-theory (enable interp-st-bvar-list-okp
					   bvar-list-okp$c
					   bfr-varname-p)))
  :returns (mv successp new-interp-st)
  (b* (((when (atom indices)) (mv nil interp-st))
       ((mv successp interp-st)
        (fgl-rewrite-relieve-hyp-match-assums-index (car indices) hyp negatedp interp-st))
       ((when successp) (mv t interp-st)))
    (fgl-rewrite-relieve-hyp-match-assums-indices (cdr indices) hyp negatedp interp-st))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-list-okp indices interp-st))
	     (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret interp-st-get-of-<fn>
    (implies (not (member-equal (interp-st-field-fix key)
				'(:pathcond :constraint :stack)))
	     (Equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st))))

  (defret interp-st-scratch-isomorphic-of-<fn>
    (interp-st-scratch-isomorphic new-interp-st interp-st))

  (defret <fn>-preserves-pathcond-enabledp
    (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	 (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-preserves-pathcond-stack-length
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (equal (pathcond-rewind-stack-len
		     mode
		     (interp-st->pathcond new-interp-st))
		    (pathcond-rewind-stack-len
		     mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond-rewind-ok
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
		  (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-list-okp indices interp-st))
	     (equal (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond new-interp-st)
		     (interp-st->logicman interp-st))
		    (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond interp-st)
		     (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret <fn>-constraint-same
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-list-okp indices interp-st))
	     (iff (logicman-pathcond-eval
		   env
		   (interp-st->constraint new-interp-st)
		   (interp-st->logicman interp-st))
		  (logicman-pathcond-eval
		   env
		   (interp-st->constraint interp-st)
		   (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret <fn>-stack-equiv-except-top-bindings
    (stack-equiv-except-top-bindings
     (interp-st->stack new-interp-st)
     (interp-st->stack interp-st))))


(define fgl-rewrite-relieve-hyp-match-assums1 ((hyp pseudo-termp)
                                               (negatedp)
                                               (interp-st interp-st-bfrs-ok))
  :returns (mv successp give-up new-interp-st)
  :guard-hints (("goal" :in-theory (enable interp-st-bvar-fn-term-indices
					   interp-st-bvar-list-okp)))
  :prepwork ((local (defthm bvar-list-okp-of-bvar-fn-term-indices1
		      (implies (and (bvar-fn-indices-okp$c fi bvar-db)
				    (pseudo-fnsym-p fn))
			       (bvar-list-okp$c (cdr (hons-assoc-equal fn fi)) bvar-db))
		      :hints(("Goal" :in-theory (enable bvar-fn-indices-okp$c
							hons-assoc-equal)))))
	     (local (defthm bvar-list-okp-of-bvar-fn-term-indices
		      (implies (bvar-db-wfp$c bvar-db)
			       (bvar-list-okp$c (bvar-fn-term-indices$c fn bvar-db) bvar-db))
		      :hints(("Goal" :in-theory (enable bvar-db-wfp$c
							bvar-fn-term-indices$c)))))
	     (local (defthm interp-stp-implies-bvar-db-wfp
		      (implies (interp-stp interp-st)
			       (bvar-db-wfp$c (interp-st->bvar-db interp-st)))
		      :hints(("Goal" :in-theory (enable interp-stp
							interp-st->bvar-db))))))
  (pseudo-term-case hyp
    :fncall (b* ((indices (interp-st-bvar-fn-term-indices hyp.fn interp-st))
		 ((mv successp interp-st)
		  (fgl-rewrite-relieve-hyp-match-assums-indices indices hyp negatedp interp-st)))
	      (mv successp (not successp) interp-st))
    :otherwise (mv nil t interp-st))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret interp-st-get-of-<fn>
    (implies (not (member-equal (interp-st-field-fix key)
				'(:pathcond :constraint :stack)))
	     (Equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st))))

  (defret interp-st-scratch-isomorphic-of-<fn>
    (interp-st-scratch-isomorphic new-interp-st interp-st))

  (defret <fn>-preserves-pathcond-enabledp
    (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	 (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-preserves-pathcond-stack-length
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (equal (pathcond-rewind-stack-len
		     mode
		     (interp-st->pathcond new-interp-st))
		    (pathcond-rewind-stack-len
		     mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond-rewind-ok
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
		  (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond
    (implies (interp-st-bfrs-ok interp-st)
	     (equal (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond new-interp-st)
		     (interp-st->logicman interp-st))
		    (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond interp-st)
		     (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret <fn>-constraint-same
    (implies (and (interp-st-bfrs-ok interp-st))
	     (iff (logicman-pathcond-eval
		   env
		   (interp-st->constraint new-interp-st)
		   (interp-st->logicman interp-st))
		  (logicman-pathcond-eval
		   env
		   (interp-st->constraint interp-st)
		   (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret <fn>-stack-equiv-except-top-bindings
    (stack-equiv-except-top-bindings
     (interp-st->stack new-interp-st)
     (interp-st->stack interp-st))))


(define fgl-rewrite-relieve-hyp-match-assums0 ((hyp pseudo-termp)
                                               (interp-st interp-st-bfrs-ok))
  :returns (mv successp give-up new-interp-st)
  (b* (((mv negatedp core-hyp)
        (pseudo-term-case hyp
	  :fncall (if (and (eq hyp.fn 'not) (eql (len hyp.args) 1))
		      (mv t (car hyp.args))
		    (mv nil hyp))
	  :otherwise (mv nil hyp))))
    (fgl-rewrite-relieve-hyp-match-assums1 core-hyp negatedp interp-st))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret interp-st-get-of-<fn>
    (implies (not (member-equal (interp-st-field-fix key)
				'(:pathcond :constraint :stack)))
	     (Equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st))))

  (defret interp-st-scratch-isomorphic-of-<fn>
    (interp-st-scratch-isomorphic new-interp-st interp-st))

  (defret <fn>-preserves-pathcond-enabledp
    (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	 (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-preserves-pathcond-stack-length
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (equal (pathcond-rewind-stack-len
		     mode
		     (interp-st->pathcond new-interp-st))
		    (pathcond-rewind-stack-len
		     mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond-rewind-ok
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
		  (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond
    (implies (interp-st-bfrs-ok interp-st)
	     (equal (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond new-interp-st)
		     (interp-st->logicman interp-st))
		    (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond interp-st)
		     (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret <fn>-constraint-same
    (implies (and (interp-st-bfrs-ok interp-st))
	     (iff (logicman-pathcond-eval
		   env
		   (interp-st->constraint new-interp-st)
		   (interp-st->logicman interp-st))
		  (logicman-pathcond-eval
		   env
		   (interp-st->constraint interp-st)
		   (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret <fn>-stack-equiv-except-top-bindings
    (stack-equiv-except-top-bindings
     (interp-st->stack new-interp-st)
     (interp-st->stack interp-st))))


(define fgl-rewrite-relieve-hyp-match-assums ((hyp pseudo-termp)
                                              (interp-st interp-st-bfrs-ok))
  :returns (mv successp give-up new-interp-st)
  (pseudo-term-case hyp
    :fncall (if (and (eq hyp.fn 'match-assums)
		     (eql (len hyp.args) 1))
		(if (interp-st-minor-bindings interp-st)
		    (prog2$ (cw "UNEXPECTED -- minor bindings when trying to match assumptions~%")
			    (mv nil t interp-st))
		  (fgl-rewrite-relieve-hyp-match-assums0 (car hyp.args) interp-st))
	      (mv nil nil interp-st))
    :otherwise (mv nil nil interp-st))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p))))

  (defret interp-st-get-of-<fn>
    (implies (not (member-equal (interp-st-field-fix key)
				'(:pathcond :constraint :stack)))
	     (Equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st))))

  (defret interp-st-scratch-isomorphic-of-<fn>
    (interp-st-scratch-isomorphic new-interp-st interp-st))

  (defret <fn>-preserves-pathcond-enabledp
    (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	 (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-preserves-pathcond-stack-length
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (equal (pathcond-rewind-stack-len
		     mode
		     (interp-st->pathcond new-interp-st))
		    (pathcond-rewind-stack-len
		     mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond-rewind-ok
    (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
	     (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
		  (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

  (defret <fn>-preserves-pathcond
    (implies (and (interp-st-bfrs-ok interp-st)
		  (equal logicman (interp-st->logicman interp-st)))
	     (equal (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond new-interp-st)
		     logicman)
		    (logicman-pathcond-eval-checkpoints!
		     env
		     (interp-st->pathcond interp-st)
		     logicman))))

  (defret <fn>-preserves-pathcond-eval
    (implies (and (interp-st-bfrs-ok interp-st)
		  (equal logicman (interp-st->logicman interp-st)))
	     (equal (logicman-pathcond-eval
		     env
		     (interp-st->pathcond new-interp-st)
		     logicman)
		    (logicman-pathcond-eval
		     env
		     (interp-st->pathcond interp-st)
		     logicman)))
    :hints(("Goal" :in-theory (e/d (logicman-pathcond-eval-checkpoints!)
				   (<fn>
				    <fn>-preserves-pathcond))
	    :cases ((nth *pathcond-enabledp* (interp-st->pathcond interp-st)))
	    :use <fn>-preserves-pathcond)))

  (defret <fn>-constraint-same
    (implies (and (interp-st-bfrs-ok interp-st)
		  (equal logicman (interp-st->logicman interp-st)))
	     (iff (logicman-pathcond-eval
		   env
		   (interp-st->constraint new-interp-st)
		   logicman)
		  (logicman-pathcond-eval
		   env
		   (interp-st->constraint interp-st)
		   logicman))))

  (defret <fn>-stack-equiv-except-top-bindings
    (stack-equiv-except-top-bindings
     (interp-st->stack new-interp-st)
     (interp-st->stack interp-st))))


(define is-fncall ((fnname pseudo-fnsym-p)
                   (x pseudo-termp))
  (pseudo-term-case x
    :fncall (eq x.fn (pseudo-fnsym-fix fnname))
    :otherwise nil))


(define interp-st-try-equivalences ((dont)
                                    (x fgl-object-p)
                                    (interp-st interp-st-bfrs-ok)
                                    state)
  :returns (mv (xobj fgl-object-p) new-interp-st
	       (new-state (equal new-state state)))
  :guard (fgl-object-bfrs-ok x (interp-st-bfrstate))
  (b* (((when (or dont
		  (not (fgl-term-obj-p x))
		  (interp-flags->hide (interp-st->flags interp-st))))
        (fgl-interp-value (fgl-object-fix x)))
       (contexts (interp-st->equiv-contexts interp-st))
       ((mv error val interp-st)
        (stobj-let ((pathcond (interp-st->pathcond interp-st))
		    (logicman (interp-st->logicman interp-st))
		    (bvar-db (interp-st->bvar-db interp-st)))
		   (error val pathcond)
		   (try-equivalences-loop
		    ;; BOZO this isn't necessarily the right place to hons-copy it.
		    (hons-copy x) contexts 100 ;; bozo, configure reclimit for try-equivalences-loop?
		    pathcond bvar-db logicman state)
		   (mv error val interp-st)))
       ((when error)
        (fgl-interp-error
         :msg (fgl-msg "Try-equivalences-loop failed: ~@0" error))))
    (fgl-interp-value val))
  ///
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (interp-st-bfrs-ok interp-st)
	     (interp-st-bfrs-ok new-interp-st)))

  (defret lbfr-listp-of-<fn>
    (implies (and (fgl-object-bfrs-ok x (interp-st-bfrstate))
		  (interp-st-bfrs-ok interp-st)
		  (logicman-extension-p logicman (interp-st->logicman interp-st)))
	     (lbfr-listp (fgl-object-bfrlist xobj))))

  (defret interp-st-get-of-<fn>
    (implies (not (member-equal (interp-st-field-fix key) '(:pathcond :errmsg :debug-info :debug-stack)))
	     (Equal (interp-st-get key new-interp-st)
		    (interp-st-get key interp-st))))

  (defret pathcond-of-<fn>
    (pathcond-equiv (interp-st->pathcond new-interp-st)
		    (interp-st->pathcond interp-st)))

  (defret pathcond-enabledp-of-<fn>
    (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
	 (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret <fn>-preserves-errmsg
    (let ((errmsg (interp-st->errmsg interp-st)))
      (implies errmsg
	       (equal (interp-st->errmsg new-interp-st) errmsg))))

  (local (acl2::use-trivial-ancestors-check))
  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
	     (not (equal (interp-st->errmsg new-interp-st) :unreachable)))))


(define fgl-rule-arg-modes-allow-args-p ((modes fgl-rule-arg-mode-list-p)
                                         (args fgl-arglist-p))
  :returns (allowedp booleanp)
  ;; An empty mode list is the default: all arguments must be bound.
  (b* (((when (atom modes)) (fgl-arglist-all-boundp args))
       ((when (atom args)) nil)
       (unboundp (fgl-arg-case (car args) :unbound)))
    (and (case (fgl-rule-arg-mode-fix (car modes))
	   (:bound (not unboundp))
	   (:unbound unboundp)
	   (:either t)
	   (otherwise nil))
	 (fgl-rule-arg-modes-allow-args-p (cdr modes) (cdr args)))))


(local (in-theory (enable fgl-arg-bfrlist-of-fgl-arg-obj)))


(defthm stack-add-bindings-under-major-stack-scratch-isomorphic
  (major-stack-scratch-isomorphic
   (stack-add-bindings bindings stack) stack)
  :hints (("Goal" :in-theory (enable stack-add-bindings))))

(defthm stack-add-bindings-under-stack-equiv-except-top-bindings
  (stack-equiv-except-top-bindings
   (stack-add-bindings bindings stack) stack)
  :hints (("Goal" :in-theory (enable stack-add-bindings))))


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
		       2020 (pseudo-term-binding-count x) 30)
	:well-founded-relation acl2::nat-list-<
	:verify-guards nil
	:measure-debug t
	:returns (mv xbfr
		     new-interp-st new-state)
	(b* (((interp-st-bind
	       (equiv-contexts (fgl-interp-test-equiv-contexts (interp-st->equiv-contexts interp-st))))
	      ;; (was-fncall-p (pseudo-term-case x :call))
	      (left-to-rightp (pseudo-term-case x :fncall (eq x.fn 'left-to-right) :otherwise nil))
	      ((fgl-interp-recursive-call xobj)
	       (fgl-interp-term x interp-st state))
	      ((fgl-interp-value xobj)
	       (interp-st-try-equivalences (fgl-hide-term-p x) xobj interp-st state))))
	  ;; already-rewritten: even though we rewrite the object under iff
	  ;; context above, it can often benefit from rewriting under iff again
	  ;; to ensure that things are in normal form before they are added to
	  ;; the bvar-db.  We used to assume that if the term was a function
	  ;; call, then it had already been rewritten under iff. But e.g., if
	  ;; our input here is (foo z), with definition (foo z) = z, z is bound
	  ;; to (bar y), and we have a rule (iff (bar y) (baz y)) expecting we
	  ;; therefore won't see calls of bar in the bvar-db, this expectation will
	  ;; be violated if we say already-rewritten (because (foo z) is a
	  ;; function call) here.
	  (fgl-interp-simplify-if-test nil left-to-rightp xobj interp-st state)))

      (define fgl-interp-test-under-pathcond ((x pseudo-termp)
					      (interp-st interp-st-bfrs-ok)
					      state)
	;; Wrapper for fgl-interp-test that additionally checks the result against the path condition.
	;; Don't need use for an IF test because it's going to do the same thing anyway.
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (pseudo-term-binding-count x) 35)
	:returns (mv xbfr new-interp-st new-state)
	(b* (((fgl-interp-value xbfr)
	      (fgl-interp-test x interp-st state))
	     ((when (interp-st->errmsg interp-st))
	      (fgl-interp-value nil))
	     ((mv contra1 interp-st)
	      (interp-st-pathcond-assume xbfr interp-st))
	     (interp-st (if contra1
			    interp-st
			  (interp-st-pathcond-rewind interp-st)))
	     ((mv contra2 interp-st)
	      (interp-st-pathcond-assume (interp-st-bfr-not xbfr) interp-st))
	     (interp-st (if contra2
			    interp-st
			  (interp-st-pathcond-rewind interp-st)))
	     ((when (and contra1 contra2))
	      (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
		(fgl-interp-value nil))))
	  (fgl-interp-value (cond (contra1 nil)
				  (contra2 t)
				  (t xbfr)))))

      (define fgl-interp-postprocess-rewritten-obj ((no-equivs)
						    (x fgl-object-p)
						    (interp-st interp-st-bfrs-ok)
						    state)
	:guard (fgl-object-bfrs-ok x (interp-st-bfrstate))
	:measure (list (nfix (interp-st->reclimit interp-st)) 1600 0 0)
	:returns (mv (xobj fgl-object-p) new-interp-st new-state)
	(b* (((fgl-interp-value val)
	      (interp-st-try-equivalences no-equivs x interp-st state))
	     ((when (and (not no-equivs)
			 (not (interp-flags->hide (interp-st->flags interp-st)))
			 (interp-st-boolean-fncall-p val interp-st (w state))))
	      (b* (((fgl-interp-value xbfr) (fgl-interp-simplify-if-test
					     nil nil val interp-st state)))
		(fgl-interp-value (mk-g-boolean xbfr)))))
	  (fgl-interp-value val)))


      (define fgl-interp-term-top ((x pseudo-termp)
				   (interp-st interp-st-bfrs-ok)
				   state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (pseudo-term-binding-count x) 40)
	:returns (mv
		  (xobj fgl-object-p)
		  new-interp-st new-state)
	(b* ((contexts (interp-st->equiv-contexts interp-st))
	     ((when (member-eq 'iff contexts))
	      (b* (((fgl-interp-value xbfr) (fgl-interp-test-under-pathcond x interp-st state)))
		(fgl-interp-value (mk-g-boolean xbfr))))
	     ((fgl-interp-recursive-call xobj)
	      (fgl-interp-term x interp-st state)))
	  (fgl-interp-postprocess-rewritten-obj
	   (fgl-hide-term-p x) ;; don't use equivalence replacements if x is a hide term
	   xobj interp-st state)))
      ;;    ((when (interp-st-boolean-fncall-p xobj interp-st (w state)))
      ;;     (b* (((fgl-interp-value xbfr) (fgl-interp-simplify-if-test
      ;;                                    nil nil xobj interp-st state)))
      ;;       (fgl-interp-value (mk-g-boolean xbfr)))))
      ;; (fgl-interp-value xobj)))

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
	    (b* ((interp-st (interp-st-push-scratch-fnsym x.fn interp-st))
		 ((mv val interp-st state)
		  (b* (((fgl-interp-recursive-call successp ans)
			(fgl-interp-fncall-special x.fn x.args interp-st state))
		       ((when successp)
			(fgl-interp-value ans)))
		    (fgl-interp-fncall-nonspecial-top x.fn x.args interp-st state)))
		 ((mv & interp-st) (interp-st-pop-scratch-fnsym interp-st)))
	      (fgl-interp-value val)))))

      (define fgl-interp-fncall-nonspecial-top ((fn pseudo-fnsym-p)
                                                (args pseudo-term-listp)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (pseudo-term-list-binding-count args) 100)
	:returns (mv
		  (xobj fgl-object-p)
		  new-interp-st new-state)
	(b* ((argcontexts (fgl-interp-arglist-equiv-contexts (interp-st->equiv-contexts interp-st)
							     fn (len args)
							     (interp-st->congruence-rules interp-st)
							     (interp-st->id-congruence-rules interp-st)
							     (w state)))

	     ((fgl-interp-recursive-call args)
	      (fgl-interp-arglist args argcontexts interp-st state))
	     (all-boundp (fgl-arglist-all-boundp args))
	     (args (fgl-arglist-substitute-newly-bound-exec all-boundp args (interp-st-bindings interp-st)))
	     (all-boundp (fgl-arglist-all-boundp args))
	     ((when (interp-flags->hide (interp-st->flags interp-st)))
	      (if all-boundp
		  (mv (g-apply fn (fgl-arglist->objects args)) interp-st state)
		(b* ((interp-st (interp-st-set-error :abort-rewrite interp-st)))
		  (mv nil interp-st state)))))
	  (fgl-interp-fncall-casesplit fn args interp-st state)))

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

	  ((abort-rewrite 1)
	   (b* ((interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count (first args)) interp-st))
		(interp-st (interp-st-set-error :abort-rewrite interp-st)))
	     (fgl-interp-value nil)))

	  ((syntax-interp-fn 2)
	   (b* ((interp-st (interp-st-incr-term-index (+ (fgl-minor-frame-subterm-count (first args))
							 (fgl-minor-frame-subterm-count (second args)))
						      interp-st)))
	     (fgl-interp-syntax-interp (first args)
				       (second args)
				       interp-st state)))

	  ((disallow-boolean-var-intro 1)
	   (b* ((flags (interp-st->flags interp-st))
		(new-flags (!interp-flags->intro-bvars nil flags))
		((interp-st-bind
		  (flags new-flags flags))
		 ((fgl-interp-value val)
		  (fgl-interp-term-top (first args) interp-st state))))
	     (fgl-interp-value val)))

	  ((handle-error-fn 3)
	   (fgl-interp-handle-error (first args) (second args) (third args) interp-st state))

	  ((assume-fn 3)
	   (fgl-interp-assume (first args)
			      (second args)
			      (third args)
			      interp-st state))

	  ((narrow-equiv 2)
	   (fgl-interp-narrow-equiv (first args)
				    (second args)
				    interp-st state))

	  ((fgl-time-fn 2)
	   (fgl-interp-time$ (first args)
			     (second args)
			     interp-st state))

	  ((fgl-interp-obj 1)
	   (fgl-interp-fgl-interp-obj (first args)
				      interp-st state))

	  ((fgl-hide 1)
	   (b* ((flags (interp-st->flags interp-st))
		(new-flags (!interp-flags->hide t flags))
		((interp-st-bind
		  (flags new-flags flags))
		 ((fgl-interp-value val)
		  (fgl-interp-term-top (first args) interp-st state))))
	     (fgl-interp-value val)))

	  ((trigger-constraints 1)
	   (b* (((interp-st-bind
		  (equiv-contexts (fgl-interp-test-equiv-contexts (interp-st->equiv-contexts interp-st))))
		 ((fgl-interp-recursive-call val)
		  (fgl-interp-term-top (first args) interp-st state)))
		((fgl-interp-value) (fgl-interp-add-constraints val interp-st state)))
	     (fgl-interp-value nil)))

	  ((conditionalize1 3 t) ;; explicit success flag
	   (b* (((list freevar test term) args))
	     (fgl-interp-conditionalize-bind freevar test term term interp-st state)))
	  ((conditionalize2 4 t) ;; explicit success flag
	   (b* (((list freevar test term on-unreach) args))
	     (fgl-interp-conditionalize-bind freevar test term on-unreach interp-st state)))))

      (define fgl-interp-arglist ((args pseudo-term-listp)
				  (argcontexts equiv-argcontexts-p)
				  (interp-st interp-st-bfrs-ok)
				  state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (pseudo-term-list-binding-count args) 20)
	:returns (mv
		  (arg-objs fgl-arglist-p)
		  new-interp-st new-state)
	(b* (((when (atom args)) (fgl-interp-value nil))
	     (arg1 (car args))
	     ((when (pseudo-term-case arg1
		      :var (and (not (assoc-eq arg1.name (interp-st-minor-bindings interp-st)))
				(not (assoc-eq arg1.name (interp-st-bindings interp-st))))
		      :otherwise nil))
	      (b* ((interp-st (interp-st-incr-term-index 1 interp-st))
		   ((fgl-interp-value rest)
		    (fgl-interp-arglist (cdr args) (equiv-argcontexts-rest argcontexts) interp-st state)))
		(fgl-interp-value (cons (fgl-arg-unbound (pseudo-term-var->name arg1)) rest))))
	     ((interp-st-bind
	       (equiv-contexts (equiv-argcontexts-first argcontexts)))
	      ((fgl-interp-recursive-call arg1)
	       (fgl-interp-term-top (car args) interp-st state)))
	     ;; ((when err) (mv nil interp-st state))
	     (interp-st (interp-st-push-scratch-fgl-obj arg1 interp-st))
	     ((fgl-interp-value rest)
	      (fgl-interp-arglist (cdr args) (equiv-argcontexts-rest argcontexts) interp-st state))
	     ((mv arg interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
	  (fgl-interp-value (cons (fgl-arg-obj arg) rest))))

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
	     (interp-st (interp-st-push-scratch-formals x1.formals interp-st))
	     ((fgl-interp-recursive-call args)
	      (fgl-interp-lambda-arglist x1.args interp-st state))
	     ((mv & interp-st) (interp-st-pop-scratch-formals interp-st))
	     ;; ((when err) (mv interp-st state))
	     (interp-st (interp-st-add-minor-bindings (pairlis$ x1.formals args) interp-st)))
	  (fgl-interp-bindinglist (cdr bindings) interp-st state)))

      (define fgl-interp-fncall-casesplit ((fn pseudo-fnsym-p)
					   (args fgl-arglist-p)
					   (interp-st interp-st-bfrs-ok)
					   state)

	:guard (fgl-arglist-bfrs-ok args (interp-st-bfrstate))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2010 0 14)
	:returns (mv (ans fgl-object-p)
		     new-interp-st new-state)
	(b* ((ite (and (fgl-arglist-all-boundp args)
		       (fgl-objectlist-find-ite (fgl-arglist->objects args))))
	     ((unless (and** ite
			     ;; bozo should this be another flag?
			     (interp-flags->branch-on-ifs (interp-st->flags interp-st))
			     (fgl-function-mode->split-ifs
			      (fgl-function-mode-lookup
			       fn (fgl-config->function-modes
				   (interp-st->config interp-st))))))
	      (fgl-interp-fncall fn args interp-st state))
	     (test (g-ite->test ite))
	     ((mv then-args else-args) (fgl-objectlist-split test (fgl-arglist->objects args)))
	     (interp-st (interp-st-push-scratch-fgl-objlist else-args interp-st))
	     (interp-st (interp-st-push-scratch-fgl-objlist then-args interp-st))
	     ((fgl-interp-recursive-call testbfr)
	      ;; already-rewritten: presumably since it already ended up as the
	      ;; test of an IF.
	      (fgl-interp-simplify-if-test t nil test interp-st state))
	     ((mv then-args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))
	     ((mv else-args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st)))
	  (fgl-interp-fncall-casesplit-branches testbfr fn then-args else-args interp-st state)))

      (define fgl-interp-fncall-casesplit-branches ((testbfr interp-st-bfr-p)
						    (fn pseudo-fnsym-p)
						    (then-args fgl-objectlist-p)
						    (else-args fgl-objectlist-p)
						    (interp-st interp-st-bfrs-ok)
						    state)

	:guard (and (fgl-objectlist-bfrs-ok then-args (interp-st-bfrstate))
		    (fgl-objectlist-bfrs-ok else-args (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2010 0 13)
	:returns (mv (ans fgl-object-p)
		     new-interp-st new-state)
	(b* ((interp-st (interp-st-push-scratch-fgl-objlist else-args interp-st))
	     (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
	     ((fgl-interp-recursive-call then-unreachable then-val)
	      (fgl-maybe-interp-fncall-casesplit testbfr fn then-args interp-st state))
	     ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
	     ((mv else-args interp-st) (interp-st-pop-scratch-fgl-objlist interp-st)))
	  (fgl-interp-fncall-casesplit-else testbfr fn then-val then-unreachable else-args interp-st state)))

      (define fgl-interp-fncall-casesplit-else ((testbfr interp-st-bfr-p)
                                                (fn pseudo-fnsym-p)
                                                (then-val fgl-object-p)
                                                then-unreachable
                                                (else-args fgl-objectlist-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
	:guard (and (fgl-object-bfrs-ok then-val (interp-st-bfrstate))
		    (fgl-objectlist-bfrs-ok else-args (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st)) 2010 0 12)
	:returns (mv (ans fgl-object-p) new-interp-st new-state)
	(b* ((interp-st (interp-st-push-scratch-fgl-obj then-val interp-st))
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
	:guard (fgl-objectlist-bfrs-ok args (interp-st-bfrstate))
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
	       (fgl-interp-fncall-casesplit fn (fgl-objectlist->arglist args) interp-st state)))
	     (interp-st (interp-st-pathcond-rewind interp-st))
	     ((when (eq (interp-st->errmsg interp-st) :unreachable))
	      (b* ((interp-st (update-interp-st->errmsg nil interp-st))
		   ((mv status interp-st state)
		    ;; Check whether we're still in an unreachable state without the new assumption.
		    (interp-st-sat-check
		     (fgl-reachability-sat-check-config-wrapper
		      (fgl-config->sat-config-reachability (interp-st->config interp-st)))
		     t interp-st state))
		   ((when (eq status :unsat))
		    ;; unreachable outside the new assumption as well
		    (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
		      (fgl-interp-value nil nil))))
		(fgl-interp-value t nil))))
	  (fgl-interp-value nil ans)))

      (define fgl-interp-fncall ((fn pseudo-fnsym-p)
                                 (args fgl-arglist-p)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
	:guard (bfr-listp (fgl-arglist-bfrlist args) (interp-st-bfrstate))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1700 0 0)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* ((fn (pseudo-fnsym-fix fn))
	     ((fgl-function-mode fn-mode)
	      (fgl-function-mode-lookup fn (fgl-config->function-modes
					    (interp-st->config interp-st))))
	     ((mv successp ans)
	      (fncall-try-concrete-eval fn args fn-mode.dont-concrete-exec
					(member-eq 'unequiv (interp-st->equiv-contexts interp-st))
					state))
	     ((when successp)
	      (b* ((interp-st (interp-st-tick-steplimit interp-st)) ;; count execution of the function as a step
		   (interp-st (interp-st-prof-simple-increment-exec fn interp-st)))
		(fgl-interp-value ans)))
	     (interp-st (interp-st-push-scratch-fgl-arglist args interp-st))
	     ((fgl-interp-recursive-call successp ans)
	      (fgl-rewrite-fncall fn args fn-mode.dont-rewrite interp-st state))
	     ((mv args interp-st) (interp-st-pop-scratch-fgl-arglist interp-st))
	     ((unless (or successp
			  (fgl-arglist-all-boundp args)))
	      (b* ((interp-st (interp-st-set-error :abort-rewrite interp-st)))
		(fgl-interp-value nil)))
	     (ans (if successp ans (g-apply fn (fgl-arglist->objects args)))))
	  (fgl-interp-postprocess-rewritten-obj (eq fn 'fgl-hide) ans interp-st state)))

      (define fgl-rewrite-fncall ((fn pseudo-fnsym-p)
				  (args fgl-arglist-p)
				  (dont)
				  (interp-st interp-st-bfrs-ok)
				  state)
	:guard (fgl-arglist-bfrs-ok args (interp-st-bfrstate))
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
	     (interp-st (interp-st-push-scratch-fgl-arglist args interp-st))
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
		    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-arglist))
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
		    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-arglist))
	:measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 2)
	:returns (mv successp
		     (ans fgl-object-p)
		     new-interp-st new-state)
	;; Registration metadata gates every rule kind before application.
	(b* (((unless (and (fgl-rule->enabledp rule)
			   (fgl-rule-arg-modes-allow-args-p
			    (fgl-rule->arg-modes rule)
			    (interp-st-top-scratch-fgl-arglist interp-st))))
	      (fgl-interp-value nil nil)))
	  (fgl-rule-case rule
	    :rewrite (fgl-rewrite-try-rewrite rule fn interp-st state)
	    :meta (fgl-rewrite-try-meta rule fn interp-st state)
	    :primitive
	    (b* ((args (interp-st-top-scratch-fgl-arglist interp-st))
		 ((unless (fgl-arglist-all-boundp args))
		  (fgl-interp-value nil nil)))
	      (fgl-rewrite-try-primitive rule fn
					 (fgl-arglist->objects args)
					 interp-st state)))))

      (define fgl-rewrite-apply-rule-core ((tracep)
					   (rule fgl-rule-p)
					   (fn pseudo-fnsym-p)
					   (rev-subst pseudo-term-subst-p)
					   (hyps pseudo-term-listp)
					   (rhs pseudo-termp)
					   (rhs-equiv equiv-contextsp)
					   (interp-st interp-st-bfrs-ok)
					   state)
	:measure (list (nfix (interp-st->reclimit interp-st)) 9500 0 0)
	;; Note: "Successp" is a misnomer here. It indicates to our callers
	;; here that we should stop trying to apply rewrite rules, and just
	;; return the answer we produced. This is what we want when the rule
	;; actually succeeds, but also when we've run into an uncaught error.
	:returns (mv (failed-hyp acl2::maybe-natp :rule-classes :type-prescription)
		     (ans fgl-object-p)
		     (rev-bindings fgl-object-bindings-p)
		     new-interp-st new-state)
	(b* (((fgl-interp-recursive-call failed-hyp rev-bindings)
	      (fgl-rewrite-apply-rule-prep tracep rule fn rev-subst hyps interp-st state))
	     ((when (or failed-hyp (interp-st->errmsg interp-st)))
	      (mv failed-hyp nil nil interp-st state))
	     (interp-st (interp-st-push-scratch-fgl-bindings rev-bindings interp-st))

	     (interp-st (interp-st-set-term rhs interp-st))
	     (interp-st (interp-st-set-term-index nil interp-st))
	     ((interp-st-bind
	       (equiv-contexts rhs-equiv))
	      ((fgl-interp-value val)
	       ;; Note: Was interp-term-equivs
	       (fgl-interp-term rhs interp-st state)))
	     ((mv rev-bindings interp-st) (interp-st-pop-scratch-fgl-bindings interp-st)))
	  (mv nil val rev-bindings interp-st state)))

      ;; Relieve hypotheses and interpret the reverse substitution before the RHS.
      (define fgl-rewrite-apply-rule-prep (tracep
					   (rule fgl-rule-p)
					   (fn pseudo-fnsym-p)
					   (rev-subst pseudo-term-subst-p)
					   (hyps pseudo-term-listp)
					   (interp-st interp-st-bfrs-ok)
					   state)
	:measure (list (nfix (interp-st->reclimit interp-st)) 9400 0 0)
	:returns (mv (failed-hyp acl2::maybe-natp :rule-classes :type-prescription)
		     (rev-bindings fgl-object-bindings-p)
		     new-interp-st new-state)
	(b* ((backchain-limit (interp-st->backchain-limit interp-st))
	     ;; (hyps-flags  (!interp-flags->intro-bvars nil flags))
	     ((interp-st-bind
	       ;; (flags hyps-flags flags)
	       ;; NOTE: Even when in an unequiv context, we rewrite the hyps under IFF.
	       (equiv-contexts '(iff))
	       (backchain-limit (1- backchain-limit) backchain-limit))

	      ((fgl-interp-recursive-call failed-hyp)
	       (fgl-rewrite-relieve-hyps rule fn hyps tracep interp-st state)))

	     ((when (or** failed-hyp (interp-st->errmsg interp-st)))
	      (mv failed-hyp nil interp-st state))

	     ((interp-st-bind
	       ;; (flags hyps-flags flags)
	       ;; NOTE: Even when in an unequiv context, we rewrite the rev-subst under EQUAL.
	       (equiv-contexts nil))

	      ((fgl-interp-recursive-call rev-bindings)
	       (fgl-rewrite-reverse-subst rev-subst interp-st state)))

	     ((when (interp-st->errmsg interp-st))
	      (mv nil nil interp-st state)))
	  (mv nil rev-bindings interp-st state)))

      (define fgl-rewrite-apply-rule ((rule fgl-rule-p)
				      (fn pseudo-fnsym-p)
				      (bindings fgl-object-bindings-p)
				      (rev-subst pseudo-term-subst-p)
				      (hyps pseudo-term-listp)
				      (rhs pseudo-termp)
				      (rhs-equiv equiv-contextsp)
				      (interp-st interp-st-bfrs-ok)
				      state)
	:guard (fgl-object-bindings-bfrs-ok bindings (interp-st-bfrstate))
	:measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 0)
	;; Note: "Successp" is a misnomer here. It indicates to our callers
	;; here that we should stop trying to apply rewrite rules, and just
	;; return the answer we produced. This is what we want when the rule
	;; actually succeeds, but also when we've run into an uncaught error.
	:returns (mv successp
		     (ans fgl-object-p)
		     (new-bindings fgl-object-bindings-p)
		     new-interp-st new-state)
	(b* (((when (interp-st->errmsg interp-st))
	      ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
	      ;; If there was an error, we want to stop applying rules.
	      (fgl-interp-value t nil nil))
	     (rune (fgl-rule->rune rule))
	     (interp-st (interp-st-push-rule-frame rule bindings interp-st))
	     (interp-st (interp-st-prof-push rune interp-st))
	     ((mv tracep interp-st state) (fgl-trace-start rule fn interp-st state))

	     ((mv failed-hyp val rev-bindings interp-st state)
	      (fgl-rewrite-apply-rule-core
	       tracep rule fn rev-subst hyps rhs rhs-equiv interp-st state))

	     ((when (or** failed-hyp (interp-st->errmsg interp-st)))
	      (b* (((mv interp-st state)
		    (fgl-trace-failure-output failed-hyp rule fn tracep interp-st state))
		   (interp-st (interp-st-prof-pop-increment nil interp-st))
		   (interp-st (interp-st-pop-frame interp-st))
		   (interp-st (interp-st-cancel-error :intro-bvars-fail interp-st))
		   (interp-st (interp-st-cancel-error :abort-rewrite interp-st)))
		;; See comment about successp above -- we want to stop applying
		;; rewrites if there was an uncaught error.  Otherwise, we've
		;; just failed to relieve the hyps so go ahead and apply other
		;; rules.
		(fgl-interp-value (interp-st->errmsg interp-st) nil nil)))

	     ;; See comment about successp above. We want to stop rewriting and
	     ;; return the real result if there was either no error (including
	     ;; abort-rewrite), and we want to stop rewriting and return
	     ;; whatever bogus result came from the RHS if there was a
	     ;; non-abort-rewrite error.
	     ((mv interp-st state)
	      ;; Note: determines success by checking interp-st->errmsg, so
	      ;; don't move below the cancel-error below.
	      (fgl-trace-finish-rewrite val rule fn tracep interp-st state))
	     (err (interp-st->errmsg interp-st))
	     (successp (not (eq err :abort-rewrite)))
	     (val (and (not err) val))
	     (interp-st (interp-st-cancel-error :abort-rewrite interp-st))
	     (interp-st (interp-st-prof-pop-increment (not err) interp-st))
	     (new-bindings (interp-st-bindings interp-st))
	     (interp-st (interp-st-pop-frame interp-st))
	     (interp-st (if (not err)
			    (interp-st-add-bindings rev-bindings interp-st)
			  interp-st)))
	  (fgl-interp-value successp val new-bindings)))

      (define fgl-rewrite-try-rewrite ((rule fgl-rule-p)
				       (fn pseudo-fnsym-p)
				       (interp-st interp-st-bfrs-ok)
				       state)
	:guard (and (fgl-rule-case rule :rewrite)
		    (< 0 (interp-st-scratch-len interp-st))
		    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-arglist))
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
	     (args (interp-st-top-scratch-fgl-arglist interp-st))
	     ;; (rule.lhs.args (pseudo-term-call->args rule.lhs))
	     ((mv unify-ok bindings rev-subst)
	      (fgl-unify-term/gobj-fn/args-masked
	       (pseudo-term-fncall->fn rule.lhs)
	       (pseudo-term-call->args rule.lhs)
	       fn args
	       nil nil (interp-st-bfrstate)))
	     ((unless unify-ok) (fgl-interp-value nil nil))
	     ((fgl-interp-value successp ans ?bindings)
	      (fgl-rewrite-apply-rule
	       (fgl-rule-fix rule) fn
	       bindings
	       rev-subst
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
		    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-arglist))
	:measure (list (nfix (interp-st->reclimit interp-st)) 10000 0 1)
	:returns (mv successp
		     (ans fgl-object-p)
		     new-interp-st new-state)
	(b* ((args (interp-st-top-scratch-fgl-arglist interp-st))
	     (rule (fgl-rule-fix rule))
	     (fn (pseudo-fnsym-fix fn))
	     ((fgl-interp-value successp rhs hyps rev-subst bindings)
	      (fgl-meta-fncall-stub (fgl-rule-meta->name rule) fn args interp-st state))
	     ((when (or** (not successp) (interp-st->errmsg interp-st)))
	      ;; See comments about successp in fgl-rewrite-apply-rule.
	      (fgl-interp-value (interp-st->errmsg interp-st) nil))

	     ((fgl-interp-value successp ans ?bindings)
	      (fgl-rewrite-apply-rule
	       (fgl-rule-fix rule) fn
	       bindings rev-subst hyps rhs
	       (interp-st->equiv-contexts interp-st)
	       interp-st state)))
	  (fgl-interp-value successp ans)))

      (define fgl-rewrite-relieve-hyps ((rule fgl-rule-p)
                                        (fn pseudo-fnsym-p)
                                        (hyps pseudo-term-listp)
                                        (tracep)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
	:measure (list (nfix (interp-st->reclimit interp-st)) 9000
		       (pseudo-term-list-binding-count hyps) 0)
	:returns (mv (failed-hyp acl2::maybe-natp :rule-classes :type-prescription)
		     new-interp-st new-state)
	(b* (((when (atom hyps))
	      (b* ((interp-st (interp-st-set-phase nil interp-st)))
		(fgl-interp-value nil)))
	     ((fgl-interp-recursive-call ok)
	      (fgl-rewrite-relieve-hyp (car hyps) interp-st state))
	     (hypnum (or (interp-st-phase interp-st) 0))
	     ((when (not ok))
	      (fgl-interp-value hypnum))
	     (interp-st (interp-st-incr-phase interp-st))
	     ((mv interp-st state)
	      (fgl-trace-relieve-hyp-output hypnum rule fn tracep interp-st state)))
	  (fgl-rewrite-relieve-hyps rule fn (cdr hyps) tracep interp-st state)))

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
	     ((mv successp give-up interp-st)
	      (fgl-rewrite-relieve-hyp-match-assums hyp interp-st))
	     ((when (or successp give-up))
	      (fgl-interp-value successp))
	     ((fgl-interp-value test-bfr)
	      (fgl-interp-test-under-pathcond hyp interp-st state)))
	  ;; Could check against the pathcond here...
	  (fgl-interp-value (eq test-bfr t))))

      (define fgl-rewrite-reverse-subst ((subst pseudo-term-subst-p)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       5000 (len subst) 0)
	:returns (mv (bindings fgl-object-bindings-p)
		     new-interp-st new-state)
	(b* (((when (atom subst))
	      (fgl-interp-value nil))
	     ((unless (mbt (and (consp (car subst))
				(pseudo-var-p (caar subst)))))
	      (fgl-rewrite-reverse-subst (cdr subst) interp-st state))
	     ((cons var term) (car subst))
	     (interp-st (interp-st-set-term term interp-st))
	     (interp-st (interp-st-set-term-index nil interp-st))
	     ((interp-st-bind
	       (equiv-contexts nil))
	      ((fgl-interp-recursive-call val)
	       (fgl-interp-term-top term interp-st state)))
	     (interp-st (interp-st-push-scratch-fgl-obj val interp-st))
	     ((fgl-interp-value rest)
	      (fgl-rewrite-reverse-subst (cdr subst) interp-st state))
	     ((mv val interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
	  (fgl-interp-value (cons (cons var val) rest))))

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
	       (fgl-interp-term-top timing-arg interp-st state)))
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
	       (fgl-interp-term-top test interp-st state)))
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
	       (fgl-interp-term-top test interp-st state)))
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
	;; The branch helpers keep intermediate BFRs and objects on scratch
	;; so they track any simplification of the logicman.
	(b* (((fgl-interp-recursive-call testbfr)
	      (fgl-interp-test test interp-st state)))
	  (fgl-interp-if-branches testbfr then else interp-st state)))

      ;; Interpret the branches in two phases so no induction case contains
      ;; more than two recursive interpreter calls.
      (define fgl-interp-if-branches ((testbfr interp-st-bfr-p)
				      (then pseudo-termp)
				      (else pseudo-termp)
				      (interp-st interp-st-bfrs-ok)
				      state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020
		       (+ (pseudo-term-binding-count then)
			  (pseudo-term-binding-count else))
		       120)
	:returns (mv (ans fgl-object-p) new-interp-st new-state)
	(b* ((interp-st (interp-st-push-scratch-bfr testbfr interp-st))
	     ((fgl-interp-recursive-call then-unreachable thenval)
	      (fgl-maybe-interp testbfr then interp-st state))
	     ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st)))
	  (fgl-interp-if-else testbfr thenval then-unreachable else interp-st state)))

      ;; Shared by IF and OR: interpret ELSE and merge with the saved THEN value.
      (define fgl-interp-if-else ((testbfr interp-st-bfr-p)
				  (thenval fgl-object-p)
				  (then-unreachable)
				  (else pseudo-termp)
				  (interp-st interp-st-bfrs-ok)
				  state)
	:guard (fgl-object-bfrs-ok thenval (interp-st-bfrstate))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (pseudo-term-binding-count else) 110)
	:returns (mv (ans fgl-object-p) new-interp-st new-state)
	(b* ((interp-st (interp-st-push-scratch-bfr testbfr interp-st))
	     (interp-st (interp-st-push-scratch-fgl-obj thenval interp-st))
	     ((fgl-interp-recursive-call else-unreachable elseval)
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
	       (fgl-interp-term-top test interp-st state)))
	     (interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count test) interp-st)))
	  (fgl-interp-or-else (fgl-interp-or-test-already-rewrittenp equiv-contexts)
			      (is-fncall 'left-to-right test) testval else interp-st state)))

      (define fgl-interp-or-else ((already-rewrittenp)
				  (left-to-rightp)
				  (testval fgl-object-p)
				  (else pseudo-termp)
				  (interp-st interp-st-bfrs-ok)
				  state)
	:guard (fgl-object-bfrs-ok testval (interp-st-bfrstate))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (pseudo-term-binding-count else) 120)
	:returns (mv (ans fgl-object-p) new-interp-st new-state)
	(b* ((interp-st (interp-st-push-scratch-fgl-obj testval interp-st))
	     ((fgl-interp-recursive-call testbfr)
	      (fgl-interp-simplify-if-test already-rewrittenp left-to-rightp testval interp-st state))
	     ((mv testval interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
	  (fgl-interp-if-else testbfr testval nil else interp-st state)))

      (define fgl-interp-handle-error ((handled-error pseudo-termp)
				       (x pseudo-termp)
				       (on-error pseudo-termp)
				       (interp-st interp-st-bfrs-ok)
				       state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020
		       (+ (pseudo-term-binding-count handled-error)
			  (pseudo-term-binding-count x)
			  (pseudo-term-binding-count on-error))
		       90)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* (((when (interp-st->errmsg interp-st))
	      (fgl-interp-value nil))
	     ((unless (member-eq 'unequiv (interp-st->equiv-contexts interp-st)))
	      (fgl-interp-error :msg (fgl-msg "Handle-error called not in an unequiv context: args ~x0."
					      (list (pseudo-term-fix handled-error) (pseudo-term-fix x)
						    (pseudo-term-fix on-error)))))
	     ((fgl-interp-recursive-call handled-error-obj)
	      (fgl-interp-term-top handled-error interp-st state))
	     ((unless (fgl-object-case handled-error-obj :g-concrete))
	      (fgl-interp-error :msg (fgl-msg "Handle-error: first argument must rewrite to a concrete value"
					      (list (pseudo-term-fix handled-error) (pseudo-term-fix x)
						    (pseudo-term-fix on-error))))))
	  (fgl-interp-handle-error-body handled-error-obj x on-error interp-st state)))

      (define fgl-interp-handle-error-body ((handled-error-obj fgl-object-p)
					    (x pseudo-termp)
					    (on-error pseudo-termp)
					    (interp-st interp-st-bfrs-ok)
					    state)
	:guard (fgl-object-case handled-error-obj :g-concrete)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (+ (pseudo-term-binding-count x)
			       (pseudo-term-binding-count on-error)) 90)
	:returns (mv (ans fgl-object-p) new-interp-st new-state)
	(b* (((when (interp-st->errmsg interp-st))
	      (fgl-interp-value nil))
	     ((fgl-interp-recursive-call x-obj)
	      (fgl-interp-term-top x interp-st state))
	     ((unless (and (interp-st->errmsg interp-st)
			   (equal (interp-st->errmsg interp-st) (g-concrete->val handled-error-obj))))
	      (fgl-interp-value x-obj))
	     (interp-st (update-interp-st->errmsg nil interp-st)))
	  (fgl-interp-term-top on-error interp-st state)))

      (define fgl-interp-assume ((test pseudo-termp)
                                 (x pseudo-termp)
                                 (on-unreach pseudo-termp)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020
		       (+ (pseudo-term-binding-count test)
			  (pseudo-term-binding-count x)
			  (pseudo-term-binding-count on-unreach))
		       90)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* (((unless (member-eq 'unequiv (interp-st->equiv-contexts interp-st)))
	      (fgl-interp-error :msg (fgl-msg "Assume called not in an unequiv context: args ~x0."
					      (list (pseudo-term-fix test) (pseudo-term-fix x))))))
	  (fgl-interp-conditionalize test x on-unreach interp-st state)))

      (define fgl-interp-conditionalize ((test pseudo-termp)
                                         (x pseudo-termp)
                                         (on-unreach pseudo-termp)
                                         (interp-st interp-st-bfrs-ok)
                                         state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020
		       (+ (pseudo-term-binding-count test)
			  (max (pseudo-term-binding-count x)
			       (pseudo-term-binding-count on-unreach)))
		       85)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* (((fgl-interp-recursive-call testbfr)
	      (fgl-interp-test test interp-st state)))
	  (fgl-interp-conditionalize-branch testbfr x on-unreach interp-st state)))

      (define fgl-interp-conditionalize-branch ((testbfr interp-st-bfr-p)
                                                (x pseudo-termp)
                                                (on-unreach pseudo-termp)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020 (max (pseudo-term-binding-count x)
				 (pseudo-term-binding-count on-unreach)) 110)
	:returns (mv (ans fgl-object-p) new-interp-st new-state)
	(b* (((fgl-interp-recursive-call unreachp ans)
	      (fgl-maybe-interp testbfr x interp-st state))
	     ((when unreachp)
	      (b* (((interp-st-bind
		     (equiv-contexts (cons 'unequiv (interp-st->equiv-contexts interp-st))))
		    ((fgl-interp-value ans)
		     (fgl-interp-term-top on-unreach interp-st state))))
		(fgl-interp-value ans))))
	  (fgl-interp-value ans)))

      (define fgl-interp-conditionalize-bind ((freevar pseudo-termp)
					      (test pseudo-termp)
					      (x pseudo-termp)
					      (on-unreach pseudo-termp)
					      (interp-st interp-st-bfrs-ok)
					      state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2020
		       (+ (pseudo-term-binding-count test)
			  (max (pseudo-term-binding-count x)
			       (pseudo-term-binding-count on-unreach)))
		       87)
	:returns (mv
		  (successp)
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* (((unless (and (pseudo-term-case freevar :var)
			   (not (assoc-eq (pseudo-term-var->name freevar)
					  (interp-st-minor-bindings interp-st)))
			   (not (assoc-eq (pseudo-term-var->name freevar)
					  (interp-st-bindings interp-st)))))
	      ;; don't treat as special
	      (fgl-interp-value nil nil))
	     (varname (pseudo-term-var->name freevar))
	     ((fgl-interp-value ans)
	      (fgl-interp-conditionalize test x on-unreach interp-st state))
	     ((when (assoc-eq varname (interp-st-bindings interp-st)))
	      (b* ((interp-st (fgl-interp-store-debug-info
			       (fgl-msg "Conditionalize error: free ~
                                                  variable ~x0 was bound ~
                                                  during evaluation of the ~
                                                  form~%" freevar)
			       nil interp-st)))
		(fgl-interp-value t nil)))
	     (interp-st (interp-st-add-binding varname ans interp-st)))
	  (fgl-interp-value t ans)))

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
	      (fgl-interp-term-top equiv interp-st state))
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
	      (fgl-interp-term-top x interp-st state))
	     ((unless (fgl-object-case xobj :g-concrete))
	      (fgl-interp-error :msg (fgl-msg "First argument to fgl-interp-obj ~
                                             yielded a non-constant object: ~
                                             args ~x0."
					      (list (pseudo-term-fix x)))))
	     (term (g-concrete->val xobj))
	     ((unless (easy-termp term (w state)))
	      (fgl-interp-error :msg (fgl-msg "First argument to fgl-interp-obj ~
                                             yielded a value that did not ~
                                             satisfy termp -- input:~%~x0~%value:~%~x1."
					      (list (pseudo-term-fix x))
					      term)))
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
	(b* (((when (interp-st->errmsg interp-st))
	      ;; We cancel an error below, so we need to ensure it's not one that originated outside of this call.
	      (fgl-interp-value nil nil))
	     (unconditionalp (pseudo-term-case x
			       :fncall (eq x.fn 'unconditional)
			       :otherwise nil))
	     ((when unconditionalp)
	      (b* (((fgl-interp-value ans)
		    (fgl-interp-term-top x interp-st state))
		   ((when (eq (interp-st->errmsg interp-st) :unreachable))
		    (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
		      (fgl-interp-value t nil))))
		(fgl-interp-value nil ans)))
	     ((mv contra interp-st)
	      (interp-st-pathcond-assume test interp-st))
	     ((when contra)
	      (b* ((interp-st (interp-st-incr-term-index (fgl-minor-frame-subterm-count x) interp-st)))
		(fgl-interp-value t nil)))
	     ((fgl-interp-value ans)
	      (fgl-interp-term-top x interp-st state))
	     (interp-st (interp-st-pathcond-rewind interp-st))
	     ((when (eq (interp-st->errmsg interp-st) :unreachable))
	      (b* ((interp-st (update-interp-st->errmsg nil interp-st))
		   ((mv status interp-st state)
		    ;; Check whether we're still in an unreachable state without the new assumption.
		    (interp-st-sat-check
		     (fgl-reachability-sat-check-config-wrapper
		      (fgl-config->sat-config-reachability (interp-st->config interp-st)))
		     t interp-st state))
		   ((when (eq status :unsat))
		    ;; unreachable outside the new assumption as well
		    (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
		      (fgl-interp-value nil nil))))
		(fgl-interp-value t nil))))
	  (fgl-interp-value nil ans)))

      (define fgl-interp-maybe-simplify-if-test ((test interp-st-bfr-p)
                                                 (xobj fgl-object-p)
                                                 (interp-st interp-st-bfrs-ok)
                                                 state)
	:guard (fgl-object-bfrs-ok xobj (interp-st-bfrstate))
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
		   (fgl-interp-simplify-if-test nil nil xobj interp-st state))))
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
		 (fgl-interp-simplify-if-test nil nil xobj interp-st state)))
	       (interp-st (interp-st-pathcond-rewind interp-st))
	       ((when (eq (interp-st->errmsg interp-st) :unreachable))
		(b* ((interp-st (update-interp-st->errmsg nil interp-st)))
		  (fgl-interp-value t nil))))
	    (fgl-interp-value nil ans))))

      (define fgl-interp-simplify-if-test1 ((already-rewrittenp)
					    (left-to-rightp)
					    (xobj fgl-object-p)
					    (interp-st interp-st-bfrs-ok)
					    state)
	:guard (fgl-object-bfrs-ok xobj (interp-st-bfrstate))
	:returns (mv
		  xbfr
		  new-interp-st new-state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1500
		       (fgl-object-count xobj)
		       38)
	(fgl-object-case xobj
	  :g-concrete (fgl-interp-value (bool-fix xobj.val))
	  :g-boolean (fgl-interp-value xobj.bool)
	  :g-integer (fgl-interp-value t)
	  :g-cons (fgl-interp-value t)
	  :g-var (b* (((mv ans interp-st) (interp-st-add-term-bvar-unique xobj interp-st state)))
		   (fgl-interp-value ans))
	  :g-ite (fgl-interp-simplify-if-test-ite xobj interp-st state)
	  :g-apply (fgl-interp-simplify-if-test-fncall already-rewrittenp left-to-rightp xobj interp-st state)
	  :g-map (fgl-interp-value (bool-fix xobj.alist))))

      (define fgl-interp-simplify-if-test ((already-rewrittenp)
					   (left-to-rightp)
					   (xobj fgl-object-p)
					   (interp-st interp-st-bfrs-ok)
					   state)
	:guard (fgl-object-bfrs-ok xobj (interp-st-bfrstate))
	:returns (mv
		  xbfr
		  new-interp-st new-state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1500
		       (fgl-object-count xobj)
		       40)
	(b* (((mv ans1 interp-st state) (fgl-interp-simplify-if-test1 already-rewrittenp left-to-rightp xobj interp-st state))
	     ((mv ans interp-st) (interp-st-pathcond-fix-bfr ans1 interp-st)))
	  (mv ans interp-st state)))

      ;; BOZO should we have a version of this for OR?
      (define fgl-interp-simplify-if-test-ite ((xobj fgl-object-p)
					       (interp-st interp-st-bfrs-ok)
					       state)
	:guard (and (fgl-object-case xobj :g-ite)
		    (fgl-object-bfrs-ok xobj (interp-st-bfrstate)))
	:returns (mv
		  xbfr
		  new-interp-st new-state)
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1500
		       (fgl-object-count xobj)
		       30)
	(b* (((unless (mbt (fgl-object-case xobj :g-ite)))
	      (fgl-interp-error :msg (fgl-msg "Impossible case")))
	     ((g-ite xobj))
	     (interp-st (interp-st-push-scratch-fgl-obj xobj.else interp-st))
	     (interp-st (interp-st-push-scratch-fgl-obj xobj.then interp-st))
	     ;; scratch: xobj.then, xobj.else
	     ((fgl-interp-recursive-call test-bfr)
	      (fgl-interp-simplify-if-test t nil xobj.test interp-st state))
	     ((mv thenval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
	     ((mv elseval interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
	  (fgl-interp-simplify-if-test-branches test-bfr thenval elseval interp-st state)))

      ;; The test has been simplified; only the two branch calls remain.
      (define fgl-interp-simplify-if-test-branches ((test-bfr interp-st-bfr-p)
						    (thenval fgl-object-p)
						    (elseval fgl-object-p)
						    (interp-st interp-st-bfrs-ok)
						    state)
	:guard (and (fgl-object-bfrs-ok thenval (interp-st-bfrstate))
		    (fgl-object-bfrs-ok elseval (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1490 0 0)
	:returns (mv xbfr new-interp-st new-state)
	(b* ((interp-st (interp-st-push-scratch-fgl-obj elseval interp-st))
	     (interp-st (interp-st-push-scratch-bfr test-bfr interp-st))
	     ;; scratch: test-bfr, elseval
	     ((fgl-interp-recursive-call then-unreachable then-bfr)
	      (fgl-interp-maybe-simplify-if-test test-bfr thenval interp-st state))
	     (test-bfr (interp-st-top-scratch-bfr interp-st))
	     (elseval (interp-st-nth-scratch-fgl-obj 1 interp-st))
	     (interp-st (interp-st-update-scratch-bfr 1 then-bfr interp-st))
	     (neg-test (stobj-let ((logicman (interp-st->logicman interp-st)))
				  (not)
				  (bfr-not test-bfr)
				  not))
	     ;; scratch: test-bfr, then-bfr
	     ((fgl-interp-value else-unreachable else-bfr)
	      (fgl-interp-maybe-simplify-if-test neg-test elseval interp-st state))

	     ((mv test-bfr interp-st) (interp-st-pop-scratch-bfr interp-st))
	     ((mv then-bfr interp-st) (interp-st-pop-scratch-bfr interp-st)))
	  (fgl-interp-finish-simplify-if-test-ite
	   test-bfr then-bfr else-bfr then-unreachable else-unreachable interp-st state)))

      (define fgl-interp-simplify-if-test-fncall ((already-rewrittenp)
						  (left-to-rightp)
						  (xobj fgl-object-p)
						  (interp-st interp-st-bfrs-ok)
						  state)
	:guard (and (fgl-object-case xobj :g-apply)
		    (fgl-object-bfrs-ok xobj (interp-st-bfrstate)))

	:measure (list (nfix (interp-st->reclimit interp-st))
		       1500
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
		    (fgl-interp-simplify-if-test nil nil neg-arg interp-st state)))
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
	     (interp-st (interp-st-push-scratch-fnsym xobj.fn interp-st))
	     ((interp-st-bind
	       (reclimit (1- reclimit) reclimit)
	       (equiv-contexts '(iff)))
	      ((fgl-interp-recursive-call successp ans)
	       (fgl-rewrite-fncall xobj.fn (fgl-objectlist->arglist xobj.args)
				   (or** already-rewrittenp
					 fn-mode.dont-rewrite-under-if-test
					 (interp-flags->hide (interp-st->flags interp-st)))
				   interp-st state)))
	     (interp-st (interp-st-pop-scratch interp-st))
	     ((mv xobj interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
	     ;; ((when err)
	     ;;  (mv nil interp-st state))
	     ((when successp)
	      (b* (((interp-st-bind
		     (reclimit (1- reclimit) reclimit))
		    ((fgl-interp-value ans)
		     (fgl-interp-simplify-if-test nil left-to-rightp ans interp-st state))))
		(fgl-interp-value ans)))

	     (xobj (hons-copy xobj))
	     (look (interp-st-get-term->bvar xobj interp-st))

	     ((when look)
	      (b* ((bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
				   (bfr)
				   (bfr-var look)
				   bfr)))
		(fgl-interp-value bfr)))

	     ((mv bfr interp-st)
	      (interp-st-add-term-bvar left-to-rightp xobj interp-st state))

	     ((when (interp-st->errmsg interp-st))
	      (fgl-interp-value nil))

	     (interp-st (interp-st-push-scratch-bfr bfr interp-st))

	     ((fgl-interp-value)
	      (fgl-interp-add-constraints xobj interp-st state))

	     ((mv bfr interp-st) (interp-st-pop-scratch-bfr interp-st)))
	  (fgl-interp-value bfr)))

      (define fgl-interp-add-constraints ((xobj fgl-object-p)
					  (interp-st interp-st-bfrs-ok)
					  state)
	:guard (and ;; (fgl-object-case xobj :g-apply)
		(fgl-object-bfrs-ok xobj (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1400
		       (fgl-object-count xobj)
		       15)
	:returns (mv new-interp-st new-state)
	(b* ((constraint-db (interp-st->constraint-db interp-st))
	     ((mv constraint-substs constraint-db)
	      (gbc-process-new-lit xobj constraint-db (interp-st-bfrstate) state))
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

	     ;; (flags (interp-st->flags interp-st))
	     ;; (new-flags  (!interp-flags->intro-synvars
	     ;;              t
	     ;;              ;; (!interp-flags->intro-bvars
	     ;;              ;;  nil
	     ;;               (!interp-flags->simplify-logic nil flags)))
	     ((interp-st-bind
	       ;; (flags new-flags flags)
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
	:guard (constraint-instancelist-bfrs-ok substs (interp-st-bfrstate))
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
	     (interp-st (interp-st-push-non-rule-frame sub1.subst interp-st))
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
	:guard (and (fgl-object-bfrs-ok thenval (interp-st-bfrstate))
		    (fgl-object-bfrs-ok elseval (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       2000 0 0)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* ((thenval (fgl-object-fix thenval))
	     (elseval (fgl-object-fix elseval))
	     ((when (eq testbfr t)) (fgl-interp-value thenval))
	     ((when (eq testbfr nil)) (fgl-interp-value elseval))
	     ((when (hons-equal thenval elseval)) (fgl-interp-value thenval))
	     (flags (interp-st->flags interp-st))
	     (new-flags  (!interp-flags->if-merge-last-chance nil flags))
	     ((interp-st-bind
	       (flags new-flags flags))
	      ((fgl-interp-value ans)
	       (fgl-interp-merge-branches-rewrite testbfr thenval elseval interp-st state))))
	  (fgl-interp-value ans)))

      (define fgl-interp-merge-branches-rewrite ((testbfr interp-st-bfr-p)
                                                 (thenval fgl-object-p)
                                                 (elseval fgl-object-p)
                                                 (interp-st interp-st-bfrs-ok)
                                                 state)
	:guard (and (fgl-object-bfrs-ok thenval (interp-st-bfrstate))
		    (fgl-object-bfrs-ok elseval (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       (if (interp-flags->if-merge-last-chance (interp-st->flags interp-st))
			   1700
			 1900)
		       0 20)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* ((reclimit (interp-st->reclimit interp-st))
	     ((when (fgl-interp-check-reclimit interp-st))
	      (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.")))
	     ;; Need to bind this here before calling fgl-rewrite-try-merge-rules
	     ;; unless we're going to prove that call doesn't change the flag
	     ;; value.
	     (last-chancep (interp-flags->if-merge-last-chance (interp-st->flags interp-st)))

	     (thenval (fgl-object-fix thenval))
	     (elseval (fgl-object-fix elseval))
	     (thenfns (fgl-fncall-object->fns thenval))
	     (elsefns (fgl-fncall-object->fns elseval))

	     ((mv then-rules else-rules if-rules interp-st)
	      (interp-st-if-rules thenfns elsefns interp-st state))

	     (interp-st (interp-st-push-scratch-fnsym 'fgl-interp-merge-branches-rewrite interp-st))
	     (interp-st (interp-st-push-scratch-fgl-obj elseval interp-st))
	     (interp-st (interp-st-push-scratch-fgl-obj thenval interp-st))
	     (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
	     (interp-st (interp-st-push-scratch-fgl-arglist
			 (fgl-objectlist->arglist
			  (list (mk-g-boolean testbfr) thenval elseval))
			 interp-st))
	     ((interp-st-bind
	       (reclimit (1- reclimit) reclimit))
	      ((fgl-interp-value successp ans)
	       (fgl-rewrite-try-merge-rules then-rules else-rules if-rules 'if interp-st state)))
	     (interp-st (if (and (not successp) last-chancep)
			    (fgl-interp-store-debug-info
			     "If-then-else failed to merge -- see debug obj"
			     (list :test testbfr
				   :then (fgl-object-fix thenval)
				   :else (fgl-object-fix elseval))
			     interp-st)
			  interp-st))
	     (interp-st (interp-st-pop-scratch interp-st))
	     ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
	     ((mv thenval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
	     ((mv elseval interp-st) (interp-st-pop-scratch-fgl-obj interp-st))
	     (interp-st (interp-st-pop-scratch interp-st))
	     ;; ((when err)
	     ;;  (mv nil interp-st state))
	     ((when (or successp last-chancep))
	      (fgl-interp-value ans)))
	  (fgl-interp-merge-branch-subterms
	   testbfr thenval elseval interp-st state)))

      (define fgl-rewrite-try-merge-rules ((rules1 fgl-rulelist-p)
				           (rules2 fgl-rulelist-p)
				           (rules3 fgl-rulelist-p)
				           (fn pseudo-fnsym-p)
				           (interp-st interp-st-bfrs-ok)
				           state)
	:guard (and (< 0 (interp-st-scratch-len interp-st))
		    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-arglist))
	:measure (list (nfix (interp-st->reclimit interp-st)) 20000 0 0)
	:returns (mv successp
		     (ans fgl-object-p)
		     new-interp-st new-state)
	(b* (((fgl-interp-recursive-call successp ans)
	      (fgl-rewrite-try-rules rules1 fn interp-st state))
	     ((when successp) (fgl-interp-value successp ans)))
	  (fgl-rewrite-try-remaining-merge-rules rules2 rules3 fn interp-st state)))

      (define fgl-rewrite-try-remaining-merge-rules ((rules1 fgl-rulelist-p)
				                     (rules2 fgl-rulelist-p)
				                     (fn pseudo-fnsym-p)
				                     (interp-st interp-st-bfrs-ok)
				                     state)
	:guard (and (< 0 (interp-st-scratch-len interp-st))
		    (scratchobj-case (interp-st-top-scratch interp-st) :fgl-arglist))
	:measure (list (nfix (interp-st->reclimit interp-st)) 19000 0 0)
	:returns (mv successp
		     (ans fgl-object-p)
		     new-interp-st new-state)
	(b* (((fgl-interp-recursive-call successp ans)
	      (fgl-rewrite-try-rules rules1 fn interp-st state))
	     ((when successp) (fgl-interp-value successp ans)))
	  (fgl-rewrite-try-rules rules2 fn interp-st state)))

      (define fgl-interp-merge-branch-subterms ((testbfr interp-st-bfr-p)
                                                (thenval fgl-object-p)
                                                (elseval fgl-object-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
	:guard (and (fgl-object-bfrs-ok thenval (interp-st-bfrstate))
		    (fgl-object-bfrs-ok elseval (interp-st-bfrstate)))
	:measure (list (nfix (interp-st->reclimit interp-st))
		       1800 0 0)
	:returns (mv
		  (ans fgl-object-p)
		  new-interp-st new-state)
	(b* (((mv thenfn thenargs) (fgl-object-recognize-merge-fncall thenval))
	     ((mv elsefn elseargs) (fgl-object-recognize-merge-fncall elseval))
	     ((unless (and** thenfn
			     (eq thenfn elsefn)
			     (eql (len thenargs) (len elseargs))
			     (not (fgl-function-mode->dont-if-merge-args
				   (fgl-function-mode-lookup
				    thenfn (fgl-config->function-modes (interp-st->config interp-st)))))))
	      (b* (((mv okp obj interp-st)
		    (interp-st-object-basic-merge testbfr thenval elseval
						  (interp-flags->make-ites (interp-st->flags interp-st))))
		   ((when okp) (fgl-interp-value obj))
		   (flags (interp-st->flags interp-st))
		   (new-flags  (!interp-flags->if-merge-last-chance t flags))
		   ((interp-st-bind
		     (flags new-flags flags))
		    ((fgl-interp-value ans)
		     (fgl-interp-merge-branches-rewrite testbfr thenval elseval interp-st state))))
		(fgl-interp-value ans)))
	     ;; BOZO sad:
	     (reclimit (interp-st->reclimit interp-st))
	     ((when (fgl-interp-check-reclimit interp-st))
	      (fgl-interp-error :msg (fgl-msg "The recursion limit ran out.")))

	     (interp-st (interp-st-push-scratch-fnsym 'fgl-interp-merge-branch-subterms interp-st))
	     (interp-st (interp-st-push-scratch-fnsym thenfn interp-st))
	     (interp-st (interp-st-push-scratch-fgl-objlist thenargs interp-st))
	     (interp-st (interp-st-push-scratch-fgl-objlist elseargs interp-st))
	     ((interp-st-bind
	       (reclimit (1- reclimit) reclimit)
	       (equiv-contexts (fgl-interp-lambda-arglist-equiv-contexts (interp-st->equiv-contexts interp-st))))
	      ((fgl-interp-recursive-call args)
	       (fgl-interp-merge-branch-args testbfr thenargs elseargs interp-st state)))
	     (interp-st (interp-st-pop-scratch interp-st))
	     (interp-st (interp-st-pop-scratch interp-st))
	     (interp-st (interp-st-pop-scratch interp-st))
	     (interp-st (interp-st-pop-scratch interp-st)))
	  (fgl-interp-fncall thenfn (fgl-objectlist->arglist args)
			     interp-st state)))

      (define fgl-interp-merge-branch-args ((testbfr interp-st-bfr-p)
					    (thenargs fgl-objectlist-p)
					    (elseargs fgl-objectlist-p)
					    (interp-st interp-st-bfrs-ok)
					    state)
	:guard (and (eql (len thenargs) (len elseargs))
		    (fgl-objectlist-bfrs-ok thenargs (interp-st-bfrstate))
		    (fgl-objectlist-bfrs-ok elseargs (interp-st-bfrstate)))
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
	     (interp-st (interp-st-push-scratch-fnsym 'fgl-interp-merge-branch-args interp-st))
	     (interp-st (interp-st-push-scratch-fgl-objlist (cdr thenargs) interp-st))
	     (interp-st (interp-st-push-scratch-fgl-objlist (cdr elseargs) interp-st))
	     (interp-st (interp-st-push-scratch-bfr testbfr interp-st))
	     ((fgl-interp-recursive-call ans)
	      (fgl-interp-merge-branches testbfr (car thenargs) (car elseargs) interp-st state))
	     ((mv testbfr interp-st) (interp-st-pop-scratch-bfr interp-st))
	     ((mv rest-elseargs interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))
	     ((mv rest-thenargs interp-st) (interp-st-pop-scratch-fgl-objlist interp-st))
	     (interp-st (interp-st-pop-scratch interp-st))

	     ((unless (mbt (eql (len (cdr thenargs)) (len rest-thenargs))))
	      (fgl-interp-value nil))
	     ;; ((when err)
	     ;;  (mv nil interp-st state))
	     (interp-st (interp-st-push-scratch-fgl-obj ans interp-st))
	     ((fgl-interp-value args)
	      (fgl-interp-merge-branch-args testbfr rest-thenargs rest-elseargs interp-st state))
	     ((mv arg1 interp-st) (interp-st-pop-scratch-fgl-obj interp-st)))
	  (fgl-interp-value (cons arg1 args)))))))


(local (in-theory (enable find-flag-is-hyp)))


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


(with-output :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (defsection-progn fgl-interp-arglist-return-shapes

    ;; Share the flag induction and expansion of the interpreter bodies.
    (std::defret-mutual fgl-interp-arglist-return-shapes
      (defret len-of-fgl-interp-arglist
	(equal (len arg-objs) (len args))
	:fn fgl-interp-arglist)
      (defret len-of-fgl-interp-lambda-arglist
	(equal (len arg-objs) (len args))
	:fn fgl-interp-lambda-arglist)
      (defret true-listp-of-fgl-interp-arglist
	(true-listp arg-objs)
	:fn fgl-interp-arglist
	:rule-classes :type-prescription)
      (defret true-listp-of-fgl-interp-lambda-arglist
	(true-listp arg-objs)
	:fn fgl-interp-lambda-arglist
	:rule-classes :type-prescription)
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp
      :skip-others t)))


(defsection-progn fgl-interp-scratch-update-support

  (defthm stack$a-pop-scratch-of-stack$a-update-0
    (equal (stack$a-pop-scratch (stack$a-update-scratch 0 obj stack))
	   (stack$a-pop-scratch stack))
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch stack$a-update-scratch))))

  (defthm stack$a-top-scratch-of-stack$a-update-0
    (equal (stack$a-top-scratch (stack$a-update-scratch 0 obj stack))
	   (scratchobj-fix obj))
    :hints(("Goal" :in-theory (enable stack$a-top-scratch stack$a-update-scratch))))

  (local (in-theory (e/d (len-update-nth-when-less
                          stack$a-nth-scratch-of-stack$a-update-scratch)
                         (BFR-LISTP$-WHEN-SUBSETP-EQUAL
                          acl2::subsetp-append1
                          acl2::subsetp-of-cons
                          acl2::subsetp-trans2)))))




(local (in-theory (enable bfr-p-of-equal
                          fgl-unify-term/gobj-fn/args-masked-bfrs-ok)))




(local (in-theory (enable stack$a-top-scratch-of-set-term-index
                          stack$a-top-scratch-of-set-term)))


(defsection-progn fgl-interp-preserves-bfrs-ok
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
	    (:fnname fgl-rewrite-try-merge-rules)
	    (:fnname fgl-rewrite-try-remaining-merge-rules))
	(:add-hyp (scratchobj-case (stack$a-top-scratch (double-rewrite (interp-st->stack interp-st)))
		    :fgl-arglist))))
      :formal-hyps    ;; generates hypotheses
      (((interp-st-bfr-p x)           (lbfr-p x logicman))
       ((fgl-arglist-p x)             (lbfr-listp (fgl-arglist-bfrlist x) logicman))
       ((fgl-object-p x)              (lbfr-listp (fgl-object-bfrlist x) logicman))
       ((fgl-objectlist-p x)          (lbfr-listp (fgl-objectlist-bfrlist x) logicman))
       ((fgl-object-bindings-p x)     (lbfr-listp (fgl-object-bindings-bfrlist x) logicman))
       (interp-st                     (interp-st-bfrs-ok interp-st))
       ((constraint-instancelist-p x) (lbfr-listp (constraint-instancelist-bfrlist x) logicman)))
      :return-concls  ;; generates conclusions
      ((xbfr                          (lbfr-p xbfr new-logicman))
       ((fgl-object-p x)              (lbfr-listp (fgl-object-bfrlist x) new-logicman))
       ((fgl-arglist-p x)             (lbfr-listp (fgl-arglist-bfrlist x) new-logicman))
       ((fgl-objectlist-p x)          (lbfr-listp (fgl-objectlist-bfrlist x) new-logicman))
       ((fgl-object-bindings-p x)     (lbfr-listp (fgl-object-bindings-bfrlist x) new-logicman))
       (new-interp-st                 (interp-st-bfrs-ok new-interp-st)))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
	      `(:do-not-induct t)
	      (let ((flag (find-flag-is-hyp clause)))
		(and flag
		     (prog2$ (cw "flag: ~x0~%" flag)
			     '(:no-op t))))
	      (and stable-under-simplificationp
		   '(:in-theory (enable interp-st-get-term->bvar))))
      :mutual-recursion fgl-interp)))


(local (in-theory (disable nth update-nth)))


(defsection-progn fgl-interp-pathcond-logicman-extension-support

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
		    (logicman->mode (interp-st->logicman old))))))


(defsection-progn fgl-interp-preserves-state-fields
  ;; These properties need the same interpreter expansion.  Prove them in one
  ;; induction while exporting the individual theorems with their usual names.
  (encapsulate nil
    (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))
    (with-output
      :off (event)
      :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
      (std::defret-mutual-generate
	(std::defret-generate <fn>-preserves-logicman->mode
	  :rules ((t (:add-concl (equal (logicman->mode (interp-st->logicman new-interp-st))
					(logicman->mode (interp-st->logicman interp-st)))))))
	(std::defret-generate <fn>-preserves-reclimit
	  :rules ((t (:add-concl (acl2::nat-equiv
				  (interp-st->reclimit new-interp-st)
				  (interp-st->reclimit interp-st))))))
	(std::defret-generate <fn>-preserves-reclimit-natp
	  :rules ((t (:add-concl (implies (natp (interp-st->reclimit interp-st))
					  (natp (interp-st->reclimit new-interp-st)))))))
	(std::defret-generate <fn>-preserves-w-state
	  :rules ((t (:add-concl (equal (w new-state) (w state))))))
	(std::defret-generate <fn>-equiv-contexts-preserved
	  :rules ((t (:add-concl (equal (interp-st->equiv-contexts new-interp-st)
					(interp-st->equiv-contexts interp-st))))))
	(std::defret-generate <fn>-preserves-errmsg
	  :rules ((t (:add-concl (let ((errmsg (interp-st->errmsg interp-st)))
				   (implies errmsg
					    (equal (interp-st->errmsg new-interp-st) errmsg)))))))
	:hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
	:mutual-recursion fgl-interp))))


(local (in-theory (e/d (not-member-of-append)
                       (not
                        acl2::member-equal-append
                        acl2::member-of-append
                        bfr-listp$-of-append))))


(defret return-values-correct-of-interp-st-add-term-bvar-unique
  (equal (list . <values>)
         <call>)
  :hints(("Goal" :in-theory (enable interp-st-add-term-bvar-unique)))
  :fn interp-st-add-term-bvar-unique)


(defsection-progn fgl-interp-return-values-correct
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




(local (in-theory (enable len-cinstlist-when-scratchobj-isomorphic-rw
                          len-fgl-objlist-when-scratchobj-isomorphic-rw)))




(local (in-theory (enable intersectp-equal-of-set-diff
                          alist-keys-of-fgl-object-bindings-concretize
                          fgl-bindings-extension-p-of-append)))


(defsection stack-bindings-extension-p


  (defthmd fgl-bindings-extension-p-of-concretize
    (implies (fgl-bindings-extension-p x y)
	     (fgl-bindings-extension-p (fgl-object-bindings-concretize x env)
				       (fgl-object-bindings-concretize y env)))
    :hints(("Goal" :in-theory (enable fgl-bindings-extension-p
				      fgl-object-bindings-concretize))))


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

    (defthm stack-bindings-extension-p-of-stack$a-set-bindings
      (implies (fgl-bindings-extension-p bindings (stack$a-bindings stack))
	       (stack-bindings-extension-p (stack$a-set-bindings bindings stack) stack))
      :hints(("Goal" :in-theory (enable stack$a-set-bindings
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

    (defcong stack-bindings-equiv equal (stack-bindings-extension-p x y) 1
      :hints(("Goal" :in-theory (enable stack-bindings-equiv))))
    (defcong stack-bindings-equiv equal (stack-bindings-extension-p x y) 2
      :hints(("Goal" :in-theory (enable stack-bindings-equiv))))

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
      :hints(("Goal" :in-theory (enable stack-bindings-extension-p-transitive))))

    (defthm stack-bindings-extension-p-of-stack-add-bindings
      (implies (and (no-duplicatesp-equal (alist-keys (fgl-object-bindings-fix bindings)))
		    (not (intersectp-equal (alist-keys (fgl-object-bindings-fix bindings))
					   (alist-keys (stack$a-bindings stack1))))
		    (stack-bindings-extension-p stack1 stack2))
	       (stack-bindings-extension-p (stack-add-bindings bindings stack1) stack2))
      :hints(("Goal" :in-theory (enable stack-add-bindings
					stack$a-set-bindings
					stack$a-bindings))))

    (defthm stack-bindings-extension-p-of-stack-add-bindings-concretize
      (implies (and (no-duplicatesp-equal (alist-keys (fgl-object-bindings-fix bindings)))
		    (not (intersectp-equal (alist-keys (fgl-object-bindings-fix bindings))
					   (alist-keys (stack$a-bindings stack1))))
		    (stack-bindings-extension-p (fgl-major-stack-concretize stack1 env logicman) stack2))
	       (stack-bindings-extension-p (fgl-major-stack-concretize (stack-add-bindings bindings stack1) env logicman) stack2))
      :hints(("Goal" :in-theory (enable stack-add-bindings
					stack$a-set-bindings
					stack$a-bindings
					fgl-major-stack-concretize
					fgl-major-frame-concretize)))))

  (local (defthm alist-keys-when-stack-binding-domains-equal
	   (implies (equal (stack-binding-domains x) (stack-binding-domains y))
		    (equal (alist-keys (stack$a-bindings x))
			   (alist-keys (stack$a-bindings y))))
	   :rule-classes nil
	   :hints (("Goal" :use ((:instance bindings-of-stack-binding-domains)
				 (:instance bindings-of-stack-binding-domains (x y))
				 (:instance alist-keys-of-fgl-bindings-domain (x (stack$a-bindings x)))
				 (:instance alist-keys-of-fgl-bindings-domain (x (stack$a-bindings y))))
		    :in-theory (disable bindings-of-stack-binding-domains alist-keys-of-fgl-bindings-domain)))))

  (def-updater-independence-thm alist-keys-stack-bindings-when-binding-domains-equal
    (implies (equal (stack-binding-domains (interp-st->stack new))
		    (stack-binding-domains (interp-st->stack old)))
	     (equal (alist-keys (stack$a-bindings (interp-st->stack new)))
		    (alist-keys (stack$a-bindings (interp-st->stack old)))))
    :hints (("Goal" :use ((:instance alist-keys-when-stack-binding-domains-equal
			   (x (interp-st->stack new)) (y (interp-st->stack old)))))))

  (def-updater-independence-thm alist-keys-popped-stack-bindings-when-binding-domains-preserved
    (implies (stack-equiv-except-top-major/minor-bindings
	      (stack-binding-domains (interp-st->stack new))
	      (stack-binding-domains (interp-st->stack old)))
	     (equal (alist-keys (stack$a-bindings (stack$a-pop-frame (interp-st->stack new))))
		    (alist-keys (stack$a-bindings (stack$a-pop-frame (interp-st->stack old))))))
    :hints (("Goal" :use ((:instance alist-keys-when-stack-binding-domains-equal
			   (x (stack$a-pop-frame (interp-st->stack new)))
			   (y (stack$a-pop-frame (interp-st->stack old))))))))

  (defthm fgl-arglist-unbounds-top-scratch-structural-rw
    (implies (and (major-stack-scratch-isomorphic old (double-rewrite new))
		  (syntaxp (not (equal new old)))
		  (double-rewrite (scratchobj-case (stack$a-top-scratch old) :fgl-arglist)))
	     (equal (fgl-arglist-unbounds
		     (scratchobj-fgl-arglist->val (stack$a-top-scratch new)))
		    (fgl-arglist-unbounds
		     (scratchobj-fgl-arglist->val (stack$a-top-scratch old)))))
    :hints (("Goal" :use ((:instance fgl-arglist-unbounds-when-scratchobj-isomorphic
			   (x (stack$a-top-scratch new))
			   (y (stack$a-top-scratch old))))
	     :in-theory (disable fgl-arglist-unbounds-when-scratchobj-isomorphic))))

  (defthm alist-keys-top-scratch-bindings-structural-rw
    (implies (and (major-stack-scratch-isomorphic old (double-rewrite new))
		  (syntaxp (not (equal new old)))
		  (double-rewrite (scratchobj-case (stack$a-top-scratch old) :fgl-bindings)))
	     (equal (alist-keys (scratchobj-fgl-bindings->val (stack$a-top-scratch new)))
		    (alist-keys (scratchobj-fgl-bindings->val (stack$a-top-scratch old)))))
    :hints (("Goal" :use ((:instance alist-keys-fgl-bindings-when-scratchobj-isomorphic
			   (x (stack$a-top-scratch new))
			   (y (stack$a-top-scratch old))))
	     :in-theory (disable alist-keys-fgl-bindings-when-scratchobj-isomorphic))))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual fgl-rewrite-reverse-subst-preserves-keys
      (defret fgl-rewrite-reverse-subst-preserves-keys
	(equal (alist-keys bindings)
	       (alist-keys (pseudo-term-subst-fix subst)))
	:hints ('(:expand (<call>
			   (pseudo-term-subst-fix subst))))
	:fn fgl-rewrite-reverse-subst)
      :skip-others t
      :mutual-recursion fgl-interp))

  (local
   (defret fgl-rewrite-apply-rule-prep-alist-keys-of-rev-subst
     (implies (not (or* failed-hyp (interp-st->errmsg new-interp-st)))
	      (equal (alist-keys rev-bindings)
		     (alist-keys (pseudo-term-subst-fix rev-subst))))
     :hints (("Goal" :expand (<call>) :in-theory (enable or*) :do-not-induct t))
     :fn fgl-rewrite-apply-rule-prep))

  (defret fgl-rewrite-apply-rule-core-alist-keys-of-rev-subst
    (implies (not (or* failed-hyp
		       (interp-st->errmsg new-interp-st)))
	     (equal (alist-keys rev-bindings)
		    (alist-keys (pseudo-term-subst-fix rev-subst))))
    :hints (("goal" :expand (<call>)
	     :in-theory (enable or*)))
    :fn fgl-rewrite-apply-rule-core))
