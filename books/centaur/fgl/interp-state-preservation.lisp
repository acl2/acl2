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

; Preservation of interpreter path conditions, constraints, and BVAR state.
; Include interp.lisp for the complete interpreter correctness result.
;
; Retain the original interpreter's CMUCL exclusion: its stack-binding
; extension proofs exhausted the CMUCL dynamic heap (September 2023).
; cert-param: non-cmucl

(in-package "FGL")

(include-book "interp-defs")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/meta/resolve-flag-cp" :dir :system))
(local (include-book "centaur/meta/urewrite" :dir :system))
(local (include-book "centaur/meta/let-abs" :dir :system))
(local (include-book "centaur/meta/flatten-clause" :dir :system))
(local (include-book "std/util/defret-mutual-generate" :dir :system))

;; Preserve the client's existing theory; enable the shared private facts below
;; at the points where they are used.
(local (deftheory before-interp-proof-support (current-theory :here)))
(local (include-book "interp-proof-support"))
(local (in-theory (theory 'before-interp-proof-support)))
(std::make-returnspec-config :hints-sub-returnnames t)


(local (std::add-default-post-define-hook :fix))
(local (in-theory
        (e/d (fgl-interp-proof-enabled-rules)
             (fgl-interp-proof-disabled-rules))))

(defthm pathcond-enabledp-of-interp-st-pathcond-rewind
  (iff (nth *pathcond-enabledp* (pathcond-rewind mode pathcond))
       (nth *pathcond-enabledp* pathcond))
  :hints(("Goal" :in-theory (e/d (pathcond-rewind) (nth-add1 nth update-nth)))))


(defsection-progn fgl-interp-preserves-pathcond-enabledp
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


(defret pathcond-rewind-stack-len-of-interp-st-pathcond-assume-maybe
  (implies (and (equal mode (interp-st-bfr-mode interp-st))
                (not contra))
	   (equal (pathcond-rewind-stack-len mode (interp-st->pathcond new-interp-st))
		  (maybe-incr (nth *pathcond-enabledp* (interp-st->pathcond interp-st))
			      (pathcond-rewind-stack-len mode (interp-st->pathcond interp-st)))))
  :hints(("Goal" :in-theory (enable interp-st-pathcond-assume)))
  :fn interp-st-pathcond-assume)


(defsection-progn fgl-interp-preserves-pathcond-stack-length
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


(defsection-progn fgl-interp-preserves-pathcond-rewind-ok
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


(defret pathcond-rewind-ok-of-interp-st-pathcond-assume
  (implies (and (not contra)
		(equal bfr-mode (logicman->mode (interp-st->logicman interp-st))))
	   (pathcond-rewind-ok bfr-mode (interp-st->pathcond new-interp-st)))
  :hints(("Goal" :in-theory (enable interp-st-pathcond-assume pathcond-rewind-ok
				    maybe-incr)))
  :fn interp-st-pathcond-assume)


(local (acl2::use-trivial-ancestors-check))


(defsection-progn fgl-interp-preserves-pathcond-checkpoints
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-preserves-pathcond
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
		    ((fgl-object-p x)              (fgl-object-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-objectlist-p x)          (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-arglist-p x)             (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-object-bindings-p x)     (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
		    (interp-st                     (interp-st-bfrs-ok interp-st))
		    ((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate))))
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
		   (:fnname fgl-rewrite-try-merge-rules)
		   (:fnname fgl-rewrite-try-remaining-merge-rules))
	       (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist))))
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
    (b* (((mv ?successp ?rhs ?hyps ?rev-subst ?bindings ?new-interp-st ?new-state)
	  (fgl-meta-fncall-stub metafn fn args interp-st state)))
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
		    ((fgl-object-p x)               (fgl-object-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-objectlist-p x)           (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-arglist-p x)              (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-object-bindings-p x)      (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
		    (interp-st                     (interp-st-bfrs-ok interp-st))
		    ((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate))))
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
		   (:fnname fgl-rewrite-try-merge-rules)
		   (:fnname fgl-rewrite-try-remaining-merge-rules))
	       (:add-hyp (scratchobj-case (stack$a-top-scratch (double-rewrite (interp-st->stack interp-st))) :fgl-arglist))))
      :hints (("goal" :do-not-induct t))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))


(def-updater-independence-thm logicman-pathcond-eval-of-interp-st-logicman-extension
  (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
		(logicman-pathcond-p pathcond (interp-st->logicman old)))
	   (equal (logicman-pathcond-eval env pathcond (interp-st->logicman new))
		  (logicman-pathcond-eval env pathcond (interp-st->logicman old)))))


(defsection constraint-eval-tightens

  (local (defret logicman-pathcond-eval-of-assume-tightens
	   (implies (not (logicman-pathcond-eval env pathcond logicman))
		    (not (logicman-pathcond-eval env new-pathcond logicman)))
	   :hints (("goal" :cases (contradictionp))
		   (and stable-under-simplificationp
			'(:cases ((pathcond-enabledp pathcond)))))
	   :fn logicman-pathcond-assume))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-constraint-eval-tightens
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
		    ((fgl-object-p x)               (fgl-object-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-objectlist-p x)           (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-arglist-p x)              (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-object-bindings-p x)      (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
		    (interp-st                     (interp-st-bfrs-ok interp-st))
		    ((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate))))
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
		   (:fnname fgl-rewrite-try-merge-rules)
		   (:fnname fgl-rewrite-try-remaining-merge-rules))
	       (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist))))
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
		    ((fgl-object-p x)               (fgl-object-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-objectlist-p x)           (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-arglist-p x)              (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-object-bindings-p x)      (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
		    (interp-st                     (interp-st-bfrs-ok interp-st))
		    ((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate))))
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
		   (:fnname fgl-rewrite-try-merge-rules)
		   (:fnname fgl-rewrite-try-remaining-merge-rules))
	       (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st))) :fgl-arglist))))
      :hints (("goal" :do-not-induct t :expand ((:free (x) (hide x)))
	       :in-theory (enable iff* and*)))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))


(defsection fgl-interp-term-guards
  (local (in-theory (e/d (stack$a-update-scratch-in-terms-of-push-pop)
                         (w))))

  (local (defthm bfr-varname-p-of-get-term->bvar$c
	   (b* ((bvar-db (interp-st->bvar-db interp-st))
		(logicman (interp-st->logicman interp-st))
		(bvar (get-term->bvar$c obj bvar-db)))
	     (implies (and (interp-st-bfrs-ok interp-st)
			   bvar)
		      (bfr-varname-p bvar logicman)))
	   :hints(("Goal" :in-theory (enable interp-st-bfrs-ok bfr-varname-p)))))

  ;; ugh
  (local (defthm booleanp-of-interp-st-pathcond-enabledp
	   (implies (interp-stp interp-st)
		    (booleanp (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))
	   :hints(("Goal" :in-theory (enable interp-stp pathcondp interp-st->pathcond)))
	   :rule-classes :type-prescription))

  (local (defthm symbolp-by-pseudo-term-kind
	   (implies (and (equal (pseudo-term-kind x) :var)
			 (pseudo-termp x))
		    (symbolp x))
	   :hints(("Goal" :in-theory (enable pseudo-term-kind pseudo-termp)))))

  (local (in-theory (enable interp-st-get-term->bvar)))
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (verify-guards fgl-interp-term
      :guard-debug t)))


(defsection bvar-db-ok-of-fgl-interp
  (local (Defthm gobj-bfr-eval-of-bfr-var
	   (implies (bfr-varname-p n)
		    (equal (gobj-bfr-eval (bfr-var n logicman) env logicman)
			   (bfr-lookup n (fgl-env->bfr-vals env))))
	   :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

  (defthm interp-st-sat-check-doesnt-fix-bvar-db
    (implies (and (interp-st-bfrs-ok interp-st)
		  (not (interp-st-bvar-db-ok interp-st env)))
	     (not (interp-st-bvar-db-ok
		   (mv-nth 1 (interp-st-sat-check params bfr interp-st state))
		   env)))
    :hints(("Goal" :expand ((interp-st-bvar-db-ok interp-st env))
	    :use ((:instance interp-st-bvar-db-ok-necc
		   (n (interp-st-bvar-db-ok-witness interp-st env))
		   (interp-st (mv-nth 1 (interp-st-sat-check params bfr interp-st state)))))
	    :in-theory (disable interp-st-bvar-db-ok-necc))))

  (local (in-theory (disable not
			     logicman-extension-of-update-2
			     logicman-extension-of-update-1
			     logicman-extension-p-transitive)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-bvar-db-ok-doesnt-get-fixed-somehow

      ;; Reject this rule on the old BVAR-DB condition before attempting the
      ;; more expensive BFR well-formedness hypotheses.
      :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
		    ((fgl-object-p x)               (fgl-object-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-objectlist-p x)           (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-arglist-p x)              (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
		    ((fgl-object-bindings-p x)      (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
		    (interp-st                     (interp-st-bfrs-ok interp-st))
		    ((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate))))

      :rules ((t (:add-concl (not (interp-st-bvar-db-ok new-interp-st env)))
		 (:add-keyword :hints ('(:do-not-induct t)
				       (let ((flag (find-flag-is-hyp clause)))
					 (and flag
					      (prog2$ (cw "flag: ~x0~%" flag)
						      '(:no-op t)))))))
	      ((or (:fnname fgl-rewrite-try-rules)
		   (:fnname fgl-rewrite-try-rule)
		   (:fnname fgl-rewrite-try-rewrite)
		   (:fnname fgl-rewrite-try-meta)
		   (:fnname fgl-rewrite-try-merge-rules)
		   (:fnname fgl-rewrite-try-remaining-merge-rules))
	       (:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist)))
	      ;; ADD-HYP prepends hypotheses, so put this rule last.
	      (t (:add-hyp (not (interp-st-bvar-db-ok interp-st env)))))

      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp)))


;; This book exports its main interpreter results and the supporting lemmas below.
;; Support lemmas are nonlocal so other interpreter proof books can reuse them
;; without duplicating proofs. They stay disabled for clients until explicitly
;; enabled through this named theory; ordinary inclusion uses the main results.
(deftheory interp-state-preservation-support-rules
  '(pathcond-rewind-ok-of-interp-st-pathcond-assume
    logicman-pathcond-eval-of-interp-st-logicman-extension))
(in-theory
 (disable interp-state-preservation-support-rules))
