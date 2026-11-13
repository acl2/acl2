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

; Interpreter correctness: incremental obligations and exported theorems.
;
; interp-defs supplies definitions and common invariants. The independent
; interp-state-preservation, interp-bindings, and interp-eval books supply
; the three groups of supporting facts used by the final proof below.
;
; Retain the original interpreter's CMUCL exclusion: its stack-binding
; extension proofs exhausted the CMUCL dynamic heap (September 2023).
; cert-param: non-cmucl

(in-package "FGL")

(include-book "interp-state-preservation")
(include-book "interp-bindings")
(include-book "interp-eval")
(local (include-book "tools/some-events" :dir :system))
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

;; Infrastructure and theory settings for the incremental final proof.


(acl2::set-case-split-limitations '(500 100000))


(defsection-progn fgl-interp-incremental-proof-infrastructure

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
      (defsection-unique-fn ',name ',args (w state)))))


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

;; Shared helpers are disabled by their owning books.  Activate the facts and
;; evaluator settings used by the final correctness proof in one place.
(local (std::add-default-post-define-hook :fix))
(local (acl2::use-trivial-ancestors-check))
(local (in-theory
        (e/d (fgl-ev-context-equiv-is-equal-of-fixes
              fgl-ev-context-equiv-forall-extensions-necc
              iff-forall-extensions-necc
              iff?-forall-extensions-necc
              fgl-ev-of-extension-when-equal-forall-extensions
              equal?-bindinglist-forall-extensions
              equal?-list-forall-extensions
              equal-list-forall-extensions-necc
              equal-bindinglist-forall-extensions-necc
              equal-subst-forall-extensions-necc
              fgl-interp-proof-enabled-rules
              interp-state-preservation-support-rules
              interp-bindings-support-rules
              interp-eval-support-rules
              subsetp-when-set-diff-subsetp
              alist-fix-of-append
              hons-assoc-equal-when-sub-alistp
              sub-alistp-of-cons-when-not-shadowing
              alist-keys-subsetp-when-sub-alistp
              set-difference-equal-under-iff
              intersectp-equal-of-set-diff-when-not-intersectp-first
              subsetp-set-difference-when-subsetp
              subsetp-set-difference-simple
              conjoin-of-atom)
             (fgl-interp-proof-disabled-rules
              iff-forall-extensions
              acl2::sub-alistp-hons-assoc-equal
              acl2::rewrite-rule-term
              fgl-ev-when-pseudo-term-lambda
              fgl-ev-when-pseudo-term-fncall
              fgl-interp-lambda-arglist-equiv-contexts))))


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

   (local (defthm fgl-ev-dumb-formula-to-clause-correct
	    (iff (fgl-ev (disjoin (cmr::dumb-formula-to-clause x)) a)
		 (fgl-ev x a))
	    :hints (("goal" :use ((:instance
				   (:functional-instance
				    cmr::dumb-formula-to-clause-correct
				    (cmr::flatten-ev fgl-ev)
				    (cmr::flatten-ev-list fgl-ev-list))
				   (x x) (a a)))
		     :in-theory (enable fgl-ev-of-fncall-args
					fgl-ev-of-bad-fncall
					fgl-ev-of-nonsymbol-atom)))))

   (define my-by-hint-cp ((clause pseudo-term-listp)
			  (hint)
			  state)
     :hooks nil
     (b* (((unless (symbolp hint))
	   (value (list clause)))
	  (thm (meta-extract-formula hint state))
	  ((unless (pseudo-termp thm))
	   (value (list clause)))
	  (thm-clause (cmr::dumb-formula-to-clause (acl2::beta-reduce-full thm)))
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
			     (:instance cmr::dumb-formula-to-clause-correct
			      (x (acl2::beta-reduce-full (meta-extract-formula hint state)))))
		:in-theory (disable ;; FGL-EV-META-EXTRACT-FORMULA
			    cmr::dumb-formula-to-clause-correct
			    fgl-ev-of-disjoin-beta-reduce-full-list)))
       :rule-classes :clause-processor))))


(with-output :off :all :on (error summary) :summary-off :all :summary-on (acl2::form acl2::time) :gag-mode t
  (local
   (defsection-progn fgl-interp-correctness-support

     ;; Keep local support scoped here, and reserve the nested unique section
     ;; for the correctness schema and its incremental proof obligations.

     (defsection-progn fgl-interp-conditionalize-correctness

       (local (defthm fgl-ev-equiv-of-conditionalize2
		(fgl-ev-equiv (pseudo-term-fncall 'conditionalize2 (list free test x x))
			      (pseudo-term-fncall 'conditionalize1 (list free test x)))
		:hints(("Goal" :in-theory (enable fgl-ev-equiv
						  conditionalize2 conditionalize1)))))

       (local (defthm fgl-ev-equiv-of-conditionalize1-args
		(implies (and (equal (pseudo-fnsym-fix fn) 'conditionalize1)
			      (eql (len args) 3))
			 (fgl-ev-equiv (pseudo-term-fncall 'conditionalize1 (list (car args) (cadr args) (caddr args)))
				       (pseudo-term-fncall fn args)))
		:hints(("Goal" :in-theory (enable fgl-ev-equiv)))))

       (local (defthm fgl-ev-equiv-of-conditionalize2-args
		(implies (and (equal (pseudo-fnsym-fix fn) 'conditionalize2)
			      (eql (len args) 4))
			 (fgl-ev-equiv (pseudo-term-fncall 'conditionalize2 (list (car args) (cadr args) (caddr args) (cadddr args)))
				       (pseudo-term-fncall fn args)))
		:hints(("Goal" :in-theory (enable fgl-ev-equiv)))))

       (local (defthm fgl-ev-context-equiv-forall-extensions-of-conditionalize2
		(implies (and (fgl-ev-context-equiv-forall-extensions contexts x (append minor major))
			      (equal
			       (fgl-ev-context-fix contexts ans)
			       (fgl-ev-context-fix contexts (fgl-ev x (append minor major))))
			      (pseudo-term-case freevar :var)
			      (not (hons-assoc-equal (pseudo-term-var->name freevar) minor))
			      (not (hons-assoc-equal (pseudo-term-var->name freevar) major)))
			 (fgl-ev-context-equiv-forall-extensions
			  contexts
			  (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
			  (append minor (cons (cons (pseudo-term-var->name freevar) ans) major))))
		:hints (("goal" :use ((:instance
				       fgl-ev-context-equiv-forall-extensions-necc
				       (term x)
				       (eval-alist (append minor major))
				       (ext (fgl-ev-context-equiv-forall-extensions-witness
					     contexts
					     (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
					     (append minor (cons (cons (pseudo-term-var->name freevar) ans) major)))))
				      (:instance
				       fgl-ev-context-equiv-forall-extensions-necc
				       (term x)
				       (eval-alist (append minor major))
				       (ext (append minor (cons (cons (pseudo-term-var->name freevar) ans) major)))))
			 :in-theory (enable conditionalize2
					    sub-alistp-by-witness)
			 :expand ((fgl-ev-context-equiv-forall-extensions
				   contexts
				   (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
				   (append minor (cons (cons (pseudo-term-var->name freevar) ans) major))))))))

       (local (defthm fgl-ev-context-equiv-forall-extensions-of-conditionalize2-when-false
		(implies (and (iff?-forall-extensions contexts test (append minor major))
			      (implies
			       (not (member-eq 'unequiv (equiv-contexts-fix contexts)))
			       (iff (fgl-ev test (append minor major)) nil))
			      (pseudo-term-case freevar :var)
			      (not (hons-assoc-equal (pseudo-term-var->name freevar) minor))
			      (not (hons-assoc-equal (pseudo-term-var->name freevar) major)))
			 (fgl-ev-context-equiv-forall-extensions
			  contexts
			  (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
			  (append minor (cons (cons (pseudo-term-var->name freevar) ans) major))))
		:hints (("goal" :use ((:instance
				       iff-forall-extensions-necc
				       (term test)
				       (eval-alist (append minor major))
				       (ext (fgl-ev-context-equiv-forall-extensions-witness
					     contexts
					     (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
					     (append minor (cons (cons (pseudo-term-var->name freevar) ans) major)))))
				      (:instance
				       iff-forall-extensions-necc
				       (term test)
				       (eval-alist (append minor major))
				       (ext (append minor (cons (cons (pseudo-term-var->name freevar) ans) major)))))
			 :in-theory (enable conditionalize2
					    iff?-forall-extensions
					    sub-alistp-by-witness)
			 :expand ((fgl-ev-context-equiv-forall-extensions
				   contexts
				   (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
				   (append minor (cons (cons (pseudo-term-var->name freevar) ans) major)))))))))

     (defsection-progn fgl-interp-unification-correctness-support

       (defthm fgl-arglist-eval-with-rev-subst-of-extension
	 (implies (and (eval-alist-extension-p subst1 subst2)
		       (subsetp-equal (fgl-arglist-unbounds args) (alist-keys subst2)))
		  (equal (fgl-arglist-eval-with-rev-subst
			  args subst1 env)
			 (fgl-arglist-eval-with-rev-subst
			  args subst2 env)))
	 :hints(("Goal" :in-theory (enable fgl-arglist-eval-with-rev-subst
					   fgl-arglist-unbounds subsetp-equal))))

       (defthm alist-keys-of-fgl-ev-alist
	 (equal (alist-keys (fgl-ev-alist x a))
		(alist-keys (pseudo-term-subst-fix x)))
	 :hints(("Goal" :in-theory (enable fgl-ev-alist alist-keys
					   pseudo-term-subst-fix))))

       (defret fgl-unify-term/gobj-fn/args-masked-correct-rephrase
	 (implies (and flag
		       (equal (pseudo-fnsym-fix x-fn) fn)
		       (pseudo-fnsym-p fn)
		       (equal bfrstate (logicman->bfrstate))
		       (eval-alist-extension-p extended-alist (fgl-object-bindings-eval new-alist env)))
		  (equal (fgl-ev (cons fn
				       (kwote-lst
					(fgl-arglist-eval-with-rev-subst
					 x-args
					 (fgl-ev-alist new-subst extended-alist)
					 env)))
				 nil)
			 (fgl-ev (pseudo-term-fncall pat-fn pat-args)
				 extended-alist)))
	 :hints (("goal" :use ((:instance fgl-unify-term/gobj-fn/args-masked-correct))
		  :in-theory (enable fgl-ev-of-pseudo-term-fncall)))
	 :fn fgl-unify-term/gobj-fn/args-masked)

       (defthm eval-alist-extension-p-of-append-new-keys-2
	 (implies (not (intersectp-equal (alist-keys x) (alist-keys y)))
		  (eval-alist-extension-p (append x y) x))
	 :hints(("Goal" :in-theory (e/d (;; acl2::sub-alistp
					 sub-alistp-by-witness
					 acl2::hons-assoc-equal-iff-member-alist-keys)
					(ACL2::ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL)))))

       (encapsulate nil
	 (acl2::def-updater-independence-thm fgl-arglist-eval-with-rev-subst-of-eval-alist-extension-stack
	   (b* ((rev-subst1 (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack new))
						      env (interp-st->logicman new)))
		(rev-subst (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack old))
						     env (interp-st->logicman old))))
	     (implies (and (subsetp-equal (fgl-arglist-unbounds args) (alist-keys rev-subst))
			   (eval-alist-extension-p rev-subst1 rev-subst))
		      (equal (fgl-arglist-eval-with-rev-subst args rev-subst1 env logicman)
			     (fgl-arglist-eval-with-rev-subst args rev-subst env logicman))))
	   :hints (("goal" :use ((:instance fgl-arglist-eval-with-rev-subst-of-extension
				  (subst1 (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack new))
								    env (interp-st->logicman new)))
				  (subst2 (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack old))
								    env (interp-st->logicman old)))))))))

       (encapsulate nil
	 (local (defthm lookup-when-fgl-bindings-extension-p-fix-double
		  (IMPLIES
		   (AND (fgl-object-bindings-equiv xx (double-rewrite x))
			(FGL-BINDINGS-EXTENSION-P Xx Y)
			(FGL-OBJECT-BINDINGS-P X)
			(HONS-ASSOC-EQUAL KEY (FGL-OBJECT-BINDINGS-FIX Y)))
		   (EQUAL (HONS-ASSOC-EQUAL KEY X)
			  (HONS-ASSOC-EQUAL KEY (FGL-OBJECT-BINDINGS-FIX Y))))
		  :hints (("goal" :in-theory (disable hons-assoc-equal-of-fgl-object-bindings-fix)
			   :use ((:instance lookup-when-fgl-bindings-extension-p
				  (x (fgl-object-bindings-fix x))))))))

	 (defthm eval-alist-extension-p-of-eval-when-stack-bindings-extension-p
	   (implies (stack-bindings-extension-p (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
						(fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old)))
		    (eval-alist-extension-p (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack new)) env (interp-st->logicman new))
					    (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack old)) env (interp-st->logicman old))))
	   :hints(("Goal" :in-theory (e/d (stack-bindings-extension-p
					   stack$a-bindings
					   fgl-major-stack-concretize
					   fgl-major-frame-concretize)
					  (eval-alist-extension-p-of-eval-when-fgl-bindings-extension-p))
		   :expand ((:free (x logicman) (fgl-major-stack-concretize (interp-st->stack x) env logicman)))
		   :use ((:instance eval-alist-extension-p-of-eval-when-fgl-bindings-extension-p
			  (x (fgl-object-bindings-concretize
			      (stack$a-bindings (interp-st->stack new))
			      env (interp-st->logicman new)))
			  (y (fgl-object-bindings-concretize
			      (stack$a-bindings (interp-st->stack old))
			      env (interp-st->logicman old)))
			  (env nil) (logicman nil))))))

	 (acl2::def-updater-independence-thm eval-alist-extension-p-of-eval-when-stack-bindings-extension-p-ext
	   (implies (and (stack-bindings-extension-p (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
						     (fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old)))
			 (eval-alist-extension-p (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack old)) env (interp-st->logicman old))
						 other))
		    (eval-alist-extension-p (fgl-object-bindings-eval (stack$a-bindings (interp-st->stack new)) env (interp-st->logicman new))
					    other))
	   :hints(("Goal" :in-theory (e/d (eval-alist-extension-p-transitive-2))))))

       (local (defun unhide (x) x))
       (local (defthm unhide-hide (equal (unhide (hide x)) x)
		:hints (("goal" :expand ((:free (x) (hide x)))))))
       (local (in-theory (Disable unhide)))

       (local (acl2::def-updater-independence-thm fgl-object-bindings-eval-of-stack-bindings-extension-p
		(implies (and (eval-alist-extension-p
			       (fgl-object-bindings-eval
				(stack$a-bindings (interp-st->stack new)) env (interp-st->logicman new))
			       (unhide (hide (fgl-object-bindings-eval
					      (stack$a-bindings (interp-st->stack old)) env (interp-st->logicman old)))))
			      (eval-alist-extension-p
			       (fgl-object-bindings-eval
				(stack$a-bindings (interp-st->stack old)) env (interp-st->logicman old))
			       other))
			 (eval-alist-extension-p
			  (fgl-object-bindings-eval
			   (stack$a-bindings (interp-st->stack new)) env (interp-st->logicman new))
			  other))
		:hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-1))))))

     (defsection-progn fgl-interp-pathcond-correctness-support

       (local (defret gobj-bfr-eval-of-interp-st-pathcond-fix
		(implies (and (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
						      (interp-st->logicman interp-st))
			      (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->constraint interp-st)
						      (interp-st->logicman interp-st))
			      (interp-st-bfr-p test)
			      (logicman-extension-p logicman (interp-st->logicman interp-st)))
			 (equal (gobj-bfr-eval ans env logicman)
				(gobj-bfr-eval test env (interp-st->logicman interp-st))))
		:hints(("Goal" :in-theory (enable gobj-bfr-eval)))
		:fn interp-st-pathcond-fix-bfr))

       (defretd interp-st-pathcond-assume-contradictionp-implies
	 (implies (and contra
		       (logicman-pathcond-eval
			(fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
			(interp-st->logicman interp-st))
		       (logicman-pathcond-eval
			(fgl-env->bfr-vals env)
			(interp-st->constraint interp-st)
			(interp-st->logicman interp-st)))
		  (not (gobj-bfr-eval test env (interp-st->logicman interp-st))))
	 :hints (("goal" :use ((:instance interp-st-pathcond-assume-not-contradictionp
				(env (fgl-env->bfr-vals env))))
		  :in-theory (e/d (gobj-bfr-eval))))
	 :fn interp-st-pathcond-assume)

       (defthmd interp-st-pathcond-assume-neg-contradictionp-implies
	 (b* (((mv contra ?interp-st2) (interp-st-pathcond-assume
					(bfr-not test (interp-st->logicman interp-st))
					interp-st1)))
	   (implies (and contra
			 ;; (interp-st-bfr-p bfr interp-st)
			 (equal (interp-st->logicman interp-st1)
				(interp-st->logicman interp-st))
			 (logicman-pathcond-eval
			  (fgl-env->bfr-vals env)
			  (interp-st->pathcond interp-st1)
			  (interp-st->logicman interp-st1))
			 (logicman-pathcond-eval
			  (fgl-env->bfr-vals env)
			  (interp-st->constraint interp-st1)
			  (interp-st->logicman interp-st1)))
		    (equal (gobj-bfr-eval test env (interp-st->logicman interp-st)) t)))
	 :hints (("goal" :use ((:instance interp-st-pathcond-assume-not-contradictionp
				(interp-st interp-st1)
				(test (bfr-not test (interp-st->logicman interp-st1)))
				(env (fgl-env->bfr-vals env))))
		  :in-theory (e/d (gobj-bfr-eval)
				  (interp-st-pathcond-assume-not-contradictionp)))))

       (defthm interp-st-pathcond-assume-both-contra
	 (b* ((not-bfr (bfr-not bfr (interp-st->logicman interp-st)))
	      ((mv contra1 interp-st1) (interp-st-pathcond-assume bfr interp-st))
	      ((mv contra2 ?interp-st2) (interp-st-pathcond-assume not-bfr interp-st1)))
	   (implies (and (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
			 contra1
			 (logicman-pathcond-eval env
						 (interp-st->pathcond interp-st)
						 (interp-st->logicman interp-st))
			 (logicman-pathcond-eval env (interp-st->constraint interp-st)
						 (interp-st->logicman interp-st)))
		    (not contra2)))
	 :hints(("Goal" :use ((:instance interp-st-pathcond-assume-not-contradictionp
			       (test bfr))
			      (:instance interp-st-pathcond-assume-not-contradictionp
			       (test (interp-st-bfr-not bfr))
			       (interp-st (mv-nth 1 (interp-st-pathcond-assume bfr interp-st)))))
		 :in-theory (disable interp-st-pathcond-assume-not-contradictionp))))

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
	 (b* (((mv ?successp ?rhs ?hyps ?rev-subst ?bindings ?new-interp-st ?new-state)
	       (fgl-meta-fncall-stub metafn origfn args interp-st state)))
	   (implies (and (not (equal (interp-st->errmsg interp-st) :unreachable))
			 (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
			 (logicman-pathcond-eval env (interp-st->pathcond interp-st)
						 (interp-st->logicman interp-st))
			 (logicman-pathcond-eval env (interp-st->constraint interp-st)
						 (interp-st->logicman interp-st))
			 (interp-st-bfrs-ok interp-st))
		    (not (equal (interp-st->errmsg new-interp-st)
				:unreachable))))))

     (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

     (defsection-progn fgl-interp-rule-list-correctness-support

       (local (defthm fgl-rule-term-of-car-theoremp-when-fgl-good-fgl-rules-p
		(implies (and (fgl-good-fgl-rules-p rules)
			      (consp rules))
			 (fgl-ev-theoremp (fgl-rule-term (car rules))))
		:hints(("Goal" :in-theory (enable fgl-good-fgl-rules-p
						  fgl-good-fgl-rule-p)))))

       (local (defthm fgl-good-fgl-rules-p-of-cdr
		(implies (fgl-good-fgl-rules-p x)
			 (fgl-good-fgl-rules-p (cdr x)))
		:hints(("Goal" :in-theory (enable fgl-good-fgl-rules-p))))))

     (defsection-progn fgl-interp-append-and-conditional-support

       (local (defthm bfr-listp-of-append-when-each
		(implies (And (bfr-listp a)
			      (bfr-listp b))
			 (bfr-listp (append a b)))))

       (local (in-theory (disable not-member-of-append)))

       (local (defthm if*-same
		(equal (if* test x x) x)
		:hints(("Goal" :in-theory (enable if*))))))

     (defsection-progn fgl-interp-object-concretization-adapters

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

       (local (defthm fgl-arglist-eval-with-rev-subst-of-concretize
		(equal (fgl-arglist-eval-with-rev-subst (fgl-arglist-concretize x env) rev-subst env2 logicman2)
		       (fgl-arglist-eval-with-rev-subst x rev-subst env))
		:hints(("Goal" :in-theory (enable fgl-arglist-eval-with-rev-subst
						  fgl-arglist-concretize)))))

       (local (defthm fgl-arglist-eval-with-rev-subst-rewrite-with-fgl-arglist-concretize
		(implies (and (equal ev (double-rewrite (fgl-arglist-concretize x env)))
			      (syntaxp (and (not (equal ev x))
					    (case-match ev
					      (('fgl-arglist-concretize-fn xans & &)
					       (not (equal xans x)))
					      (& t))))
			      (equal eval (fgl-arglist-eval-with-rev-subst ev rev-subst nil nil))
			      (syntaxp (case-match eval
					 (('fgl-arglist-eval-with-rev-subst-fn ('fgl-arglist-concretize-fn xans & &) & & &)
					  (not (equal xans x)))
					 (('fgl-arglist-eval-with-rev-subst-fn xans & & &)
					  (not (equal xans x)))
					 (& t))))
			 (equal (fgl-arglist-eval-with-rev-subst-fn x rev-subst env logicman) eval))))

       (local (defthm stack$a-top-scratch-of-fgl-major-stack-concretize
		(equal (stack$a-top-scratch (fgl-major-stack-concretize stack env))
		       (fgl-scratchobj-concretize (stack$a-top-scratch stack) env))
		:hints(("Goal" :in-theory (e/d (stack$a-top-scratch
						fgl-major-frame-concretize
						fgl-minor-frame-concretize)
					       (fgl-scratchlist-concretize-of-cdr))
			:expand ((fgl-major-stack-concretize stack env)
				 (fgl-minor-stack-concretize (major-frame->minor-stack (car stack)) env)
				 (:free (frame) (fgl-scratchlist-concretize (minor-frame->scratch frame) env))
				 (fgl-scratchobj-concretize '(:fgl-obj) env)
				 (fgl-object-concretize nil env))))))

       (local (defthm scratchobj-fgl-arglist->val-of-concretize
		(implies (scratchobj-case x :fgl-arglist)
			 (equal (scratchobj-fgl-arglist->val (fgl-scratchobj-concretize x env))
				(fgl-arglist-concretize (scratchobj-fgl-arglist->val x) env)))
		:hints(("Goal" :in-theory (enable fgl-scratchobj-concretize)))))

       (local (defthm scratchobj-bfr->val-of-concretize
		(implies (scratchobj-case x :bfr)
			 (equal (scratchobj-bfr->val (fgl-scratchobj-concretize x env))
				(gobj-bfr-eval (scratchobj-bfr->val x) env)))
		:hints(("Goal" :in-theory (e/d (fgl-scratchobj-concretize)))))))

     (defsection-progn fgl-interp-binding-domain-observations

       (local (in-theory (enable stack$a-bindings-of-fgl-major-stack-concretize
				 stack$a-minor-bindings-of-fgl-major-stack-concretize)))

       (local (defthm fgl-bindings-domain-under-iff
		(iff (fgl-bindings-domain x) (fgl-object-bindings-fix x))
		:hints (("Goal" :in-theory (enable fgl-bindings-domain fgl-object-bindings-fix)))))

       (local (def-updater-independence-thm minor-bindings-under-iff-when-binding-domains-preserved
		(implies (stack-equiv-except-top-bindings
			  (stack-binding-domains (interp-st->stack new))
			  (stack-binding-domains (interp-st->stack old)))
			 (iff (stack$a-minor-bindings (interp-st->stack new))
			      (stack$a-minor-bindings (interp-st->stack old))))
		:hints (("Goal" :use ((:instance minor-bindings-of-stack-binding-domains (x (interp-st->stack new)))
				      (:instance minor-bindings-of-stack-binding-domains (x (interp-st->stack old)))
				      (:instance fgl-bindings-domain-under-iff (x (stack$a-minor-bindings (interp-st->stack new))))
				      (:instance fgl-bindings-domain-under-iff (x (stack$a-minor-bindings (interp-st->stack old)))))
			 :in-theory (disable minor-bindings-of-stack-binding-domains fgl-bindings-domain-under-iff))))))

     (defsection-progn fgl-interp-stack-concretization-adapters

       (local (defthm fgl-objectlist-concretize-of-scratchobj-rewrite-with-fgl-major-stack-concretize
		(implies (and (scratchobj-case (stack$a-top-scratch stack) :fgl-objlist)
			      (stack-equiv-except-top-bindings
			       conc (double-rewrite (fgl-major-stack-concretize stack env logicman)))
			      (syntaxp (case-match conc
					 (('fgl-major-stack-concretize-fn stack1 & logicman1)
					  (not (and (equal stack1 stack) (equal logicman1 logicman))))
					 (& t))))
			 (equal (fgl-objectlist-concretize
				 (scratchobj-fgl-objlist->val
				  (stack$a-top-scratch stack))
				 env logicman)
				(scratchobj-fgl-objlist->val
				 (stack$a-top-scratch conc))))
		:hints(("Goal" :in-theory (e/d (stack$a-top-scratch
						fgl-major-frame-concretize
						fgl-minor-frame-concretize
						stack-equiv-except-top-bindings
						minor-stack-equiv-except-top-debug
						fgl-scratchobj-concretize)
					       (FGL-SCRATCHLIST-CONCRETIZE-OF-CDR))
			:expand ((fgl-major-stack-concretize stack env logicman)
				 (fgl-minor-stack-concretize (major-frame->minor-stack (car stack)) env logicman)
				 (:free (frame)
				  (fgl-scratchlist-concretize
				   (minor-frame->scratch frame) env logicman)))))))

       (local (defthm fgl-object-bindings-concretize-of-scratchobj-rewrite-with-fgl-major-stack-concretize
		(implies (and (scratchobj-case (stack$a-top-scratch stack) :fgl-bindings)
			      (stack-equiv-except-top-bindings
			       conc (double-rewrite (fgl-major-stack-concretize stack env logicman)))
			      (syntaxp (case-match conc
					 (('fgl-major-stack-concretize-fn stack1 & logicman1)
					  (not (and (equal stack1 stack) (equal logicman1 logicman))))
					 (& t))))
			 (equal (fgl-object-bindings-concretize
				 (scratchobj-fgl-bindings->val
				  (stack$a-top-scratch stack))
				 env logicman)
				(scratchobj-fgl-bindings->val
				 (stack$a-top-scratch conc))))
		:hints(("Goal" :in-theory (e/d (stack$a-top-scratch
						fgl-major-frame-concretize
						fgl-minor-frame-concretize
						stack-equiv-except-top-bindings
						minor-stack-equiv-except-top-debug
						fgl-scratchobj-concretize)
					       (FGL-SCRATCHLIST-CONCRETIZE-OF-CDR))
			:expand ((fgl-major-stack-concretize stack env logicman)
				 (fgl-minor-stack-concretize (major-frame->minor-stack (car stack)) env logicman)
				 (:free (frame)
				  (fgl-scratchlist-concretize
				   (minor-frame->scratch frame) env logicman)))))))

       (local (defthm fgl-arglist->objects-of-concretize
		(implies (not (fgl-arglist-unbounds x))
			 (equal (fgl-arglist->objects (fgl-arglist-concretize x env))
				(fgl-objectlist-concretize (fgl-arglist->objects x) env)))
		:hints(("Goal" :in-theory (enable fgl-arglist-concretize
						  fgl-objectlist-concretize
						  fgl-arglist-unbounds
						  fgl-arglist->objects)))))

       (local (defthm fgl-object-concretize-of-scratchobj-rewrite-with-fgl-major-stack-concretize
		(implies (and (scratchobj-case (stack$a-top-scratch stack) :fgl-obj)
			      (stack-equiv-except-top-bindings
			       conc (double-rewrite (fgl-major-stack-concretize stack env logicman)))
			      (syntaxp (case-match conc
					 (('fgl-major-stack-concretize-fn stack1 & logicman1)
					  (not (and (equal stack1 stack) (equal logicman1 logicman))))
					 (& t))))
			 (equal (fgl-object-concretize
				 (scratchobj-fgl-obj->val
				  (stack$a-top-scratch stack))
				 env logicman)
				(scratchobj-fgl-obj->val
				 (stack$a-top-scratch conc))))
		:hints(("Goal" :in-theory (e/d (stack$a-top-scratch
						fgl-major-frame-concretize
						fgl-minor-frame-concretize
						stack-equiv-except-top-bindings
						minor-stack-equiv-except-top-debug
						fgl-scratchobj-concretize)
					       (FGL-SCRATCHLIST-CONCRETIZE-OF-CDR))
			:expand ((fgl-major-stack-concretize stack env logicman)
				 (fgl-minor-stack-concretize (major-frame->minor-stack (car stack)) env logicman)
				 (fgl-object-concretize nil env)
				 (:free (frame)
				  (fgl-scratchlist-concretize
				   (minor-frame->scratch frame) env logicman)))))))

       (local (defthm gobj-bfr-eval-of-scratchobj-bfr->val-rewrite-with-concretize
		(implies (and (scratchobj-case scr :bfr)
			      (equal conc (fgl-scratchobj-concretize scr env))
			      (syntaxp (case-match conc
					 (('fgl-scratchobj-concretize-fn sc . &)
					  (not (equal sc scr)))
					 (& t))))
			 (equal (gobj-bfr-eval (scratchobj-bfr->val scr) env)
				(gobj-bfr-eval (scratchobj-bfr->val conc) nil nil)))))

       (local (in-theory (disable (fgl-scratchobj-concretize))))

       (local (acl2::def-updater-independence-thm fgl-object-bindings-concretize-major-rewrite-with-stack-concretize
		(implies (equal (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
				(fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old)))
			 (equal (fgl-object-bindings-concretize (stack$a-bindings (interp-st->stack new)) env (interp-st->logicman new))
				(fgl-object-bindings-concretize (stack$a-bindings (interp-st->stack old)) env (interp-st->logicman old))))
		:hints (("goal" :use ((:instance stack$a-bindings-of-fgl-major-stack-concretize
				       (stack (interp-st->stack new))
				       (logicman (interp-st->logicman new)))
				      (:instance stack$a-bindings-of-fgl-major-stack-concretize
				       (stack (interp-st->stack old))
				       (logicman (interp-st->logicman old))))
			 :in-theory (disable stack$a-bindings-of-fgl-major-stack-concretize)))))

       (local (acl2::def-updater-independence-thm fgl-object-bindings-concretize-minor-rewrite-with-stack-concretize
		(implies (stack-equiv-except-top-bindings
			  (fgl-major-stack-concretize (interp-st->stack new) env (interp-st->logicman new))
			  (fgl-major-stack-concretize (interp-st->stack old) env (interp-st->logicman old)))
			 (equal (fgl-object-bindings-concretize (stack$a-minor-bindings (interp-st->stack new)) env (interp-st->logicman new))
				(fgl-object-bindings-concretize (stack$a-minor-bindings (interp-st->stack old)) env (interp-st->logicman old))))
		:hints (("goal" :use ((:instance stack$a-minor-bindings-of-fgl-major-stack-concretize
				       (stack (interp-st->stack new))
				       (logicman (interp-st->logicman new)))
				      (:instance stack$a-minor-bindings-of-fgl-major-stack-concretize
				       (stack (interp-st->stack old))
				       (logicman (interp-st->logicman old))))
			 :in-theory (disable stack$a-minor-bindings-of-fgl-major-stack-concretize)))))

       (defthm stack$a-minor-bindings-of-stack$a-pop-scratch
	 (equal (stack$a-minor-bindings (stack$a-pop-scratch x))
		(stack$a-minor-bindings x))
	 :hints(("Goal" :in-theory (enable stack$a-minor-bindings
					   stack$a-pop-scratch))))

       (local (defthm scratchobj-kind-top-rewrite-with-stack-isomorphic
		(implies (and (major-stack-scratch-isomorphic stack2 (double-rewrite stack))
			      (syntaxp (not (equal stack2 stack))))
			 (equal (scratchobj-kind (stack$a-top-scratch stack))
				(scratchobj-kind (stack$a-top-scratch stack2))))
		:hints(("Goal" :in-theory (enable stack$a-top-scratch
						  major-stack-scratch-isomorphic)))))

       (local (defthm fgl-object-bindings-eval-rewrite-with-fgl-object-bindings-concretize
		(implies (and (equal ev (double-rewrite (fgl-object-bindings-concretize x env)))
			      (syntaxp ;; (prog2$ (fmt-to-comment-window
			       ;;          "ev: ~x0~%" `((#\0 . ,ev))
			       ;;          0 '(nil 5 8 nil) nil)
			       (and (not (equal ev x))
				    (case-match ev
				      (('fgl-object-bindings-concretize-fn xans & &)
				       (not (equal xans x)))
				      (& t))))
			      (equal eval (fgl-object-bindings-eval ev nil nil))
			      (syntaxp ;; (prog2$ (fmt-to-comment-window
			       ;;          "eval: ~x0~%" `((#\0 . ,ev))
			       ;;          0 '(nil 5 8 nil) nil)
			       (case-match eval
				 (('fgl-object-bindings-eval-fn ('fgl-object-bindings-concretize-fn xans & &) & &)
				  (not (equal xans x)))
				 (('fgl-object-bindings-eval-fn xans & &)
				  (not (equal xans x)))
				 (& t))))
			 (equal (fgl-object-bindings-eval x env) eval)))))

     (defsection-progn fgl-interp-object-evaluation-normalization

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

       (local (defthm len-cdr-equal-when-len-equal
		(implies (equal (len x) (len y))
			 (equal (equal (len (cdr x)) (len (cdr y))) t))
		:hints(("Goal" :in-theory (enable len)))))

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
		:hints(("Goal" :in-theory (enable fgl-object-bindings-eval))))))

     (local (in-theory (disable stack$a-open-nth-scratch)))

     (defsection-progn fgl-interp-arglist-scratch-concretization-adapters

       (local (defthm stack$a-open-nth-scratch2
		(implies (and (syntaxp (quotep n))
			      (< (nfix n) (double-rewrite (stack$a-scratch-len stack))))
			 (equal (stack$a-nth-scratch n stack)
				(if (zp n)
				    (stack$a-top-scratch stack)
				  (stack$a-nth-scratch (1- n)
						       (stack$a-pop-scratch stack)))))
		:hints (("goal" :use stack$a-open-nth-scratch))))

       (local (defthm fgl-objectlist-concretize-of-arglist-scratchobj-rewrite-with-fgl-major-stack-concretize
		(implies (and (scratchobj-case (stack$a-top-scratch stack) :fgl-arglist)
			      (not (fgl-arglist-unbounds (scratchobj-fgl-arglist->val
							  (stack$a-top-scratch stack))))
			      (stack-equiv-except-top-bindings
			       conc (double-rewrite (fgl-major-stack-concretize stack env logicman)))
			      (syntaxp (case-match conc
					 (('fgl-major-stack-concretize-fn stack1 & logicman1)
					  (not (and (equal stack1 stack) (equal logicman1 logicman))))
					 (& t))))
			 (equal (fgl-objectlist-concretize
				 (fgl-arglist->objects
				  (scratchobj-fgl-arglist->val
				   (stack$a-top-scratch stack)))
				 env logicman)
				(fgl-arglist->objects
				 (scratchobj-fgl-arglist->val
				  (stack$a-top-scratch conc)))))
		:hints(("Goal" :in-theory (e/d (stack$a-top-scratch
						fgl-major-frame-concretize
						fgl-minor-frame-concretize
						stack-equiv-except-top-bindings
						minor-stack-equiv-except-top-debug
						fgl-scratchobj-concretize
						cons-equal)
					       (FGL-SCRATCHLIST-CONCRETIZE-OF-CDR))
			:expand ((fgl-major-stack-concretize stack env logicman)
				 (fgl-minor-stack-concretize (major-frame->minor-stack (car stack)) env logicman)
				 (:free (frame)
				  (fgl-scratchlist-concretize
				   (minor-frame->scratch frame) env logicman)))))))

       (local (defthm fgl-arglist-concretize-of-arglist-scratchobj-rewrite-with-fgl-major-stack-concretize
		(implies (and (scratchobj-case (stack$a-top-scratch stack) :fgl-arglist)
			      (stack-equiv-except-top-bindings
			       conc (double-rewrite (fgl-major-stack-concretize stack env logicman)))
			      (syntaxp (case-match conc
					 (('fgl-major-stack-concretize-fn stack1 & logicman1)
					  (not (and (equal stack1 stack) (equal logicman1 logicman))))
					 (& t))))
			 (equal (fgl-arglist-concretize
				 (scratchobj-fgl-arglist->val
				  (stack$a-top-scratch stack))
				 env logicman)
				(scratchobj-fgl-arglist->val
				 (stack$a-top-scratch conc))))
		:hints(("Goal" :in-theory (e/d (stack$a-top-scratch
						fgl-major-frame-concretize
						fgl-minor-frame-concretize
						stack-equiv-except-top-bindings
						minor-stack-equiv-except-top-debug
						fgl-scratchobj-concretize
						cons-equal)
					       (FGL-SCRATCHLIST-CONCRETIZE-OF-CDR))
			:expand ((fgl-major-stack-concretize stack env logicman)
				 (fgl-minor-stack-concretize (major-frame->minor-stack (car stack)) env logicman)
				 (:free (frame)
				  (fgl-scratchlist-concretize
				   (minor-frame->scratch frame) env logicman)))))))

       (local (def-updater-independence-thm lookup-present-in-stack-minor-bindings-when-binding-domains-preserved
		(implies (stack-equiv-except-top-bindings
			  (stack-binding-domains (interp-st->stack new))
			  (stack-binding-domains (interp-st->stack old)))
			 (iff (hons-assoc-equal k (stack$a-minor-bindings (interp-st->stack new)))
			      (hons-assoc-equal k (stack$a-minor-bindings (interp-st->stack old)))))
		:hints (("Goal" :use ((:instance hons-assoc-equal-of-minor-bindings-when-binding-domains-preserved
				       (new (interp-st->stack new))
				       (old (interp-st->stack old))))))))

       (defcong stack-equiv-except-top-bindings equal (stack$a-top-scratch stack) 1
	 :hints(("Goal" :in-theory (enable stack$a-top-scratch
					   stack-equiv-except-top-bindings
					   minor-stack-equiv-except-top-debug))))

       (local (defthm fgl-scratchobj-concretize-of-stack$a-top-scratch-rewrite-with-major-stack
		(implies (and (stack-equiv-except-top-bindings conc (Double-rewrite (fgl-major-stack-concretize stack env)))
			      (syntaxp (case-match conc
					 (('fgl-major-stack-concretize-fn conc2 . &)
					  (not (equal conc2 stack)))
					 (& t))))
			 (equal (fgl-scratchobj-concretize (stack$a-top-scratch stack) env)
				(fgl-scratchobj-concretize (stack$a-top-scratch conc) nil nil))))))

     (defsection-progn fgl-interp-boolean-evaluation-normalization

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

       (defthm stack$a-bindings-of-stack$a-pop-scratch
	 (equal (stack$a-bindings (stack$a-pop-scratch stack))
		(stack$a-bindings stack))
	 :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-pop-scratch)))))

     (local (in-theory (disable not)))

     (local (defret interp-st-try-equivalences-correct-under-iff
	      (implies (and (equal logicman (interp-st->logicman interp-st))
			    (equal (interp-st->equiv-contexts interp-st) '(iff))
			    (case-split (not (interp-st->errmsg new-interp-st)))
			    (logicman-pathcond-eval (fgl-env->bfr-vals env)
						    (interp-st->pathcond interp-st)
						    (interp-st->logicman interp-st))
			    (interp-st-bfrs-ok interp-st)
			    (case-split (interp-st-bvar-db-ok interp-st env)))
		       (iff (fgl-object-eval xobj env logicman)
			    (fgl-object-eval x env logicman)))
	      :hints (("Goal" :use interp-st-try-equivalences-correct
		       :in-theory (disable interp-st-try-equivalences-correct
					   interp-st-try-equivalences-correct-rw)))
	      :fn interp-st-try-equivalences))

     (local (defthm fgl-ev-of-fncall-reconstruction
	      (implies (pseudo-term-case x :fncall)
		       (equal (fgl-ev (cons (pseudo-term-fncall->fn x) (pseudo-term-call->args x)) al)
			      (fgl-ev x al)))
	      :hints (("Goal" :in-theory (enable fgl-ev-when-pseudo-term-fncall))))))))


(with-output :off :all :on (error summary) :summary-off :all :summary-on (acl2::form acl2::time) :gag-mode t
  (local
   ;; These semantic conclusions remain mutually inductive.  Lambda stability
   ;; needs agreement of the produced minor bindings with the source bindings;
   ;; evaluation agreement needs stability across later binding extensions.
   ;; Constraint validity and reachability also depend on evaluation.
   (defsection-unique fgl-interp-correct

     (defconst *fgl-interp-correct-body*
       '(std::defret-generate <fn>-correct
	  :formal-hyps (((interp-st-bfr-p x)           (interp-st-bfr-p x))
			((fgl-object-p x)               (fgl-object-bfrs-ok x (interp-st-bfrstate)))
			((fgl-objectlist-p x)           (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
			((fgl-arglist-p x)              (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
			((fgl-object-bindings-p x)      (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
			(interp-st                     (interp-st-bfrs-ok interp-st))
			((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate)))
			(state                         (and (fgl-ev-meta-extract-global-facts :state st)
							    (equal (w st) (w state))
							    (fgl-formula-checks-stub st))))
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
		       (:fnname fgl-rewrite-try-merge-rules)
		       (:fnname fgl-rewrite-try-remaining-merge-rules))
		   (:add-hyp (and (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist)
				  (not (intersectp-equal (fgl-arglist-unbounds (stack$a-top-scratch-fgl-arglist (interp-st->stack interp-st)))
							 (alist-keys (interp-st-bindings interp-st))))))

		   (:add-bindings
		    ((args (interp-st-top-scratch-fgl-arglist interp-st))
		     (?call-ev (fgl-ev (pseudo-term-fncall
					fn (kwote-lst
					    (fgl-arglist-eval-with-rev-subst
					     args
					     (fgl-object-bindings-eval
					      (interp-st-bindings new-interp-st)
					      env new-logicman)
					     env logicman)))
				       nil)))))

		  ((or (:fnname fgl-rewrite-fncall)
		       (:fnname fgl-interp-fncall)
		       (:fnname fgl-interp-fncall-casesplit))
		   (:add-hyp (not (intersectp-equal (fgl-arglist-unbounds args)
						    (alist-keys (stack$a-bindings (interp-st->stack interp-st)))))))

		  ((or (:fnname fgl-rewrite-apply-rule))
		   (:add-hyp
		    (and (not (intersectp-equal (alist-keys (pseudo-term-subst-fix rev-subst))
						(alist-keys (interp-st-bindings interp-st))))
			 (no-duplicatesp-equal (alist-keys (pseudo-term-subst-fix rev-subst))))))

		  ((:fnname fgl-interp-add-constraints-for-substs)
		   (:push-hyp (and (not (pathcond-enabledp (interp-st->pathcond interp-st)))
				   (equal (interp-st->equiv-contexts interp-st) '(iff)))))

		  ((:fnname fgl-interp-handle-error-body)
		   (:add-hyp (member-equal 'unequiv (equiv-contexts-fix (interp-st->equiv-contexts interp-st)))))

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
		  ((or (:fnname fgl-interp-if-else)
		       (:fnname fgl-interp-fncall-casesplit-else))
		   (:push-hyp (implies (gobj-bfr-eval testbfr env logicman)
				       (not then-unreachable))))

		  (t (:push-hyp (not (interp-st->errmsg interp-st))))

		  (t (:add-concl ;; (implies (and (not (interp-st->errmsg interp-st))
		      ;;               (logicman-pathcond-eval (fgl-env->bfr-vals env)
		      ;;                                       (interp-st->pathcond interp-st)
		      ;;                                       logicman))
		      (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

		  (t (:pop-hyp)
		     (:push-hyp
		      (not (interp-st->errmsg new-interp-st))))

		  ((or (:fnname fgl-interp-test)
		       (:fnname fgl-interp-test-under-pathcond))
		   (:add-concl
		    ;; (iff* (gobj-bfr-eval xbfr env new-logicman)
		    ;;       (fgl-ev x eval-alist))
		    (and
		     (iff?-forall-extensions (interp-st->equiv-contexts interp-st) x eval-alist)
		     (implies
		      (not (member-eq 'unequiv (equiv-contexts-fix (interp-st->equiv-contexts interp-st))))
		      (iff (fgl-ev x eval-alist) (gobj-bfr-eval xbfr env new-logicman))))))

		  ((or (:fnname fgl-interp-term-equivs)
		       (:fnname fgl-interp-term-top)
		       (:fnname fgl-interp-term)
		       (:fnname fgl-interp-time$)
		       (:fnname fgl-interp-return-last)
		       ;; (:fnname fgl-interp-prog2)
		       (:fnname fgl-interp-narrow-equiv))
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      x
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval xobj env new-logicman))
		      (fgl-ev-context-fix (interp-st->equiv-contexts interp-st) (fgl-ev x eval-alist))))))

		  ((:fnname fgl-interp-fncall-special)
		   (:add-concl
		    (implies successp
			     (and
			      (fgl-ev-context-equiv-forall-extensions
			       (interp-st->equiv-contexts interp-st)
			       (pseudo-term-fncall fn args)
			       eval-alist)
			      (equal
			       (fgl-ev-context-fix
				(interp-st->equiv-contexts interp-st)
				(fgl-object-eval ans env new-logicman))
			       (fgl-ev-context-fix
				(interp-st->equiv-contexts interp-st)
				(fgl-ev (pseudo-term-fncall fn args) eval-alist)))))))

		  ((:fnname fgl-interp-conditionalize-bind)
		   (:add-concl
		    (implies successp
			     (and
			      (fgl-ev-context-equiv-forall-extensions
			       (interp-st->equiv-contexts interp-st)
			       (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
			       eval-alist)
			      (equal
			       (fgl-ev-context-fix
				(interp-st->equiv-contexts interp-st)
				(fgl-object-eval ans env new-logicman))
			       (fgl-ev-context-fix
				(interp-st->equiv-contexts interp-st)
				(fgl-ev
				 (pseudo-term-fncall 'conditionalize2 (list freevar test x on-unreach))
				 eval-alist)))))))

		  ((:fnname fgl-interp-fncall-nonspecial-top)
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      (pseudo-term-fncall fn args)
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval xobj env new-logicman))
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-ev (pseudo-term-fncall fn args) eval-alist))))))

		  ((:fnname fgl-interp-sat-check)
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      `(if ,x 't 'nil)
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval xobj env new-logicman))
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-ev `(if ,x 't 'nil) eval-alist))))))

		  ((or (:fnname fgl-interp-assume)
		       (:fnname fgl-interp-handle-error)
		       (:fnname fgl-interp-handle-error-body))
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      x
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval ans env new-logicman))
		      (fgl-ev-context-fix (interp-st->equiv-contexts interp-st) (fgl-ev x eval-alist))))))

		  ((:fnname fgl-interp-conditionalize-branch)
		   (:add-concl
		    (implies (gobj-bfr-eval testbfr env logicman)
			     (and (fgl-ev-context-equiv-forall-extensions
				   (interp-st->equiv-contexts interp-st) x eval-alist)
				  (equal (fgl-ev-context-fix
					  (interp-st->equiv-contexts interp-st)
					  (fgl-object-eval ans env new-logicman))
					 (fgl-ev-context-fix
					  (interp-st->equiv-contexts interp-st)
					  (fgl-ev x eval-alist)))))))

		  ((:fnname fgl-interp-fncall-casesplit-else)
		   (:add-concl
		    (equal (fgl-ev-context-fix
			    (interp-st->equiv-contexts interp-st)
			    (fgl-object-eval ans env new-logicman))
			   (fgl-ev-context-fix
			    (interp-st->equiv-contexts interp-st)
			    (if* (gobj-bfr-eval testbfr env logicman)
				 (fgl-object-eval then-val env logicman)
				 (fgl-ev (cons (pseudo-fnsym-fix fn)
					       (kwote-lst (fgl-objectlist-eval else-args env logicman)))
					 nil))))))

		  ((:fnname fgl-interp-simplify-if-test-branches)
		   (:add-concl
		    (iff* (gobj-bfr-eval xbfr env new-logicman)
			  (if* (gobj-bfr-eval test-bfr env logicman)
			       (fgl-object-eval thenval env logicman)
			       (fgl-object-eval elseval env logicman)))))

		  ((:fnname fgl-rewrite-apply-rule-prep)
		   (:add-hyp (not (interp-st-minor-bindings interp-st)))
		   (:add-concl
		    (b* ((new-ev-al (fgl-object-bindings-eval (interp-st-bindings new-interp-st)
							      env new-logicman))
			 (ev-al (fgl-object-bindings-eval (interp-st-bindings interp-st) env logicman)))
		      (implies (not failed-hyp)
			       (and (eval-alist-extension-p new-ev-al ev-al)
				    (iff-forall-extensions (conjoin hyps) new-ev-al)
				    (equal-subst-forall-extensions rev-subst new-ev-al)
				    (fgl-ev (conjoin hyps) new-ev-al)
				    (equal (fgl-object-bindings-eval rev-bindings env new-logicman)
					   (fgl-ev-alist rev-subst new-ev-al)))))))

		  ((:fnname fgl-interp-conditionalize)
		   (:add-concl
		    (and
		     ;; this basically just says that whatever test evaluates to
		     ;; under the output alist, it won't change its value under
		     ;; an extension to that alist -- because, basically, the
		     ;; variables used in test are bound in eval-alist. We need
		     ;; this because the rest of the correctness property is
		     ;; conditional on the evaluation of test.
		     (iff?-forall-extensions (interp-st->equiv-contexts interp-st) test eval-alist)
		     (implies (fgl-ev test eval-alist)
			      (and
			       (fgl-ev-context-equiv-forall-extensions
				(interp-st->equiv-contexts interp-st)
				x
				eval-alist)
			       (equal
				(fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (fgl-object-eval ans env new-logicman))
				(fgl-ev-context-fix (interp-st->equiv-contexts interp-st) (fgl-ev x eval-alist))))))))

		  ((:fnname fgl-interp-fgl-interp-obj)
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      nil
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval ans env new-logicman))
		      (fgl-ev-context-fix (interp-st->equiv-contexts interp-st) (fgl-ev nil eval-alist))))))

		  ((:fnname fgl-interp-arglist)
		   (:add-concl
		    (and
		     (fgl-ev-argcontexts-equiv-forall-extensions
		      (fgl-arglist-bound-contexts arg-objs argcontexts)
		      args
		      eval-alist)
		     (fgl-ev-arglist-contexts-equiv argcontexts arg-objs args eval-alist env new-logicman))))

		  ((:fnname fgl-interp-lambda-arglist)
		   (:add-concl
		    (and
		     (equal?-list-forall-extensions (interp-st->equiv-contexts interp-st) args eval-alist)
		     (implies
		      (equal (equiv-contexts-fix (interp-st->equiv-contexts interp-st)) nil)
		      (equal (fgl-ev-list args eval-alist) (fgl-objectlist-eval arg-objs env new-logicman))))))
		  ((:fnname fgl-interp-bindinglist)
		   (:add-concl
		    (and
		     (equal?-bindinglist-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      bindings
		      minor-alist
		      major-alist)
		     (implies
		      (equal (equiv-contexts-fix (interp-st->equiv-contexts interp-st)) nil)
		      (equal
		       (fgl-ev-bindinglist-minmaj bindings minor-alist major-alist)
		       (fgl-object-bindings-eval (stack$a-minor-bindings new-stack) env new-logicman))))))

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
					   (fgl-arglist-eval-with-rev-subst
					    args
					    (fgl-object-bindings-eval
					     (interp-st-bindings new-interp-st)
					     env new-logicman)
					    env logicman)))
				    nil)))))
		  ((:fnname fgl-interp-postprocess-rewritten-obj)
		   (:add-concl
		    (equal (fgl-ev-context-fix
			    (interp-st->equiv-contexts interp-st)
			    (fgl-object-eval xobj env new-logicman))
			   (fgl-ev-context-fix
			    (interp-st->equiv-contexts interp-st)
			    (fgl-object-eval x env logicman)))))
		  ((:fnname fgl-interp-fncall-casesplit-branches)
		   (:add-concl
		    (equal (fgl-ev-context-fix
			    (interp-st->equiv-contexts interp-st)
			    (fgl-object-eval ans env new-logicman))
			   (fgl-ev-context-fix
			    (interp-st->equiv-contexts interp-st)
			    (fgl-ev (cons (pseudo-fnsym-fix fn)
					  (kwote-lst
					   (fgl-objectlist-eval
					    (if* (gobj-bfr-eval testbfr env logicman)
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
							 (fgl-objectlist-eval
							  args env logicman)))
						  nil)))
				  (not unreachable)))))

		  ((:fnname fgl-rewrite-fncall)
		   (:add-concl
		    (implies successp
			     (and
			      (equal (fgl-ev-context-fix
				      (interp-st->equiv-contexts interp-st)
				      (fgl-object-eval ans env new-logicman))
				     (fgl-ev-context-fix
				      (interp-st->equiv-contexts interp-st)
				      (fgl-ev (cons (pseudo-fnsym-fix fn)
						    (kwote-lst
						     (fgl-arglist-eval-with-rev-subst
						      args
						      (fgl-object-bindings-eval
						       (interp-st-bindings new-interp-st)
						       env new-logicman)
						      env logicman)))
					      nil)))))))

		  ((:fnname fgl-rewrite-try-rule)
		   (:add-concl
		    (implies (and successp
				  (fgl-ev-theoremp (fgl-rule-term rule)))
			     (fgl-ev-context-equiv
			      (interp-st->equiv-contexts interp-st)
			      (fgl-object-eval ans env new-logicman)
			      call-ev))))

		  ((:fnname fgl-rewrite-apply-rule)

		   (:add-concl
		    (b* ((new-ev-al (fgl-object-bindings-eval new-bindings env new-logicman))
			 (ev-al (fgl-object-bindings-eval bindings env logicman)))
		      (implies successp
			       (and (eval-alist-extension-p new-ev-al ev-al)
				    (fgl-ev (conjoin hyps) new-ev-al)
				    (equal
				     (fgl-ev-context-fix rhs-equiv
							 (fgl-object-eval ans env new-logicman))
				     (fgl-ev-context-fix rhs-equiv
							 (fgl-ev rhs new-ev-al)))
				    (eval-alist-extension-p
				     (fgl-object-bindings-eval
				      (interp-st-bindings new-interp-st)
				      env new-logicman)
				     (fgl-ev-alist rev-subst new-ev-al)))))))

		  ((:fnname fgl-rewrite-apply-rule-core)
		   (:add-hyp (not (interp-st-minor-bindings interp-st)))
		   (:add-concl
		    (b* ((new-ev-al (fgl-object-bindings-eval (interp-st-bindings new-interp-st)
							      env new-logicman))
			 (ev-al (fgl-object-bindings-eval (interp-st-bindings interp-st) env logicman)))
		      (implies (not failed-hyp)
			       (and (eval-alist-extension-p new-ev-al ev-al)
				    (fgl-ev (conjoin hyps) new-ev-al)
				    (equal
				     (fgl-ev-context-fix rhs-equiv
							 (fgl-object-eval ans env new-logicman))
				     (fgl-ev-context-fix rhs-equiv
							 (fgl-ev rhs new-ev-al)))
				    (equal
				     (fgl-object-bindings-eval rev-bindings env new-logicman)
				     (fgl-ev-alist rev-subst new-ev-al)))))))

		  ((:fnname fgl-rewrite-reverse-subst)
		   (:add-hyp (not (interp-st-minor-bindings interp-st)))
		   (:add-concl
		    (and
		     (equal-subst-forall-extensions
		      subst
		      (fgl-object-bindings-eval (interp-st-bindings new-interp-st)
						env new-logicman))
		     (equal
		      (fgl-ev-alist
		       subst
		       (fgl-object-bindings-eval (interp-st-bindings new-interp-st)
						 env new-logicman))
		      (fgl-object-bindings-eval bindings env new-logicman)))))

		  ((:fnname fgl-rewrite-try-rewrite)
		   (:add-concl
		    (implies (and successp
				  (fgl-rule-case rule :rewrite)
				  (fgl-ev-theoremp (fgl-rule-term rule)))
			     (fgl-ev-context-equiv
			      (interp-st->equiv-contexts interp-st)
			      (fgl-object-eval ans env new-logicman)
			      call-ev))))

		  ((:fnname fgl-rewrite-try-meta)
		   (:add-concl
		    (implies (and successp)
			     (fgl-ev-context-equiv
			      (interp-st->equiv-contexts interp-st)
			      (fgl-object-eval ans env new-logicman)
			      call-ev))))

		  ((:fnname fgl-rewrite-try-rules)
		   (:add-concl
		    (implies (and successp
				  (fgl-good-fgl-rules-p rules))
			     (equal (fgl-ev-context-fix
				     (interp-st->equiv-contexts interp-st)
				     (fgl-object-eval ans env new-logicman))
				    (fgl-ev-context-fix
				     (interp-st->equiv-contexts interp-st)
				     call-ev)))))

		  ((:fnname fgl-rewrite-try-merge-rules)
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
						    (fgl-arglist-eval-with-rev-subst
						     (interp-st-top-scratch-fgl-arglist interp-st)
						     (fgl-object-bindings-eval
						      (interp-st-bindings new-interp-st)
						      env new-logicman)
						     env logicman)))
					     nil))))))

		  ((:fnname fgl-rewrite-try-remaining-merge-rules)
		   (:add-concl
		    (implies (and successp
				  (fgl-good-fgl-rules-p rules1)
				  (fgl-good-fgl-rules-p rules2))
			     (equal (fgl-ev-context-fix
				     (interp-st->equiv-contexts interp-st)
				     (fgl-object-eval ans env new-logicman))
				    (fgl-ev-context-fix
				     (interp-st->equiv-contexts interp-st)
				     (fgl-ev (cons (pseudo-fnsym-fix fn)
						   (kwote-lst
						    (fgl-arglist-eval-with-rev-subst
						     (interp-st-top-scratch-fgl-arglist interp-st)
						     (fgl-object-bindings-eval
						      (interp-st-bindings new-interp-st)
						      env new-logicman)
						     env logicman)))
					     nil))))))

		  ((:fnname fgl-rewrite-relieve-hyps)
		   (:add-concl
		    (implies (and (not failed-hyp)
				  (equal (interp-st->equiv-contexts interp-st) '(iff)))
			     (and
			      (iff-forall-extensions (conjoin hyps) eval-alist)
			      (iff (fgl-ev (conjoin hyps) eval-alist) t)))))
		  ((:fnname fgl-rewrite-relieve-hyp)
		   (:add-concl
		    (implies (and successp
				  (equal (interp-st->equiv-contexts interp-st) '(iff)))
			     (and (iff-forall-extensions hyp eval-alist) (iff (fgl-ev hyp eval-alist) t)))))
		  ((:fnname fgl-interp-binding-hyp)
		   (:add-concl
		    (implies okp
			     (and (iff-forall-extensions hyp eval-alist) (iff (fgl-ev hyp eval-alist) t)))))
		  ((:fnname fgl-interp-if-branches)
		   (:add-concl
		    (and (if (gobj-bfr-eval testbfr env logicman)
			     (fgl-ev-context-equiv-forall-extensions
			      (interp-st->equiv-contexts interp-st) then eval-alist)
			   (fgl-ev-context-equiv-forall-extensions
			    (interp-st->equiv-contexts interp-st) else eval-alist))
			 (equal (fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (fgl-object-eval ans env new-logicman))
				(fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (if (gobj-bfr-eval testbfr env logicman)
				     (fgl-ev then eval-alist)
				   (fgl-ev else eval-alist)))))))

		  ((:fnname fgl-interp-if-else)
		   (:add-concl
		    (and (implies (not (gobj-bfr-eval testbfr env logicman))
				  (fgl-ev-context-equiv-forall-extensions
				   (interp-st->equiv-contexts interp-st) else eval-alist))
			 (equal (fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (fgl-object-eval ans env new-logicman))
				(fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (if (gobj-bfr-eval testbfr env logicman)
				     (fgl-object-eval thenval env logicman)
				   (fgl-ev else eval-alist)))))))

		  ((:fnname fgl-interp-or-else)
		   (:add-concl
		    (and (implies (not (fgl-object-eval testval env logicman))
				  (fgl-ev-context-equiv-forall-extensions
				   (interp-st->equiv-contexts interp-st) else eval-alist))
			 (equal (fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (fgl-object-eval ans env new-logicman))
				(fgl-ev-context-fix
				 (interp-st->equiv-contexts interp-st)
				 (or (fgl-object-eval testval env logicman)
				     (fgl-ev else eval-alist)))))))

		  ((or (:fnname fgl-interp-if/or)
		       (:fnname fgl-interp-if)
		       (:fnname fgl-interp-if-nonbranching))
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      (pseudo-term-fncall 'if (list test then else))
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval ans env new-logicman))
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-ev (pseudo-term-fncall 'if (list test then else)) eval-alist))))))
		  ((or (:fnname fgl-interp-or)
		       (:fnname fgl-interp-or-nonbranching))
		   (:add-concl
		    (and
		     (fgl-ev-context-equiv-forall-extensions
		      (interp-st->equiv-contexts interp-st)
		      (pseudo-term-fncall 'if (list test test else))
		      eval-alist)
		     (equal
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval ans env new-logicman))
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-ev (pseudo-term-fncall 'if (list test test else)) eval-alist))))))
		  ((:fnname fgl-maybe-interp)
		   (:add-concl
		    (implies (gobj-bfr-eval test env logicman)
			     (and (and
				   (fgl-ev-context-equiv-forall-extensions
				    (interp-st->equiv-contexts interp-st)
				    x
				    eval-alist)
				   (equal
				    (fgl-ev-context-fix
				     (interp-st->equiv-contexts interp-st)
				     (fgl-object-eval ans env new-logicman))
				    (fgl-ev-context-fix (interp-st->equiv-contexts interp-st) (fgl-ev x eval-alist))))
				  (not unreachable)))))
		  ((:fnname fgl-interp-maybe-simplify-if-test)
		   (:add-concl
		    (implies (gobj-bfr-eval test env logicman)
			     (and (iff* (gobj-bfr-eval xbfr env new-logicman)
					(fgl-object-eval xobj env logicman))
				  (not unreachable)))))

		  ((or (:fnname fgl-interp-simplify-if-test)
		       (:fnname fgl-interp-simplify-if-test1))
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
	      (std::defret-mutual-generate
		,*fgl-interp-correct-body*
		:hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
			(b* ((flag (find-flag-is-hyp clause))
			     ((unless flag) (value nil))
			     (state (f-put-global 'fgl-interp-term-subgoals
						  (cons clause (@ fgl-interp-term-subgoals))
						  state)))
			  (cw "~x0~%" flag)
			  (value '(:by nil))))
		:mutual-recursion fgl-interp)
	      (value-triple :goals-saved))))))

     (local (defun my-prettyify-clause (clause)
	      (cond ((atom clause) nil)
		    ((atom (cdr clause)) (car clause))
		    ((atom (cddr clause))
		     `(implies ,(acl2::dumb-negate-lit (car clause))
			       ,(cadr clause)))
		    (t `(implies (and . ,(acl2::dumb-negate-lit-lst (take (- (len clause) 1) clause)))
				 ,(nth (- (len clause) 1) clause))))))

     ;; (local
     ;;  (defun prettyify-clause-list (clauses let*-abstractionp wrld)
     ;;    (declare (xargs :mode :program))
     ;;    (if (atom clauses)
     ;;        nil
     ;;      (cons (prettyify-clause (car clauses) let*-abstractionp wrld)
     ;;            (prettyify-clause-list (cdr clauses) let*-abstractionp wrld)))))

     (local (defun fgl-interp-clause-to-defthm (clause base-name let*-absp flag-index-alist hints wrld)
	      (declare (xargs :mode :program)
		       (ignorable let*-absp wrld))
	      (b* ((flag (find-flag-is-hyp clause))
		   (goal ;; (acl2::prettyify-clause clause let*-absp wrld)
		    (my-prettyify-clause clause))
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

     ;; NOTE: accumulated persistence hacking -- try enabling these if proofs fail unexpectedly
     (local (in-theory (disable logicman-extension-of-update-2
				bfr-listp-when-logicman-extension
				logicman->mode-of-interp-st-logicman-extension
				logicman->aignet-of-interp-st->logicman
				INTERP-ST-FIELD-FIX-UNDER-INTERP-ST-FIELD-EQUIV
				logicman->bfrstate-updater-independence
				fgl-object-bindings-eval-of-stack-bindings-extension-p)))
     (local (in-theory (enable interp-st-get-term->bvar)))
     (make-event
      `(acl2::run-events-stop-on-failure
	,(fgl-interp-clauses-to-defthms
	  (@ fgl-interp-term-subgoals)
	  'fgl-interp-correct
	  nil nil
	  '(("goal" :do-not-induct t :do-not '(generalize))
	    (and stable-under-simplificationp
		 (case (find-flag-is-hyp clause)
		   (fgl-rewrite-reverse-subst
		    '(:expand ((:free (al) (fgl-ev-alist subst al)))))
		   ((fgl-interp-or fgl-interp-or-nonbranching)
		    '(:in-theory (enable iff* fgl-interp-or-test-equiv-contexts)))
		   (fgl-interp-term
		    '(:in-theory (enable fgl-interp-lambda-arglist-equiv-contexts)))
		   (fgl-interp-bindinglist
		    '(:expand ((:free (minor major) (fgl-ev-bindinglist-minmaj bindings minor major)))))
		   (fgl-interp-conditionalize-bind
		    '(:in-theory (enable conditionalize2 sub-alistp-by-witness)))
		   (fgl-interp-fncall-special
		    '(:in-theory (enable conditionalize1 conditionalize2)))
		   (fgl-interp-test
		    '(:in-theory (e/d (iff* iff?-forall-extensions fgl-interp-test-equiv-contexts iff-forall-extensions-necc)
				      (fgl-ev-when-pseudo-term-fncall))))
		   ((fgl-interp-if-else
		     fgl-interp-simplify-if-test-branches
		     fgl-interp-merge-branches
		     fgl-interp-merge-branch-subterms
		     fgl-interp-fncall-casesplit
		     fgl-interp-fncall-casesplit-branches
		     fgl-interp-fncall-casesplit-else)
		    '(:in-theory (enable if*)))
		   (fgl-interp-test-under-pathcond
		    '(:in-theory (enable interp-st-pathcond-assume-contradictionp-implies
					 interp-st-pathcond-assume-neg-contradictionp-implies))))))
	  (w state)))))))


(with-output
  :off (event warning)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (make-event
   `(std::defret-mutual-generate
      ,*fgl-interp-correct-body*
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
	      (b* ((flag (find-flag-is-hyp clause))
                   ((unless flag) (value nil))
                   (thm (cdr (assoc-equal clause (table-alist 'fgl-interp-clauses-table (w state)))))
                   ((unless thm)
		    (cw "Couldn't find theorem for clause: ~x0~%"
		        (acl2::prettyify-clause clause t (w state)))
		    (value '(:error t))))
                (value `(:computed-hint-replacement
                         ('(:error t))
                         :clause-processor (my-by-hint-cp clause ',thm state)))))

      :mutual-recursion fgl-interp)))
