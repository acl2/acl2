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

; Structural and semantic preservation and extension of interpreter bindings.
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

(defsection-progn fgl-interp-binding-preservation-support

  (defcong minor-stack-equiv-except-top-debug minor-stack-equiv-except-top-debug
    (minor-stack-binding-domains x) 1
    :hints (("Goal" :in-theory (enable minor-stack-equiv-except-top-debug
				       minor-stack-binding-domains))))

  (defcong stack-equiv-except-top-bindings stack-equiv-except-top-bindings
    (stack-binding-domains x) 1
    :hints (("Goal" :in-theory (enable stack-equiv-except-top-bindings
				       stack-binding-domains))))

  (defthm stack-equiv-except-top-bindings-of-add-binding-structural
    (stack-equiv-except-top-bindings (stack$a-add-binding var val stack) stack)
    :hints (("Goal" :in-theory (enable stack-equiv-except-top-bindings stack$a-add-binding
				       minor-stack-equiv-except-top-debug default-car))))
  (defret binding-domains-of-fgl-rewrite-relieve-hyp-synp
    (stack-equiv-except-top-bindings
     (stack-binding-domains (interp-st->stack new-interp-st))
     (stack-binding-domains (interp-st->stack interp-st)))
    :hints (("Goal" :in-theory (enable fgl-rewrite-relieve-hyp-synp)))
    :fn fgl-rewrite-relieve-hyp-synp)
  (defthmd stack$a-bindings-of-fgl-major-stack-concretize
    (equal (stack$a-bindings (fgl-major-stack-concretize stack env logicman))
	   (fgl-object-bindings-concretize (stack$a-bindings stack) env logicman))
    :hints(("Goal" :in-theory (enable stack$a-bindings fgl-major-stack-concretize
				      fgl-major-frame-concretize))))

  (defthmd stack$a-minor-bindings-of-fgl-major-stack-concretize
    (equal (stack$a-minor-bindings (fgl-major-stack-concretize stack env logicman))
	   (fgl-object-bindings-concretize (stack$a-minor-bindings stack) env logicman))
    :hints(("Goal" :in-theory (enable stack$a-minor-bindings fgl-major-stack-concretize
				      fgl-major-frame-concretize
				      fgl-minor-stack-concretize
				      fgl-minor-frame-concretize))))

  ;; Share the stack theorem specifications.  Only the semantic projections need
  ;; BFR well-formedness; binding domains are purely structural.
  (define defret-mutual-interp-stack ((name symbolp)
				      (args true-listp)
				      (domainsp booleanp))
    :returns (event true-listp)
    :hooks nil
    `(std::defret-mutual-generate ,name
       :formal-hyps
       ,(and (not domainsp)
	     '(((interp-st-bfr-p x) (interp-st-bfr-p x))
	       ((fgl-object-p x) (fgl-object-bfrs-ok x (interp-st-bfrstate)))
	       ((fgl-objectlist-p x) (fgl-objectlist-bfrs-ok x (interp-st-bfrstate)))
	       ((fgl-arglist-p x) (fgl-arglist-bfrs-ok x (interp-st-bfrstate)))
	       ((fgl-object-bindings-p x) (fgl-object-bindings-bfrs-ok x (interp-st-bfrstate)))
	       (interp-st (interp-st-bfrs-ok interp-st))
	       ((constraint-instancelist-p x) (constraint-instancelist-bfrs-ok x (interp-st-bfrstate)))))
       ,@args
       :mutual-recursion fgl-interp))

  ;; Structural and semantic preservation have the same exceptions and restoration
  ;; cases.  Only the projection of each stack differs.
  (define defret-mutual-interp-stack-preserved ((name symbolp) (domainsp booleanp))
    :returns (event true-listp)
    :hooks nil
    (let ((new-stack (if domainsp
			 '(stack-binding-domains (interp-st->stack new-interp-st))
		       '(fgl-major-stack-concretize (interp-st->stack new-interp-st)
				                    env (interp-st->logicman new-interp-st))))
	  (old-stack (if domainsp
			 '(stack-binding-domains (interp-st->stack interp-st))
		       '(fgl-major-stack-concretize (interp-st->stack interp-st)
				                    env (interp-st->logicman interp-st)))))
      (defret-mutual-interp-stack name
	`(:rules ((t (:add-keyword :hints ('(:do-not-induct t)
					   (let ((flag (find-flag-is-hyp clause)))
					     (and flag
						  (prog2$ (cw "flag: ~x0~%" flag)
							  '(:no-op t)))))))
		  ((not (:fnname fgl-interp-bindinglist))
		   (:add-concl (stack-equiv-except-top-bindings ,new-stack ,old-stack)))
		  ((:fnname fgl-interp-bindinglist)
		   (:add-concl (stack-equiv-except-top-major/minor-bindings ,new-stack ,old-stack)))
		  ((or (:fnname fgl-interp-fncall-special)
		       (:fnname fgl-interp-conditionalize-bind)
		       (:fnname fgl-rewrite-try-rules)
		       (:fnname fgl-rewrite-try-rule)
		       (:fnname fgl-rewrite-try-rewrite)
		       (:fnname fgl-rewrite-try-meta)
		       (:fnname fgl-rewrite-apply-rule))
		   (:add-concl (implies (not successp) (equal ,new-stack ,old-stack))))
		  ((or (:fnname fgl-rewrite-try-rules)
		       (:fnname fgl-rewrite-try-rule)
		       (:fnname fgl-rewrite-try-rewrite)
		       (:fnname fgl-rewrite-try-meta)
		       (:fnname fgl-rewrite-apply-rule))
		   (:add-concl (implies (interp-st->errmsg new-interp-st)
					(equal ,new-stack ,old-stack))))
		  ((or (:fnname fgl-rewrite-try-rules)
		       (:fnname fgl-rewrite-try-rule)
		       (:fnname fgl-rewrite-try-rewrite)
		       (:fnname fgl-rewrite-try-meta)
		       (:fnname fgl-rewrite-try-merge-rules)
		       (:fnname fgl-rewrite-try-remaining-merge-rules))
		   (:add-hyp (scratchobj-case (double-rewrite (stack$a-top-scratch (interp-st->stack interp-st)))
			       :fgl-arglist))))
	  :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)))
	domainsp)))

  ;; Keep the freshness requirements identical for both projections and their
  ;; rewrite companions.  The companions use the already-proved extension facts.
  (define defret-mutual-interp-stack-extended ((name symbolp) (domainsp booleanp) (rewritep booleanp))
    :returns (event true-listp)
    :hooks nil
    (let* ((new-stack (if domainsp
			  '(stack-binding-domains (interp-st->stack new-interp-st))
			'(fgl-major-stack-concretize (interp-st->stack new-interp-st)
				                     env (interp-st->logicman new-interp-st))))
	   (old-stack (if domainsp
			  '(stack-binding-domains (interp-st->stack interp-st))
			'(fgl-major-stack-concretize (interp-st->stack interp-st)
				                     env (interp-st->logicman interp-st))))
	   (older-stack (if domainsp 'old-stack-domain 'old-stack-ev))
	   (concl (if rewritep
		      `(implies (equal (stack$a-bindings ,older-stack)
				       (stack$a-bindings ,old-stack))
				(stack-bindings-extension-p ,new-stack ,older-stack))
		    `(stack-bindings-extension-p ,new-stack ,old-stack))))
      (defret-mutual-interp-stack name
	`(:rules ((t (:add-concl ,concl)
		     ,@(and (not rewritep)
			    '((:add-keyword :hints ('(:do-not-induct t)
						    (let ((flag (find-flag-is-hyp clause)))
						      (and flag
							   (prog2$ (cw "flag: ~x0~%" flag)
								   '(:no-op t)))))))))
		  ((or (:fnname fgl-rewrite-fncall)
		       (:fnname fgl-interp-fncall)
		       (:fnname fgl-interp-fncall-casesplit))
		   (:add-hyp (not (intersectp-equal (fgl-arglist-unbounds args)
						    (alist-keys (stack$a-bindings (interp-st->stack interp-st)))))))
		  ((:fnname fgl-rewrite-apply-rule)
		   (:add-hyp (and (not (intersectp-equal (alist-keys (pseudo-term-subst-fix rev-subst))
							 (alist-keys (interp-st-bindings interp-st))))
				  (no-duplicatesp-equal (alist-keys (pseudo-term-subst-fix rev-subst))))))
		  ((or (:fnname fgl-rewrite-try-rules)
		       (:fnname fgl-rewrite-try-rule)
		       (:fnname fgl-rewrite-try-rewrite)
		       (:fnname fgl-rewrite-try-meta)
		       (:fnname fgl-rewrite-try-merge-rules)
		       (:fnname fgl-rewrite-try-remaining-merge-rules))
		   (:add-hyp (and (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist)
				  (not (intersectp-equal
					(fgl-arglist-unbounds (stack$a-top-scratch-fgl-arglist (interp-st->stack interp-st)))
					(alist-keys (interp-st-bindings interp-st))))))))
	  ,@(if rewritep
		'(:no-induction-hint t)
	      '(:hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)))))
	domainsp))))


(defsection fgl-interp-binding-domains
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (make-event
     (defret-mutual-interp-stack-preserved '<fn>-binding-domains-preserved t))))


(defsection-progn fgl-interp-minor-binding-domain-support

  (defcong stack-equiv-except-top-bindings equal (stack$a-minor-bindings stack) 1
    :hints (("Goal" :in-theory (enable stack$a-minor-bindings
				       minor-stack-equiv-except-top-debug
				       stack-equiv-except-top-bindings))))

  (defthm hons-assoc-equal-of-minor-bindings-when-binding-domains-preserved
    (implies (stack-equiv-except-top-bindings
	      (stack-binding-domains new) (stack-binding-domains old))
	     (iff (hons-assoc-equal k (stack$a-minor-bindings new))
		  (hons-assoc-equal k (stack$a-minor-bindings old))))
    :rule-classes nil
    :hints (("Goal" :use ((:instance minor-bindings-of-stack-binding-domains (x new))
			  (:instance minor-bindings-of-stack-binding-domains (x old))
			  (:instance hons-assoc-equal-of-fgl-bindings-domain (x (stack$a-minor-bindings new)))
			  (:instance hons-assoc-equal-of-fgl-bindings-domain (x (stack$a-minor-bindings old))))
	     :in-theory (disable minor-bindings-of-stack-binding-domains hons-assoc-equal-of-fgl-bindings-domain)))))


(defsection fgl-interp-stack-equiv-except-top-bindings
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (make-event
     (defret-mutual-interp-stack-preserved '<fn>-stack-equiv-except-top-bindings nil)))

  (defthm hons-assoc-equal-of-fgl-object-bindings-concretize
    (iff (hons-assoc-equal v (fgl-object-bindings-concretize bindings env logicman))
	 (hons-assoc-equal v (fgl-object-bindings-fix bindings)))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
				      fgl-object-bindings-fix))))

  (defthm hons-assoc-equal-of-stack$a-minor-bindings-of-fgl-interp-term-top
    (b* (((mv ?ans new-interp-st ?new-state) (fgl-interp-term-top x interp-st state)))
      (iff (hons-assoc-equal v (stack$a-minor-bindings (interp-st->stack new-interp-st)))
	   (hons-assoc-equal v (stack$a-minor-bindings (interp-st->stack interp-st)))))
    :hints (("Goal" :use ((:instance hons-assoc-equal-of-minor-bindings-when-binding-domains-preserved
			   (k v) (new (interp-st->stack (mv-nth 1 (fgl-interp-term-top x interp-st state))))
			   (old (interp-st->stack interp-st))))))))


;; Prove extension once on raw bindings, then project it to evaluations.
(defsection-progn fgl-rewrite-match-assums-bindings-extension

  (defret raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums-index
    (stack-bindings-extension-p (interp-st->stack new-interp-st) (interp-st->stack interp-st))
    :hints (("Goal" :in-theory (enable fgl-rewrite-relieve-hyp-match-assums-index stack-bindings-extension-p
				       stack$a-set-bindings stack$a-bindings)
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums-index)

  (defret raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums-indices
    (stack-bindings-extension-p (interp-st->stack new-interp-st) (interp-st->stack interp-st))
    :hints (("Goal" :in-theory (e/d (fgl-rewrite-relieve-hyp-match-assums-indices) (stack-bindings-extension-p))
	     :induct t)
	    (and stable-under-simplificationp
		 '(:use ((:instance raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums-index
			  (idx (car indices))))
		   :in-theory (disable raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums-index))))
    :fn fgl-rewrite-relieve-hyp-match-assums-indices)

  (defret raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums1
    (stack-bindings-extension-p (interp-st->stack new-interp-st) (interp-st->stack interp-st))
    :hints (("Goal" :in-theory (e/d (fgl-rewrite-relieve-hyp-match-assums1) (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums1)

  (defret raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums0
    (stack-bindings-extension-p (interp-st->stack new-interp-st) (interp-st->stack interp-st))
    :hints (("Goal" :in-theory (e/d (fgl-rewrite-relieve-hyp-match-assums0) (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums0)

  (defret raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums
    (stack-bindings-extension-p (interp-st->stack new-interp-st) (interp-st->stack interp-st))
    :hints (("Goal" :in-theory (e/d (fgl-rewrite-relieve-hyp-match-assums) (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums)

  (defthmd stack-bindings-extension-p-of-concretize
    (implies (stack-bindings-extension-p x y)
	     (stack-bindings-extension-p
	      (fgl-major-stack-concretize x env logicman)
	      (fgl-major-stack-concretize y env logicman)))
    :hints (("Goal" :in-theory (enable stack-bindings-extension-p
				       fgl-major-stack-concretize
				       fgl-major-frame-concretize
				       fgl-bindings-extension-p-of-concretize))))

  (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums-index
    (stack-bindings-extension-p
     (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman interp-st))
     (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))
    :hints (("Goal" :in-theory (e/d (stack-bindings-extension-p-of-concretize)
				    (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums-index)

  (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums-indices
    (stack-bindings-extension-p
     (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman interp-st))
     (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))
    :hints (("Goal" :in-theory (e/d (stack-bindings-extension-p-of-concretize)
				    (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums-indices)

  (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums1
    (stack-bindings-extension-p
     (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman interp-st))
     (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))
    :hints (("Goal" :in-theory (e/d (stack-bindings-extension-p-of-concretize)
				    (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums1)

  (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums0
    (stack-bindings-extension-p
     (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman interp-st))
     (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))
    :hints (("Goal" :in-theory (e/d (stack-bindings-extension-p-of-concretize)
				    (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums0)

  (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums
    (stack-bindings-extension-p
     (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman interp-st))
     (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))
    :hints (("Goal" :in-theory (e/d (stack-bindings-extension-p-of-concretize)
				    (stack-bindings-extension-p))
	     :do-not-induct t))
    :fn fgl-rewrite-relieve-hyp-match-assums)

  (defret stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums-trans
    (implies (and (equal (fgl-major-stack-concretize (interp-st->stack new-interp-st) env logicman)
			 (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman interp-st)))
		  (stack-bindings-extension-p
		   (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st))
		   (fgl-major-stack-concretize (interp-st->stack interp-st1) env (interp-st->logicman interp-st1))))
	     (stack-bindings-extension-p
	      (fgl-major-stack-concretize (interp-st->stack new-interp-st) env
					  logicman)
	      (fgl-major-stack-concretize (interp-st->stack interp-st1) env
					  (interp-st->logicman interp-st1))))
    :hints(("Goal" :in-theory (e/d ()
				   (stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums))
	    :use stack-bindings-extension-p-of-fgl-rewrite-relieve-hyp-match-assums))
    :fn fgl-rewrite-relieve-hyp-match-assums))


(defsection fgl-interp-binding-domains-extension
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

  (local (acl2::use-trivial-ancestors-check))

  (local (progn
	   (def-updater-independence-thm domain-interp-st-stack-bindings-extension-p-trans-rw
	     (implies (and (syntaxp (not (equal old older)))
			   (stack-bindings-extension-p
			    (stack-binding-domains (interp-st->stack new))
			    (stack-binding-domains (interp-st->stack old)))
			   (stack-bindings-extension-p
			    (stack-binding-domains (interp-st->stack old)) older))
		      (stack-bindings-extension-p
		       (stack-binding-domains (interp-st->stack new)) older))
	     :hints (("Goal" :in-theory (enable stack-bindings-extension-p-transitive))))
	   (defthm stack-bindings-extension-p-of-add-binding-trans
	     (implies (and (not (hons-assoc-equal (pseudo-var-fix var) (stack$a-bindings stack1)))
			   (stack-bindings-extension-p stack1 stack2))
		      (stack-bindings-extension-p (stack$a-add-binding var val stack1) stack2))
	     :hints (("Goal" :use ((:instance stack-bindings-extension-p-transitive
				    (x (stack$a-add-binding var val stack1)) (y stack1) (z stack2))))))
	   (defthm fgl-bindings-extension-p-of-append-fresh
	     (implies (and (not (intersectp-equal (alist-keys (fgl-object-bindings-fix bb))
						  (alist-keys (fgl-object-bindings-fix a))))
			   (no-duplicatesp-equal (alist-keys (fgl-object-bindings-fix a))))
		      (fgl-bindings-extension-p (append a bb) bb))
	     :hints (("Goal" :use ((:instance fgl-bindings-extension-p-of-append (b bb)))
		      :in-theory (disable fgl-bindings-extension-p-of-append))))
	   (defthm fgl-object-bindings-p-when-fgl-bfr-object-bindings-p
	     (implies (fgl-bfr-object-bindings-p x bfrstate) (fgl-object-bindings-p x))
	     :hints (("Goal" :in-theory (enable fgl-bfr-object-bindings-p-implies-fgl-object-bindings-p)))
	     :rule-classes :forward-chaining)
	   (defthm fgl-bindings-extension-p-of-domain
	     (implies (fgl-bindings-extension-p x y)
		      (fgl-bindings-extension-p (fgl-bindings-domain x) (fgl-bindings-domain y)))
	     :hints (("Goal" :induct (fgl-bindings-extension-p x y)
		      :in-theory (enable fgl-bindings-extension-p fgl-bindings-domain))))

	   (defthm stack-bindings-extension-p-of-domain
	     (implies (stack-bindings-extension-p x y)
		      (stack-bindings-extension-p (stack-binding-domains x) (stack-binding-domains y)))
	     :hints (("Goal" :in-theory (enable stack-bindings-extension-p)
		      :expand ((stack-binding-domains x) (stack-binding-domains y)))))

	   (defret raw-bindings-extended-of-fgl-rewrite-relieve-hyp-synp
	     (stack-bindings-extension-p (interp-st->stack new-interp-st) (interp-st->stack interp-st))
	     :hints (("Goal" :in-theory (enable fgl-rewrite-relieve-hyp-synp fgl-bfr-object-bindings-p stack-bindings-extension-p
						stack$a-set-bindings stack$a-bindings)
		      :do-not-induct t))
	     :fn fgl-rewrite-relieve-hyp-synp)

	   (defret binding-domains-extended-of-match-assums-trans
	     (implies (stack-bindings-extension-p
		       (stack-binding-domains (interp-st->stack interp-st)) older)
		      (stack-bindings-extension-p
		       (stack-binding-domains (interp-st->stack new-interp-st)) older))
	     :hints (("Goal" :use ((:instance stack-bindings-extension-p-transitive
				    (x (stack-binding-domains (interp-st->stack new-interp-st)))
				    (y (stack-binding-domains (interp-st->stack interp-st)))
				    (z older)))))
	     :fn fgl-rewrite-relieve-hyp-match-assums)
	   (defret binding-domains-extended-of-synp-trans
	     (implies (stack-bindings-extension-p
		       (stack-binding-domains (interp-st->stack interp-st)) older)
		      (stack-bindings-extension-p
		       (stack-binding-domains (interp-st->stack new-interp-st)) older))
	     :hints (("Goal" :use ((:instance stack-bindings-extension-p-transitive
				    (x (stack-binding-domains (interp-st->stack new-interp-st)))
				    (y (stack-binding-domains (interp-st->stack interp-st)))
				    (z older)))))
	     :fn fgl-rewrite-relieve-hyp-synp)
	   (defthm stack-binding-domains-of-stack-add-bindings
	     (equal (stack-binding-domains (stack-add-bindings bindings stack))
		    (stack-add-bindings (fgl-bindings-domain bindings) (stack-binding-domains stack)))
	     :hints (("Goal" :in-theory (enable stack-add-bindings))))))
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (make-event
     (defret-mutual-interp-stack-extended '<fn>-binding-domains-extended t nil))))


(defthm stack-bindings-extension-p-when-equal-bindings
  (implies (and (equal (stack$a-bindings y) (stack$a-bindings z))
		(stack-bindings-extension-p x z))
	   (stack-bindings-extension-p x y))
  :hints (("Goal" :in-theory (enable stack-bindings-extension-p stack$a-bindings))))


(defsection fgl-interp-binding-domains-extension-rw

  (local (in-theory (disable bindings-of-stack-binding-domains)))
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (make-event
     (defret-mutual-interp-stack-extended '<fn>-binding-domains-extended-rw t t))))


(with-output :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (defsection fgl-interp-stack-bindings-extension
    (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

    (local (acl2::use-trivial-ancestors-check))

    (make-event
     (defret-mutual-interp-stack-extended '<fn>-stack-bindings-extended nil nil))

    (make-event
     (defret-mutual-interp-stack-extended '<fn>-stack-bindings-extended-rw nil t))))


(defsection-progn fgl-interp-binding-key-support

  (local (in-theory (enable subsetp-when-set-diff-subsetp)))

  (defthm fgl-arglist-unbounds-of-cons
    (equal (fgl-arglist-unbounds (cons arg rest))
	   (let ((rest (fgl-arglist-unbounds rest)))
	     (fgl-arg-case arg
	       :unbound (cons arg.var rest)
	       :otherwise rest)))
    :hints(("Goal" :in-theory (enable fgl-arglist-unbounds)))))


(def-updater-independence-thm alist-keys-minor-bindings-when-binding-domains-preserved
  (implies (stack-equiv-except-top-bindings
	    (stack-binding-domains (interp-st->stack new))
	    (stack-binding-domains (interp-st->stack old)))
	   (equal (alist-keys (stack$a-minor-bindings (interp-st->stack new)))
		  (alist-keys (stack$a-minor-bindings (interp-st->stack old)))))
  :hints (("Goal" :use ((:instance alist-keys-of-fgl-bindings-domain (x (stack$a-minor-bindings (interp-st->stack new))))
			(:instance alist-keys-of-fgl-bindings-domain (x (stack$a-minor-bindings (interp-st->stack old))))
			(:instance minor-bindings-of-stack-binding-domains (x (interp-st->stack new)))
			(:instance minor-bindings-of-stack-binding-domains (x (interp-st->stack old))))
	   :in-theory (disable minor-bindings-of-stack-binding-domains alist-keys-of-fgl-bindings-domain))))


(defthm stack$a-minor-bindings-of-push-scratch
  (equal (stack$a-minor-bindings (stack$a-push-scratch obj stack))
         (stack$a-minor-bindings stack))
  :hints(("Goal" :in-theory (enable stack$a-minor-bindings
				    stack$a-push-scratch))))


(with-output
  :off (event)
  :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
  (defsection fgl-interp-syntactic-return-properties
    (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))

    (std::defret-mutual fgl-interp-arglist-syntax
      (defret fgl-interp-arglist-syntax
	(and (not (intersectp-equal
		   (alist-keys (stack$a-minor-bindings (interp-st->stack interp-st)))
		   (fgl-arglist-unbounds arg-objs)))
	     (fgl-arglist-unbound-vars-match-p arg-objs args))
	:fn fgl-interp-arglist)
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
	      '(:in-theory (enable fgl-arglist-unbound-vars-match-p)
		:do-not-induct t))
      :mutual-recursion fgl-interp
      :skip-others t)

    (std::defret-mutual alist-keys-of-fgl-rewrite-reverse-subst
      (defret alist-keys-of-fgl-rewrite-reverse-subst
	(equal (alist-keys bindings)
	       (alist-keys (pseudo-term-subst-fix subst)))
	:fn fgl-rewrite-reverse-subst)
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world)
	      '(:in-theory (enable alist-keys pseudo-term-subst-fix)
		:do-not-induct t))
      :mutual-recursion fgl-interp
      :skip-others t)))


(defthm alist-keys-subsetp-when-fgl-bindings-extension-p
  (implies (fgl-bindings-extension-p new old)
	   (subsetp-equal (alist-keys (fgl-object-bindings-fix old))
			  (alist-keys (fgl-object-bindings-fix new))))
  :hints (("Goal" :induct (fgl-bindings-extension-p new old)
	   :in-theory (enable fgl-bindings-extension-p
			      fgl-object-bindings-fix alist-keys))))


(defthm subsetp-alist-keys-when-binding-domains-extended
  (implies (stack-bindings-extension-p
	    (stack-binding-domains (interp-st->stack new))
	    (stack-binding-domains (interp-st->stack old)))
	   (subsetp-equal (alist-keys (stack$a-bindings (interp-st->stack old)))
			  (alist-keys (stack$a-bindings (interp-st->stack new)))))
  :hints (("Goal" :in-theory (enable stack-bindings-extension-p stack$a-bindings)
	   :expand ((stack-binding-domains (interp-st->stack new))
		    (stack-binding-domains (interp-st->stack old)))
	   :use ((:instance alist-keys-subsetp-when-fgl-bindings-extension-p
		  (new (stack$a-bindings (stack-binding-domains (interp-st->stack new))))
		  (old (stack$a-bindings (stack-binding-domains (interp-st->stack old)))))))))


(defsection fgl-interp-unbound-arguments-bound
  (local (in-theory (enable stack$a-update-scratch-in-terms-of-push-pop)))
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-unbound-arguments-bound
      :rules
      (((or (:fnname fgl-rewrite-try-rules)
	    (:fnname fgl-rewrite-try-rule)
	    (:fnname fgl-rewrite-try-rewrite)
	    (:fnname fgl-rewrite-try-meta)
	    (:fnname fgl-rewrite-try-merge-rules)
	    (:fnname fgl-rewrite-try-remaining-merge-rules))
	(:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist))
	(:add-concl
	 (implies (and successp
		       (not (interp-st->errmsg new-interp-st)))
		  (subsetp-equal
		   (fgl-arglist-unbounds (stack$a-top-scratch-fgl-arglist (interp-st->stack interp-st)))
		   (alist-keys (stack$a-bindings (interp-st->stack new-interp-st)))))))
       ((or (:fnname fgl-interp-fncall)
	    (:fnname fgl-interp-fncall-casesplit))
	(:add-concl
	 (implies (not (interp-st->errmsg new-interp-st))
		  (subsetp-equal (fgl-arglist-unbounds args)
				 (alist-keys (stack$a-bindings (interp-st->stack new-interp-st)))))))
       ((:fnname fgl-rewrite-fncall)
	(:add-concl
	 (implies (and successp (not (interp-st->errmsg new-interp-st)))
		  (subsetp-equal (fgl-arglist-unbounds args)
				 (alist-keys (stack$a-bindings (interp-st->stack new-interp-st)))))))
       ((:fnname fgl-rewrite-apply-rule)
	(:add-concl
	 (implies (and successp (not (interp-st->errmsg new-interp-st)))
		  (subsetp-equal (alist-keys (pseudo-term-subst-fix rev-subst))
				 (alist-keys (stack$a-bindings (interp-st->stack new-interp-st)))))))

       (t (:add-keyword :hints ('(:do-not-induct t)))))
      :hints ((fgl-interp-default-hint 'fgl-interp-term id nil world))
      :mutual-recursion fgl-interp))

  ;; The following subsetp-lemma is a version of this tweak to subsetp-transitive --
  ;; (local (defthm subsetp-transitive-tweaked
  ;;          (implies (and (Subsetp-equal (set-difference-equal x z) y)
  ;;                        (subsetp-equal y z))
  ;;                   (subsetp-equal x z))

  (local (defthm subsetp-lemma
	   (implies (and (not (subsetp-equal x z))
			 (subsetp-equal y z))
		    (not (subsetp-equal (set-difference-equal x z) y)))
	   :hints ((acl2::set-reasoning))))

  ;; Note: This rearranges the above inductive theorem into a form we can use
  ;; in the correctness theorem. The fgl-interp-fncall-casesplit one in
  ;; particular needs a strange condition for rewriting to be correctly
  ;; implied.
  (with-output
    :off (event)
    :evisc (:gag-mode (evisc-tuple 8 10 nil nil) :term nil)
    (std::defret-mutual-generate <fn>-unbound-arguments-bound-rw
      :rules
      ((t
	(:add-bindings
	 ((new-binding-keys (alist-keys (stack$a-bindings (interp-st->stack new-interp-st)))))))
       ((or (:fnname fgl-rewrite-try-rules)
	    (:fnname fgl-rewrite-try-rule)
	    (:fnname fgl-rewrite-try-rewrite)
	    (:fnname fgl-rewrite-try-meta)
	    (:fnname fgl-rewrite-try-merge-rules)
	    (:fnname fgl-rewrite-try-remaining-merge-rules))
	(:add-hyp (scratchobj-case (stack$a-top-scratch (interp-st->stack interp-st)) :fgl-arglist))

	(:add-concl
	 (implies (and successp (subsetp-equal unbounds
					       (fgl-arglist-unbounds (stack$a-top-scratch-fgl-arglist (interp-st->stack interp-st))))
		       (case-split (not (interp-st->errmsg new-interp-st))))
		  (subsetp-equal unbounds new-binding-keys))))
       ((:fnname fgl-interp-fncall)
	(:add-concl
	 (implies (and (subsetp-equal unbounds
				      (fgl-arglist-unbounds args))
		       (case-split (not (interp-st->errmsg new-interp-st))))
		  (subsetp-equal unbounds new-binding-keys))))
       ((:fnname fgl-interp-fncall-casesplit)
	(:add-concl
	 (implies (and (subsetp-equal (set-difference-equal unbounds new-binding-keys)
				      (fgl-arglist-unbounds args))
		       (case-split (not (interp-st->errmsg new-interp-st))))
		  (subsetp-equal unbounds new-binding-keys))))
       ((:fnname fgl-rewrite-fncall)
	(:add-concl
	 (implies (and successp (subsetp-equal unbounds (fgl-arglist-unbounds args))
		       (case-split (not (interp-st->errmsg new-interp-st))))
		  (subsetp-equal unbounds new-binding-keys))))
       ((:fnname fgl-rewrite-apply-rule)
	(:add-concl
	 (implies (and successp (subsetp-equal unbounds
					       (alist-keys (pseudo-term-subst-fix rev-subst)))
		       (case-split (not (interp-st->errmsg new-interp-st))))
		  (subsetp-equal unbounds new-binding-keys))))

       (t (:add-keyword :hints ('(:do-not-induct t
				  :use ((:instance <fn>-unbound-arguments-bound))
				  :in-theory (disable <fn>-unbound-arguments-bound))))))
      :no-induction-hint t
      :mutual-recursion fgl-interp)))


;; This book exports its main interpreter results and the supporting lemmas below.
;; Support lemmas are nonlocal so other interpreter proof books can reuse them
;; without duplicating proofs. They stay disabled for clients until explicitly
;; enabled through this named theory; ordinary inclusion uses the main results.
(deftheory interp-bindings-support-rules
  '(true-listp-of-defret-mutual-interp-stack
    true-listp-of-defret-mutual-interp-stack-preserved
    true-listp-of-defret-mutual-interp-stack-extended
    raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums-index
    raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums-indices
    raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums1
    raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums0
    raw-bindings-extended-of-fgl-rewrite-relieve-hyp-match-assums
    stack-bindings-extension-p-when-equal-bindings
    fgl-arglist-unbounds-of-cons
    alist-keys-minor-bindings-when-binding-domains-preserved
    alist-keys-subsetp-when-fgl-bindings-extension-p
    subsetp-alist-keys-when-binding-domains-extended))
(in-theory
 (disable defret-mutual-interp-stack
          defret-mutual-interp-stack-preserved
          defret-mutual-interp-stack-extended
          stack$a-bindings-of-fgl-major-stack-concretize
          stack$a-minor-bindings-of-fgl-major-stack-concretize
          stack-bindings-extension-p-of-concretize
          interp-bindings-support-rules))