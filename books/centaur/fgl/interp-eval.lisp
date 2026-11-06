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

; Evaluation relations and supporting correctness lemmas.
; Include interp.lisp for the complete interpreter correctness result.
;
; Retain the original interpreter's CMUCL exclusion: its stack-binding
; extension proofs exhausted the CMUCL dynamic heap (September 2023).
; cert-param: non-cmucl

(in-package "FGL")

(include-book "interp-defs")
(local (include-book "tools/trivial-ancestors-check" :dir :system))

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

(defsection-progn fgl-ev-alist-fixing-support

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

  (local (in-theory (enable alist-fix-of-append)))

  (progn

    (fty::deffixtype alistp :pred alistp :fix acl2::alist-fix :equiv alistp-equiv :define t :forward t)

    (fty::deffixcong alistp-equiv equal (fgl-ev x a) a)
    (fty::deffixcong alistp-equiv equal (fgl-ev-list x a) a)

    (fty::deffixcong alistp-equiv alistp-equiv (append a b) a)
    (fty::deffixcong alistp-equiv alistp-equiv (append a b) b)

    (fty::deffixcong alistp-equiv equal (hons-assoc-equal x a) a)))


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
  (local
   (defthmd fgl-ev-bindinglist-minmaj-in-terms-of-fgl-ev-bindinglist-lemma
     (equal (append (fgl-ev-bindinglist-minmaj x minor major) (acl2::alist-fix major))
	    (fgl-ev-bindinglist x (append minor major)))
     :hints(("Goal" :in-theory (enable fgl-ev-bindinglist)))))

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
    :fn lambda-nest-to-bindinglist))


(defsection-progn fgl-ev-fixing-and-concretization-support

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

  (defthm fgl-object-bindings-eval-of-fgl-object-bindings-concretize
    (equal (fgl-object-bindings-eval (fgl-object-bindings-concretize x env) env2 logicman2)
	   (fgl-object-bindings-eval x env))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
				      fgl-object-bindings-eval))))

  (defthm hons-assoc-equal-of-fgl-object-bindings-eval-under-iff
    (iff (hons-assoc-equal k (fgl-object-bindings-eval x env))
	 (hons-assoc-equal k (fgl-object-bindings-fix x)))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-eval
				      fgl-object-bindings-fix)))))


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

  )


(local (in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes)))


(defsection-progn fgl-ev-environment-extension-support

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

  (defthm eval-alist-extension-p-of-fresh-binding
    (implies (not (hons-assoc-equal var major))
	     (eval-alist-extension-p
	      (append minor (cons (cons var val) major))
	      (append minor major)))
    :hints (("Goal" :in-theory (enable sub-alistp-by-witness))))

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

  (local (in-theory (enable hons-assoc-equal-when-sub-alistp)))

  (local (in-theory (disable acl2::sub-alistp-hons-assoc-equal))))


(defsection fgl-ev-context-equiv-forall-extensions
  (in-theory (disable fgl-ev-context-equiv-forall-extensions
		      fgl-ev-context-equiv-forall-extensions-necc))

  (defthm fgl-ev-context-equiv-forall-extensions-of-extension
    (implies (and (fgl-ev-context-equiv-forall-extensions contexts term eval-alist1)
		  (eval-alist-extension-p eval-alist2 eval-alist1))
	     (fgl-ev-context-equiv-forall-extensions contexts term eval-alist2))
    :hints (("Goal" :expand ((fgl-ev-context-equiv-forall-extensions contexts term eval-alist2))
	     :in-theory (enable fgl-ev-context-equiv-forall-extensions-necc
				eval-alist-extension-p-transitive-1
				eval-alist-extension-p-transitive-2))))

  (defthmd fgl-ev-of-extension-when-equal-forall-extensions
    (implies (and (fgl-ev-context-equiv-forall-extensions nil term eval-alist)
		  (syntaxp (not (equal ext eval-alist)))
		  (eval-alist-extension-p ext eval-alist))
	     (equal (fgl-ev term ext) (fgl-ev term eval-alist)))
    :hints (("Goal" :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
			   (contexts nil))))))

  (local (defthm equal-of-or-test-contexts-implies-contexts
	   (b* ((contexts1 (fgl-interp-or-test-equiv-contexts contexts)))
	     (implies (equal (fgl-ev-context-fix contexts1 x)
			     (fgl-ev-context-fix contexts1 y))
		      (equal (fgl-ev-context-fix contexts x)
			     (fgl-ev-context-fix contexts y))))
	   :hints(("Goal" :in-theory (enable fgl-interp-or-test-equiv-contexts)))
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

  (defthm iff-forall-extensions-of-eval
    (implies (and (iff-forall-extensions term eval-alist1)
		  (eval-alist-extension-p eval-alist2 eval-alist1))
	     (iff-forall-extensions term eval-alist2))
    :hints (("Goal" :expand ((iff-forall-extensions term eval-alist2))
	     :in-theory (e/d (iff-forall-extensions-necc
			      eval-alist-extension-p-transitive-1
			      eval-alist-extension-p-transitive-2) (iff-forall-extensions)))))

  (local (in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes)))

  (defthm fgl-ev-context-equiv-forall-extensions-rewrite-or
    (implies (and (fgl-ev-context-equiv-forall-extensions
		   (fgl-interp-or-test-equiv-contexts contexts)
		   test
		   (append minor-bindings major-bindings0))
		  (fgl-ev-context-equiv-forall-extensions
		   contexts
		   else
		   (append minor-bindings major-bindings1))
		  (eval-alist-extension-p major-bindings1 major-bindings0)
		  (eval-alist-extension-p major-bindings2 major-bindings1))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
	      (pseudo-term-fncall 'if (list test test else))
	      (append minor-bindings major-bindings2)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2 fgl-interp-or-test-equiv-contexts
				       iff-forall-extensions-necc fgl-ev-of-extension-when-equal-forall-extensions))
	    (acl2::Witness :ruleset fgl-ev-context-equiv-forall)
	    (and stable-under-simplificationp
		 '(:use ((:instance fgl-ev-context-equiv-forall-extensions-necc
			  (contexts (fgl-interp-or-test-equiv-contexts contexts))
			  (term test) (eval-alist (append minor-bindings major-bindings0))
			  (ext ext0))
			 (:instance fgl-ev-context-equiv-forall-extensions-necc
			  (contexts (fgl-interp-or-test-equiv-contexts contexts))
			  (term test) (eval-alist (append minor-bindings major-bindings0))
			  (ext (append minor-bindings major-bindings2))))))))

  (defthm fgl-ev-context-equiv-forall-extensions-rewrite-or-when-test
    (implies (and (fgl-ev-context-equiv-forall-extensions
		   (fgl-interp-or-test-equiv-contexts contexts)
		   test
		   (append minor-bindings major-bindings0))
		  (equal
		   (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts) test-ev)
		   (fgl-ev-context-fix
		    (fgl-interp-or-test-equiv-contexts contexts)
		    (fgl-ev test (append minor-bindings major-bindings0))))
		  test-ev
		  (eval-alist-extension-p major-bindings2 major-bindings0))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
	      (pseudo-term-fncall 'if (list test test else))
	      (append minor-bindings major-bindings2)))
    :hints (("goal" :in-theory (e/d (eval-alist-extension-p-transitive-append-2 fgl-interp-or-test-equiv-contexts
										iff-forall-extensions-necc fgl-ev-of-extension-when-equal-forall-extensions)
				    ( if*)))
	    (acl2::Witness :ruleset fgl-ev-context-equiv-forall)
	    (and stable-under-simplificationp
		 '(:use ((:instance fgl-ev-context-equiv-forall-extensions-necc
			  (contexts (fgl-interp-or-test-equiv-contexts contexts))
			  (term test) (eval-alist (append minor-bindings major-bindings0))
			  (ext ext0))
			 (:instance fgl-ev-context-equiv-forall-extensions-necc
			  (contexts (fgl-interp-or-test-equiv-contexts contexts))
			  (term test) (eval-alist (append minor-bindings major-bindings0))
			  (ext (append minor-bindings major-bindings2))))))))

  (defthm fgl-ev-context-equiv-forall-extensions-var-minor-bindings
    (implies (and (pseudo-term-case x :var)
		  (hons-assoc-equal (pseudo-term-var->name x) minor-bindings))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
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
	      x
	      (append minor-bindings major-bindings)))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions
				      acl2::sub-alistp-hons-assoc-equal))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-if-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
		    (equal x.fn 'if)
		    (fgl-ev-context-equiv-forall-extensions
		     contexts
		     (pseudo-term-fncall 'if
					 (list (car x.args)
					       (cadr x.args)
					       (caddr x.args)))
		     alist))
	       (fgl-ev-context-equiv-forall-extensions contexts x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-return-last-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
		    (equal x.fn 'return-last)
		    (fgl-ev-context-equiv-forall-extensions contexts (caddr x.args) alist))
	       (fgl-ev-context-equiv-forall-extensions contexts x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-disallow-boolean-var-intro-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
		    (equal x.fn 'disallow-boolean-var-intro)
		    (fgl-ev-context-equiv-forall-extensions contexts (car x.args) alist))
	       (fgl-ev-context-equiv-forall-extensions contexts x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-handle-error-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
		    (equal x.fn 'handle-error-fn)
		    (fgl-ev-context-equiv-forall-extensions contexts (cadr x.args) alist))
	       (fgl-ev-context-equiv-forall-extensions contexts x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-fgl-hide-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
		    (equal x.fn 'fgl-hide)
		    (fgl-ev-context-equiv-forall-extensions contexts (car x.args) alist))
	       (fgl-ev-context-equiv-forall-extensions contexts x alist)))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-trigger-constraints-term
    (b* (((pseudo-term-fncall x)))
      (implies (and (pseudo-term-case x :fncall)
		    (equal x.fn 'trigger-constraints))
	       (fgl-ev-context-equiv-forall-extensions contexts x alist)))
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

  (defthm fgl-ev-equiv-of-syntax-interp-call
    (implies (member (pseudo-fnsym-fix fn) '(syntax-interp-fn fgl-interp-obj))
	     (fgl-ev-equiv (pseudo-term-fncall fn args)
			   nil))
    :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

  (defthm fgl-ev-equiv-of-narrow-equiv-call
    (implies (member (pseudo-fnsym-fix fn) '(assume-fn narrow-equiv fgl-time-fn))
	     (fgl-ev-equiv (pseudo-term-fncall fn args)
			   (second args)))
    :hints(("Goal" :in-theory (enable fgl-ev-equiv))))

  (defthm fgl-ev-context-equiv-forall-extensions-when-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
	     (fgl-ev-context-equiv-forall-extensions contexts term eval-alist))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions))))

  (fty::deffixcong cmr::equiv-contexts-equiv equal (fgl-ev-context-equiv-forall-extensions contexts term eval-alist)
    contexts
    :hints (("goal" :cases
	     ((fgl-ev-context-equiv-forall-extensions contexts term eval-alist))
	     :use ((:instance
		    fgl-ev-context-equiv-forall-extensions-necc
		    (contexts contexts)
		    (ext (fgl-ev-context-equiv-forall-extensions-witness
			  (equiv-contexts-fix contexts)
			  term
			  eval-alist)))
		   (:instance
		    fgl-ev-context-equiv-forall-extensions-necc
		    (contexts (equiv-contexts-fix contexts))
		    (ext (fgl-ev-context-equiv-forall-extensions-witness contexts term eval-alist))))
	     :in-theory (e/d (fgl-ev-context-equiv-forall-extensions)
			     (fgl-ev-context-equiv-forall-extensions-necc)))))

  (defthm fgl-ev-context-equiv-forall-extensions-when-coarsening
    (implies (and (equiv-contexts-coarsening-p contexts contexts2)
		  (fgl-ev-context-equiv-forall-extensions contexts2 term eval-alist))
	     (fgl-ev-context-equiv-forall-extensions contexts term eval-alist))
    :hints (("goal" :expand ((fgl-ev-context-equiv-forall-extensions contexts term eval-alist))
	     :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)
	     :use ((:instance
		    fgl-ev-context-equiv-forall-extensions-necc
		    (contexts contexts2)
		    (ext (fgl-ev-context-equiv-forall-extensions-witness contexts term eval-alist)))))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-pseudo-term-fix
    (equal (fgl-ev-context-equiv-forall-extensions context (pseudo-term-fix x) alist)
	   (fgl-ev-context-equiv-forall-extensions context x alist))))


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


(defsection fgl-ev-context-equiv-when-equiv-rel

  (defthmd fgl-ev-context-equiv-of-equiv-rel
    (implies (and (fgl-ev-theoremp (cmr::equiv-rel-term equiv))
		  (pseudo-fnsym-p equiv)
		  (fgl-ev-context-equiv (list equiv) x y))
	     (fgl-ev (list equiv (pseudo-term-quote x) (pseudo-term-quote y)) nil))
    :hints(("Goal" :in-theory (e/d (;; fgl-ev-of-fncall-args
				    fgl-ev-context-equiv-of-singleton)
				   (fgl-ev-context-equiv-is-equal-of-fixes))))))


(defthm member-equiv-contexts-implies-not-quote
  (implies (member-equal x (equiv-contexts-fix contexts))
	   (not (equal x 'quote)))
  :hints(("Goal" :in-theory (enable equiv-contexts-fix)))
  :rule-classes :forward-chaining)


(defsection fgl-ev-context-fix-equal-by-eval

  (local (in-theory (enable fgl-ev-context-equiv-is-equal-of-fixes)))

  (local (defthm pseudo-fnsym-p-when-equiv-context-p
	   (implies (and (symbolp x)
			 (not (equal x 'quote)))
		    (pseudo-fnsym-p x))
	   :hints(("Goal" :in-theory (enable pseudo-fnsym-p)))))

  (local (defthm fgl-ev-context-equiv-by-eval
	   (implies (and (fgl-ev (list fn (pseudo-term-quote x) (pseudo-term-quote y))
				 nil)
			 (member-equal fn (equiv-contexts-fix contexts))
			 (symbolp fn))
		    (fgl-ev-context-equiv contexts x y))
	   :hints(("Goal" :in-theory (e/d (fgl-ev-context-equiv-when-singleton)
					  (fgl-ev-context-equiv-is-equal-of-fixes))
		   :use ((:instance fgl-ev-context-equiv-by-singleton
			  (equiv fn) (ctx contexts)))))))

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
    :hints(("Goal" :in-theory (e/d (fgl-interp-equiv-refinementp
				    fgl-ev-context-fix-equal-by-eval)
				   (cmr::pseudo-fnsym-p-when-member-equal-of-equiv-contextsp))))))


(local (acl2::use-trivial-ancestors-check))


(local (in-theory (disable acl2::rewrite-rule-term)))


(defthmd eval-alist-extension-p-transitive-append-3
  (implies (and (eval-alist-extension-p a (append c b))
                (eval-alist-extension-p b d))
	   (eval-alist-extension-p a (append c d)))
  :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-1))))


(defthm eval-under-iff-when-boolean-fix
  (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
    (implies (and ok
		  (fgl-object-case boolfix :g-concrete))
	     (iff (fgl-object-eval testobj env)
		  (g-concrete->val boolfix))))
  :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-fix fgl-object-eval))))


(local (in-theory (e/d (iff-forall-extensions-necc)
                       (iff-forall-extensions))))

(defsection iff-forall-extensions


  (local (defthm fgl-ev-of-equal-lemma
	   (implies (equal (pseudo-fnsym-fix fn) 'equal)
		    (equal (fgl-ev (list fn x y) a)
			   (equal (fgl-ev x a) (fgl-ev y a))))
	   :hints(("Goal" :in-theory (enable pseudo-fnsym-fix)))))

  (local (in-theory (enable fgl-ev-context-fix-equal-by-eval)))

  (defthm iff-forall-extensions-of-conjoin
    (implies (and (Consp hyps)
		  (iff-forall-extensions (car hyps) (append minor major1))
		  (iff-forall-extensions (conjoin (cdr hyps)) (append minor major2))
		  (eval-alist-extension-p major2 major1))
	     (iff-forall-extensions (conjoin hyps) (append minor major2)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
				       fgl-ev-conjoin-when-consp))
	    (acl2::witness :ruleset iff-forall)))

  (defthm iff-forall-extensions-of-quote
    (implies (pseudo-term-case x :quote)
	     (iff-forall-extensions x eval-alist))
    :hints (("goal" :in-theory (enable iff-forall-extensions))))

  (local (in-theory (enable conjoin-of-atom)))

  (defthm iff-forall-extensions-relieve-hyp-synp
    (implies (mv-nth 0 (fgl-interp-match-synp hyp))
	     (iff-forall-extensions hyp eval-alist))
    :hints(("Goal" :in-theory (enable iff-forall-extensions))))

  (defthm fgl-ev-test-when-concrete-boolean-fix
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and (fgl-ev-context-equiv-forall-extensions
		     (fgl-interp-test-equiv-contexts contexts)
		     test eval-alist)
		    (equal (fgl-ev-context-fix (fgl-interp-test-equiv-contexts contexts)
					       (fgl-object-eval testobj env logicman))
			   (fgl-ev-context-fix (fgl-interp-test-equiv-contexts contexts)
					       (fgl-ev test eval-alist)))
		    ok (fgl-object-case boolfix :g-concrete)
		    (case-split (not (member-eq 'unequiv (equiv-contexts-fix contexts))))
		    (eval-alist-extension-p ext eval-alist))
	       (iff (fgl-ev test ext) (g-concrete->val boolfix))))
    :hints (("Goal" :in-theory (enable fgl-interp-test-equiv-contexts
				       iff-forall-extensions-necc))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-if-nonbranching-true
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
		    (fgl-object-case boolfix :g-concrete)
		    (g-concrete->val boolfix)
		    (fgl-ev-context-equiv-forall-extensions
		     (fgl-interp-test-equiv-contexts contexts)
		     test
		     (append minor-bindings major-bindings1))
		    (equal
		     (fgl-ev-context-fix
		      (fgl-interp-test-equiv-contexts contexts)
		      (fgl-object-eval testobj env))
		     (fgl-ev-context-fix
		      (fgl-interp-test-equiv-contexts contexts)
		      (fgl-ev test (append minor-bindings major-bindings1))))
		    (fgl-ev-context-equiv-forall-extensions
		     contexts
		     then
		     (append minor-bindings major-bindings2))
		    (eval-alist-extension-p major-bindings2 major-bindings1))
	       (fgl-ev-context-equiv-forall-extensions
		contexts
		(pseudo-term-fncall 'if (list test then else))
		(append minor-bindings major-bindings2))))
    :hints (("Goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
				       fgl-interp-test-equiv-contexts))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-if-nonbranching-false
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
		    (fgl-object-case boolfix :g-concrete)
		    (not (g-concrete->val boolfix))
		    (fgl-ev-context-equiv-forall-extensions
		     (fgl-interp-test-equiv-contexts contexts)
		     test
		     (append minor-bindings major-bindings1))
		    (equal
		     (fgl-ev-context-fix
		      (fgl-interp-test-equiv-contexts contexts)
		      (fgl-object-eval testobj env))
		     (fgl-ev-context-fix
		      (fgl-interp-test-equiv-contexts contexts)
		      (fgl-ev test (append minor-bindings major-bindings1))))
		    (fgl-ev-context-equiv-forall-extensions
		     contexts
		     else
		     (append minor-bindings major-bindings2))
		    (eval-alist-extension-p major-bindings2 major-bindings1))
	       (fgl-ev-context-equiv-forall-extensions
		contexts
		(pseudo-term-fncall 'if (list test then else))
		(append minor-bindings major-bindings2))))
    :hints (("Goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
				       fgl-interp-test-equiv-contexts))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm fgl-ev-or-test-of-extension
    (implies (and (fgl-ev-context-equiv-forall-extensions
		   (fgl-interp-or-test-equiv-contexts contexts) term eval-alist)
		  (equal (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts)
					     (fgl-object-eval obj env logicman))
			 (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts)
					     (fgl-ev term eval-alist)))
		  (case-split (not (member-eq 'unequiv (equiv-contexts-fix contexts))))
		  (eval-alist-extension-p ext eval-alist))
	     (iff (fgl-ev term ext) (fgl-object-eval obj env logicman)))
    :hints (("Goal" :in-theory (enable fgl-interp-or-test-equiv-contexts
				       iff-forall-extensions-necc
				       fgl-ev-of-extension-when-equal-forall-extensions))))

  (defthm fgl-ev-context-fix-of-or-test-of-extension
    (implies (and (fgl-ev-context-equiv-forall-extensions
		   (fgl-interp-or-test-equiv-contexts contexts) term eval-alist)
		  (equal (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts)
					     (fgl-object-eval obj env logicman))
			 (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts)
					     (fgl-ev term eval-alist)))
		  (case-split (not (member-eq 'unequiv (equiv-contexts-fix contexts))))
		  (eval-alist-extension-p ext eval-alist))
	     (equal (fgl-ev-context-fix contexts (fgl-ev term ext))
		    (fgl-ev-context-fix contexts (fgl-object-eval obj env logicman))))
    :hints (("Goal"
	     :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
		    (contexts (fgl-interp-or-test-equiv-contexts contexts)))
		   (:instance iff-forall-extensions-necc))
	     :in-theory (e/d (iff* fgl-interp-or-test-equiv-contexts
				   fgl-ev-of-extension-when-equal-forall-extensions)
			     (iff-forall-extensions-necc)))))

  (defthm fgl-ev-or-test-when-concrete-boolean-fix
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and (fgl-ev-context-equiv-forall-extensions
		     (fgl-interp-or-test-equiv-contexts contexts)
		     test eval-alist)
		    (equal (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts)
					       (fgl-object-eval testobj env logicman))
			   (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts)
					       (fgl-ev test eval-alist)))
		    ok (fgl-object-case boolfix :g-concrete)
		    (case-split (not (member-eq 'unequiv (equiv-contexts-fix contexts))))
		    (eval-alist-extension-p ext eval-alist))
	       (iff (fgl-ev test ext) (g-concrete->val boolfix))))
    :hints (("Goal" :in-theory (enable fgl-interp-or-test-equiv-contexts
				       iff-forall-extensions-necc
				       fgl-ev-of-extension-when-equal-forall-extensions))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-or-nonbranching-true
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
		    (fgl-object-case boolfix :g-concrete)
		    (g-concrete->val boolfix)
		    (fgl-ev-context-equiv-forall-extensions
		     (fgl-interp-or-test-equiv-contexts contexts)
		     test
		     bindings)
		    (equal
		     (fgl-ev-context-fix
		      (fgl-interp-or-test-equiv-contexts contexts)
		      (fgl-object-eval testobj env))
		     (fgl-ev-context-fix (fgl-interp-or-test-equiv-contexts contexts) (fgl-ev test bindings))))
	       (fgl-ev-context-equiv-forall-extensions
		contexts
		(pseudo-term-fncall 'if (list test test else))
		bindings)))
    :hints (("goal" :in-theory (enable fgl-interp-or-test-equiv-contexts))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm fgl-ev-context-equiv-forall-extensions-of-or-nonbranching-false
    (b* (((mv ok boolfix) (gobj-syntactic-boolean-fix testobj)))
      (implies (and ok
		    (fgl-object-case boolfix :g-concrete)
		    (not (g-concrete->val boolfix))
		    (fgl-ev-context-equiv-forall-extensions
		     (fgl-interp-or-test-equiv-contexts contexts)
		     test
		     (append minor-bindings major-bindings1))
		    (equal
		     (fgl-ev-context-fix
		      (fgl-interp-or-test-equiv-contexts contexts)
		      (fgl-object-eval testobj env))
		     (fgl-ev-context-fix
		      (fgl-interp-or-test-equiv-contexts contexts)
		      (fgl-ev test (append minor-bindings major-bindings1))))
		    (fgl-ev-context-equiv-forall-extensions
		     contexts
		     else
		     (append minor-bindings major-bindings2))
		    (eval-alist-extension-p major-bindings2 major-bindings1))
	       (fgl-ev-context-equiv-forall-extensions
		contexts
		(pseudo-term-fncall 'if (list test then else))
		(append minor-bindings major-bindings2))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
				       fgl-interp-or-test-equiv-contexts))
	    (acl2::witness :ruleset context-equiv-forall)))

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

  (local
   (defthmd fgl-ev-of-equiv-binding-hyp-of-extension
     (implies (and (fgl-ev-iff-equiv hyp (list equiv (pseudo-term-var var) term))
		   (pseudo-fnsym-p equiv)
		   (pseudo-var-p var)
		   (fgl-ev-theoremp (cmr::equiv-rel-term equiv))
		   (fgl-ev-context-equiv-forall-extensions
		    (equiv-contexts-from-equiv equiv)
		    term
		    (append minor major))
		   (equal
		    (fgl-ev-context-fix (equiv-contexts-from-equiv equiv) obj)
		    (fgl-ev-context-fix (equiv-contexts-from-equiv equiv) (fgl-ev term (append minor major))))
		   (not (hons-assoc-equal var minor))
		   (not (hons-assoc-equal var major))
		   (eval-alist-extension-p ext (append minor (cons (cons var obj) major))))
	      (fgl-ev hyp ext))
     :hints (("Goal" :use ((:instance fgl-ev-iff-equiv-necc
			    (x hyp) (y (list equiv (pseudo-term-var var) term))
			    (env ext)))
	      :in-theory (enable eval-alist-extension-p-transitive-append-3
				 fgl-ev-of-fncall-args
				 hons-assoc-equal-when-sub-alistp
				 fgl-ev-context-equiv-of-equiv-rel-equiv-contexts-from-equiv))
	     (acl2::witness :ruleset context-equiv-forall))))

  (defthm fgl-ev-of-check-equivbind-hyp
    (b* (((mv var term equiv) (check-equivbind-hyp hyp interp-st state)))
      (implies (and var
		    (fgl-ev-meta-extract-global-facts :state st)
		    (equal (w st) (w state))
		    (fgl-ev-context-equiv-forall-extensions
		     (equiv-contexts-from-equiv equiv)
		     term
		     (append minor major))
		    (equal
		     (fgl-ev-context-fix (equiv-contexts-from-equiv equiv) obj)
		     (fgl-ev-context-fix (equiv-contexts-from-equiv equiv) (fgl-ev term (append minor major))))
		    (not (hons-assoc-equal var minor))
		    (not (hons-assoc-equal var major)))
	       (iff (fgl-ev hyp (append minor (cons (cons var obj) major))) t)))
    :hints (("Goal" :use ((:instance fgl-ev-of-equiv-binding-hyp-of-extension
			   (var (mv-nth 0 (check-equivbind-hyp hyp interp-st state)))
			   (term (mv-nth 1 (check-equivbind-hyp hyp interp-st state)))
			   (equiv (mv-nth 2 (check-equivbind-hyp hyp interp-st state)))
			   (ext (append minor (cons (cons (mv-nth 0 (check-equivbind-hyp hyp interp-st state)) obj) major)))))
	     :in-theory (enable fgl-ev-theoremp))))

  (defthm iff-forall-extensions-of-check-equivbind-hyp
    (b* (((mv var term equiv) (check-equivbind-hyp hyp interp-st state)))
      (implies (and var
		    (fgl-ev-meta-extract-global-facts :state st)
		    (equal (w st) (w state))
		    (fgl-ev-context-equiv-forall-extensions
		     (equiv-contexts-from-equiv equiv)
		     term
		     (append minor major))
		    (equal
		     (fgl-ev-context-fix (equiv-contexts-from-equiv equiv) obj)
		     (fgl-ev-context-fix (equiv-contexts-from-equiv equiv) (fgl-ev term (append minor major))))
		    (not (hons-assoc-equal var minor))
		    (not (hons-assoc-equal var major)))
	       (iff-forall-extensions hyp (append minor (cons (cons var obj) major)))))
    :hints (("Goal" :expand ((:free (alist) (iff-forall-extensions hyp alist)))
	     :use ((:instance fgl-ev-of-equiv-binding-hyp-of-extension
		    (var (mv-nth 0 (check-equivbind-hyp hyp interp-st state)))
		    (term (mv-nth 1 (check-equivbind-hyp hyp interp-st state)))
		    (equiv (mv-nth 2 (check-equivbind-hyp hyp interp-st state)))
		    (ext (iff-forall-extensions-witness
			  hyp (append minor (cons (cons (mv-nth 0 (check-equivbind-hyp hyp interp-st state)) obj) major))))))
	     :in-theory (enable fgl-ev-theoremp))))

  (defthm iff-forall-extensions-of-pseudo-term-fix
    (equal (iff-forall-extensions (pseudo-term-fix x) alist)
	   (iff-forall-extensions x alist))))


(defsection-progn fgl-rewrite-match-assums-correctness

  ;; Successful assumption matching establishes both extension stability and
  ;; the truth value of the matched hypothesis.  These operational correctness
  ;; results supply both facts to callers.
  (defret iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums-index
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-db-ok interp-st env)
		  (< (nfix idx) (bfr-nvars (interp-st->logicman interp-st)))
		  (<= (base-bvar (interp-st->bvar-db interp-st)) (nfix idx))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  successp)
	     (and
	      (iff-forall-extensions
	       hyp
	       (fgl-object-bindings-eval
		(stack$a-bindings
		 (interp-st->stack new-interp-st))
		env (interp-st->logicman interp-st)))
	      (iff
	       (fgl-ev
		hyp
		(fgl-object-bindings-eval
		 (stack$a-bindings
		  (interp-st->stack new-interp-st))
		 env (interp-st->logicman interp-st)))
	       (not negatedp))))
    :hints(("Goal" :in-theory (e/d (<fn> gobj-bfr-eval
					 FGL-EV-OF-EXTENSION-WHEN-TERM-VARS-BOUND
					 iff-forall-extensions
					 stack$a-bindings
					 stack$a-set-bindings)
				   (interp-st-pathcond-assume-not-contradictionp
				    interp-st-bvar-db-ok-necc
				    fgl-unify-term/gobj-correct))
	    :use ((:instance interp-st-pathcond-assume-not-contradictionp
		   (test (BFR-NOT (BFR-VAR IDX (INTERP-ST->LOGICMAN INTERP-ST))
				  (INTERP-ST->LOGICMAN INTERP-ST)))
		   (env (fgl-env->bfr-vals env)))
		  (:instance interp-st-pathcond-assume-not-contradictionp
		   (test (BFR-VAR IDX (INTERP-ST->LOGICMAN INTERP-ST)))
		   (env (fgl-env->bfr-vals env)))
		  (:instance interp-st-bvar-db-ok-necc
		   (n idx))
		  (:instance fgl-unify-term/gobj-correct
		   (pat hyp)
		   (x (get-bvar->term$c idx (interp-st->bvar-db interp-st)))
		   (alist (stack$a-bindings (interp-st->stack interp-st)))
		   (logicman (interp-st->logicman interp-st))
		   (bfrstate (logicman->bfrstate (interp-st->logicman interp-st)))))))
    :fn fgl-rewrite-relieve-hyp-match-assums-index)

  (defret iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums-indices
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-db-ok interp-st env)
		  (interp-st-bvar-list-okp indices interp-st)
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  successp)
	     (and
	      (iff-forall-extensions
	       hyp
	       (fgl-object-bindings-eval
		(stack$a-bindings
		 (interp-st->stack new-interp-st))
		env (interp-st->logicman interp-st)))
	      (iff
	       (fgl-ev
		hyp
		(fgl-object-bindings-eval
		 (stack$a-bindings
		  (interp-st->stack new-interp-st))
		 env (interp-st->logicman interp-st)))
	       (not negatedp))))
    :hints(("Goal" :in-theory (enable <fn>
				      interp-st-bvar-list-okp
				      bvar-list-okp$c
				      bfr-varname-p)))
    :fn fgl-rewrite-relieve-hyp-match-assums-indices)

  (defret iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums1
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-db-ok interp-st env)
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  successp)
	     (and
	      (iff-forall-extensions
	       hyp
	       (fgl-object-bindings-eval
		(stack$a-bindings
		 (interp-st->stack new-interp-st))
		env (interp-st->logicman interp-st)))
	      (iff
	       (fgl-ev
		hyp
		(fgl-object-bindings-eval
		 (stack$a-bindings
		  (interp-st->stack new-interp-st))
		 env (interp-st->logicman interp-st)))
	       (not negatedp))))
    :hints(("Goal" :in-theory (enable <fn>
				      interp-st-bvar-list-okp
				      interp-st-bvar-fn-term-indices
				      bvar-list-okp$c
				      bfr-varname-p)))
    :fn fgl-rewrite-relieve-hyp-match-assums1)

  (defthmd iff-forall-extensions-of-negated
    (implies (pseudo-term-case hyp
	       :fncall (and (eq hyp.fn 'not) (eql (len hyp.args) 1))
	       :otherwise nil)
	     (iff (iff-forall-extensions (car (pseudo-term-call->args hyp)) subst)
		  (iff-forall-extensions hyp subst)))
    :hints (("Goal" :in-theory (enable iff*))
	    (acl2::witness :ruleset iff-forall)))

  (defret iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums0
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-db-ok interp-st env)
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  successp)
	     (and
	      (iff-forall-extensions
	       hyp
	       (fgl-object-bindings-eval
		(stack$a-bindings
		 (interp-st->stack new-interp-st))
		env (interp-st->logicman interp-st)))
	      (iff
	       (fgl-ev
		hyp
		(fgl-object-bindings-eval
		 (stack$a-bindings
		  (interp-st->stack new-interp-st))
		 env (interp-st->logicman interp-st)))
	       t)))
    :hints(("Goal" :in-theory (e/d (<fn>
				    interp-st-bvar-list-okp
				    interp-st-bvar-fn-term-indices
				    bvar-list-okp$c
				    bfr-varname-p
				    iff-forall-extensions-of-negated)
				   (iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums1 len open-len-is equal-len-hyp))
	    :use ((:instance iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums1
		   (negatedp (pseudo-term-case hyp
			       :fncall (and (eq hyp.fn 'not) (eql (len hyp.args) 1))
			       :otherwise nil))
		   (hyp (pseudo-term-case hyp
			  :fncall (if (and (eq hyp.fn 'not) (eql (len hyp.args) 1)) (car hyp.args) hyp)
			  :otherwise hyp))))))
    :fn fgl-rewrite-relieve-hyp-match-assums0)

  (defthm iff-forall-extensions-of-match-assums
    (implies (and (pseudo-term-case x :fncall)
		  (equal (pseudo-term-fncall->fn x) 'match-assums))
	     (iff (iff-forall-extensions x eval-alist)
		  (iff-forall-extensions
		   (car (pseudo-term-call->args x)) eval-alist)))
    :hints (("Goal" :in-theory (enable iff*))
	    (acl2::witness :ruleset iff-forall)))

  (defret iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums
    (implies (and (interp-st-bfrs-ok interp-st)
		  (interp-st-bvar-db-ok interp-st env)
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (logicman-pathcond-eval (fgl-env->bfr-vals env) (interp-st->constraint interp-st)
					  (interp-st->logicman interp-st))
		  successp
		  (equal minor (fgl-object-bindings-eval
				(stack$a-minor-bindings
				 (interp-st->stack interp-st))
				env (interp-st->logicman interp-st)))
		  (equal logicman (interp-st->logicman interp-st)))
	     (and
	      (iff-forall-extensions
	       hyp
	       (append minor
		       (fgl-object-bindings-eval
			(stack$a-bindings
			 (interp-st->stack new-interp-st))
			env logicman)))
	      (iff
	       (fgl-ev
		hyp
		(append minor
			(fgl-object-bindings-eval
			 (stack$a-bindings
			  (interp-st->stack new-interp-st))
			 env logicman)))
	       t)))
    :hints(("Goal" :in-theory (e/d (<fn>)
				   (iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums0))
	    :use ((:instance iff-forall-extensions-fgl-rewrite-relieve-hyp-match-assums0
		   (hyp (car (acl2::pseudo-term-fncall->args hyp)))))
	    :expand ((fgl-object-bindings-eval nil env (interp-st->logicman interp-st)))))
    :fn fgl-rewrite-relieve-hyp-match-assums))


(define iff?-forall-extensions ((contexts equiv-contextsp)
                                term eval-alist)
  :verify-guards nil
  (if (member-eq 'unequiv (equiv-contexts-fix contexts))
      t
    (iff-forall-extensions term eval-alist))
  ///
  (local (defthm iff-forall-extensions-when-extension
	   (implies (and (iff-forall-extensions term (append minor major0))
			 (eval-alist-extension-p major1 major0))
		    (iff-forall-extensions term (append minor major1)))
	   :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
		   (acl2::witness :ruleset iff-forall))))

  (defthmd iff?-forall-extensions-necc
    (implies (and (iff?-forall-extensions contexts term eval-alist)
		  (syntaxp (not (equal ext eval-alist)))
		  (case-split (not (member-eq 'unequiv (equiv-contexts-fix contexts))))
		  (eval-alist-extension-p ext eval-alist))
	     (iff (fgl-ev term ext) (fgl-ev term eval-alist)))
    :hints (("Goal" :in-theory (enable iff?-forall-extensions iff-forall-extensions-necc))))

  (defthm iff?-forall-extensions-of-test-contexts
    (implies (and (fgl-ev-context-equiv-forall-extensions
		   (fgl-interp-test-equiv-contexts contexts)
		   x (append minor-bindings major-bindings1))
		  (eval-alist-extension-p major-bindings2 major-bindings1))
	     (iff?-forall-extensions contexts x (append minor-bindings major-bindings2)))
    :hints (("Goal" :in-theory (enable iff?-forall-extensions
				       fgl-interp-test-equiv-contexts
				       eval-alist-extension-p-transitive-append-2))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-iff
    (equal (iff?-forall-extensions '(iff) term eval-alist)
	   (iff-forall-extensions term eval-alist)))

  (defthm iff?-forall-extensions-of-if
    (implies (and (iff?-forall-extensions contexts test (append minor-bindings major-bindings1))
		  (fgl-ev-context-equiv-forall-extensions
		   contexts
		   then
		   (append minor-bindings major-bindings2))
		  (fgl-ev-context-equiv-forall-extensions
		   contexts
		   else
		   (append minor-bindings major-bindings3))
		  (eval-alist-extension-p major-bindings2 major-bindings1)
		  (eval-alist-extension-p major-bindings3 major-bindings2)
		  (eval-alist-extension-p major-bindings4 major-bindings3))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
	      (pseudo-term-fncall 'if (list test then else))
	      (append minor-bindings major-bindings4)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-if-false
    (implies (and (iff?-forall-extensions contexts test (append minor-bindings major-bindings1))
		  (implies
		   (not (member-eq 'unequiv (equiv-contexts-fix contexts)))
		   (iff (fgl-ev test (append minor-bindings major-bindings1)) nil))
		  (fgl-ev-context-equiv-forall-extensions
		   contexts
		   else
		   (append minor-bindings major-bindings3))
		  (eval-alist-extension-p major-bindings3 major-bindings1))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
	      (pseudo-term-fncall 'if (list test then else))
	      (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-if-true
    (implies (and (iff?-forall-extensions contexts test (append minor-bindings major-bindings1))
		  (implies
		   (not (member-eq 'unequiv (equiv-contexts-fix contexts)))
		   (iff (fgl-ev test (append minor-bindings major-bindings1)) t))
		  (fgl-ev-context-equiv-forall-extensions
		   contexts
		   then
		   (append minor-bindings major-bindings2))
		  (eval-alist-extension-p major-bindings2 major-bindings1)
		  (eval-alist-extension-p major-bindings3 major-bindings2))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
	      (pseudo-term-fncall 'if (list test then else))
	      (append minor-bindings major-bindings3)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-implies-fgl-ev-context-equiv-forall-extensions
    (implies (and (iff?-forall-extensions contexts x eval-alist)
		  (member 'iff (equiv-contexts-fix contexts)))
	     (fgl-ev-context-equiv-forall-extensions contexts x eval-alist))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm iff?-forall-extensions-of-pseudo-term-fix
    (equal (iff?-forall-extensions contexts (pseudo-term-fix x) alist)
	   (iff?-forall-extensions contexts x alist)))

  (defthm iff?-forall-extensions-of-eval
    (implies (and (iff?-forall-extensions contexts x env1)
		  (eval-alist-extension-p env2 env1))
	     (iff?-forall-extensions contexts x env2))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-2))
	    (acl2::witness :ruleset context-equiv-forall))))


(defsection equal-list-forall-extensions
  (defun-sk equal-list-forall-extensions (terms eval-alist)
    (forall (ext)
	    (implies (and (syntaxp (not (equal ext eval-alist)))
			  (eval-alist-extension-p ext eval-alist))
		     (equal (fgl-ev-list terms ext)
			    (fgl-ev-list terms eval-alist))))
    :rewrite :direct)

  (acl2::defquantexpr equal-list-forall-extensions
    :predicate (equal-list-forall-extensions terms eval-alist)
    :quantifier :forall
    :witnesses ((ext (equal-list-forall-extensions-witness terms eval-alist)))
    :expr (implies (and (syntaxp (not (equal ext eval-alist)))
			(eval-alist-extension-p ext eval-alist))
		   (equal (fgl-ev-list terms ext)
			  (fgl-ev-list terms eval-alist)))
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
		    (equal-list-forall-extensions x.args (append minor major1))
		    (eval-alist-extension-p major2 major1))
	       (fgl-ev-context-equiv-forall-extensions contexts x (append minor major2))))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2
				       fgl-ev-of-fncall-args))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm equal-list-forall-extensions-of-args
    (implies (and (consp args)
		  (fgl-ev-context-equiv-forall-extensions nil (car args) (append minor major0))
		  (equal-list-forall-extensions (cdr args) (append minor major1))
		  (eval-alist-extension-p major1 major0)
		  (eval-alist-extension-p major2 major1))
	     (equal-list-forall-extensions args (append minor major2)))
    :hints (("goal" :in-theory (enable eval-alist-extension-p-transitive-append-2))
	    (acl2::witness :ruleset context-equiv-forall)))

  (defthm equal-list-forall-extensions-of-empty-args
    (implies (not (consp args))
	     (equal-list-forall-extensions args alist))
    :hints(("Goal" :in-theory (enable equal-list-forall-extensions)))))


(define equal?-list-forall-extensions ((contexts equiv-contextsp)
                                       terms eval-alist)
  :verify-guards nil
  (if (equal (equiv-contexts-fix contexts) nil)
      (equal-list-forall-extensions terms eval-alist)
    t)
  ///

  ;; (local (in-theory (disable equiv-contexts-fix-under-iff)))

  (local (defthm not-equiv-contexts-fix
	   (implies (not (consp x))
		    (cmr::equiv-contexts-equiv x nil))
	   :rule-classes :forward-chaining))

  (defthm equal?-list-forall-extensions-of-args
    (implies (and (consp args)
		  (fgl-ev-context-equiv-forall-extensions contexts (car args) (append minor major0))
		  (equal?-list-forall-extensions contexts (cdr args) (append minor major1))
		  (eval-alist-extension-p major1 major0)
		  (eval-alist-extension-p major2 major1))
	     (equal?-list-forall-extensions contexts args (append minor major2))))

  (defthm equal?-list-forall-extensions-of-empty-args
    (implies (not (consp args))
	     (equal?-list-forall-extensions contexts args alist)))

  (local (defthm sub-alistp-append-when-sub-alistp-append-with-cons
	   (implies (and (not (acl2::sub-alistp (append minor major) ext))
			 (not (hons-assoc-equal var major)))
		    (not (acl2::sub-alistp (append minor (cons (cons var val) major)) ext)))
	   :hints(("Goal" :in-theory (enable sub-alistp-by-witness))))))


(defsection equal-subst-forall-extensions
  (defun-sk equal-subst-forall-extensions (subst alist)
    (forall (ext)
	    (implies (and (syntaxp (not (equal ext alist)))
			  (eval-alist-extension-p ext alist))
		     (equal (fgl-ev-alist subst ext)
			    (fgl-ev-alist subst alist))))
    :rewrite :direct)

  (in-theory (Disable equal-subst-forall-extensions))

  (defthm equal-subst-forall-extensions-of-cons
    (implies (and (equal-subst-forall-extensions (cdr subst) al1)
		  (fgl-ev-context-equiv-forall-extensions nil (cdar subst) al2)
		  (eval-alist-extension-p al al1)
		  (eval-alist-extension-p al al2)
		  (consp subst)
		  (consp (car subst))
		  (pseudo-var-p (caar subst)))
	     (equal-subst-forall-extensions subst al))
    :hints (("goal" :expand ((equal-subst-forall-extensions subst al)
			     (:free (w) (fgl-ev-alist subst w)))
	     :use ((:instance
		    fgl-ev-context-equiv-forall-extensions-necc
		    (contexts nil)
		    (term (cdar subst))
		    (eval-alist al2)
		    (ext (equal-subst-forall-extensions-witness subst al)))
		   (:instance fgl-ev-context-equiv-forall-extensions-necc
		    (contexts nil) (term (cdar subst)) (eval-alist al2) (ext al)))
	     :in-theory (e/d (eval-alist-extension-p-transitive-2)
			     ()))))
  (defthm equal-subst-forall-extensions-of-bad-pair
    (implies (and (consp subst)
		  (or (not (consp (car subst)))
		      (not (pseudo-var-p (caar subst))))
		  (equal-subst-forall-extensions (cdr subst) al1)
		  (eval-alist-extension-p al al1))
	     (equal-subst-forall-extensions subst al))
    :hints (("goal" :expand ((equal-subst-forall-extensions subst al)
			     (:free (w) (fgl-ev-alist subst w)))
	     :in-theory (e/d (eval-alist-extension-p-transitive-2)))))

  (defthm equal-subst-forall-extensions-of-nil
    (implies (not (consp subst))
	     (equal-subst-forall-extensions subst al))
    :hints (("goal" :expand ((equal-subst-forall-extensions subst al)
			     (:free (w) (fgl-ev-alist subst w)))))))


(defsection equal-bindinglist-forall-extensions
  (defun-sk equal-bindinglist-forall-extensions (bindings minor-alist major-alist)
    (forall (ext)
	    (implies (and (syntaxp (not (equal ext major-alist)))
			  (eval-alist-extension-p ext major-alist))
		     (equal (fgl-ev-bindinglist-minmaj bindings minor-alist ext)
			    (fgl-ev-bindinglist-minmaj bindings minor-alist major-alist))))
    :rewrite :direct)

  (acl2::defquantexpr equal-bindinglist-forall-extensions
    :predicate (equal-bindinglist-forall-extensions bindings minor-alist major-alist)
    :quantifier :forall
    :witnesses ((ext (equal-bindinglist-forall-extensions-witness bindings minor-alist major-alist)))
    :expr (implies (and (syntaxp (not (equal ext major-alist)))
			(eval-alist-extension-p ext major-alist))
		   (equal (fgl-ev-bindinglist-minmaj bindings minor-alist ext)
			  (fgl-ev-bindinglist-minmaj bindings minor-alist major-alist)))
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

  (defthm fgl-ev-of-lambda-with-stable-bindings
    (b* (((mv bindings body) (lambda-nest-to-bindinglist x)))
      (implies (and (pseudo-term-case x :lambda)
		    (equal-bindinglist-forall-extensions bindings minor major1)
		    (eval-alist-extension-p major2 major1)
		    (alistp major1))
	       (equal (fgl-ev x (append minor major2))
		      (fgl-ev body (append (fgl-ev-bindinglist-minmaj bindings minor major1)
					   major2)))))
    :hints (("Goal"
	     :use ((:instance cmr::lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist-minmaj
		    (x x) (cmr::minor minor) (cmr::major major2) (cmr::major1 major2))
		   (:instance equal-bindinglist-forall-extensions-necc
		    (bindings (mv-nth 0 (lambda-nest-to-bindinglist x)))
		    (minor-alist minor) (major-alist major1) (ext major2)))
	     :in-theory (disable cmr::lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist-minmaj
				 fgl-ev-when-pseudo-term-lambda))))

  (defthm fgl-ev-context-equiv-forall-extensions-lambda
    (b* (((mv bindings body) (lambda-nest-to-bindinglist x)))
      (implies (and (pseudo-term-case x :lambda)
		    (equal-bindinglist-forall-extensions bindings minor-bindings major-bindings1)
		    (fgl-ev-context-equiv-forall-extensions
		     contexts
		     body
		     (append (fgl-ev-bindinglist-minmaj bindings minor-bindings major-bindings1) major-bindings2))
		    (eval-alist-extension-p major-bindings2 major-bindings1)
		    (alistp major-bindings1))
	       (fgl-ev-context-equiv-forall-extensions
		contexts
		x
		(append minor-bindings major-bindings2))))
    :hints (("goal" :in-theory (e/d (eval-alist-extension-p-transitive-append-2)
				    (fgl-ev-when-pseudo-term-lambda
				     cmr::lambda-nest-to-bindinglist-correct-for-fgl-ev-bindinglist-minmaj
				     fgl-ev-of-lambda-with-stable-bindings)))
	    (acl2::witness :ruleset fgl-ev-context-equiv-forall-extensions-witnessing)
	    (and stable-under-simplificationp
		 '(:use ((:instance fgl-ev-of-lambda-with-stable-bindings
			  (x x) (minor minor-bindings)
			  (major2 major-bindings2) (major1 major-bindings1))
			 (:instance fgl-ev-of-lambda-with-stable-bindings
			  (x x) (minor minor-bindings)
			  (major2 (append major-bindings2 ext0))
			  (major1 major-bindings1))
			 (:instance
			  equal-bindinglist-forall-extensions-necc
			  (bindings (mv-nth 0 (lambda-nest-to-bindinglist x)))
			  (minor-alist minor-bindings)
			  (major-alist major-bindings1)
			  (ext (append major-bindings2 ext0)))
			 (:instance equal-bindinglist-forall-extensions-necc
			  (bindings (mv-nth 0 (lambda-nest-to-bindinglist x)))
			  (minor-alist minor-bindings)
			  (major-alist major-bindings1)
			  (ext major-bindings2))
			 (:instance
			  fgl-ev-context-equiv-forall-extensions-necc
			  (term (mv-nth 1 (lambda-nest-to-bindinglist x)))
			  (eval-alist (append (fgl-ev-bindinglist-minmaj (mv-nth 0 (lambda-nest-to-bindinglist x)) minor-bindings major-bindings1) major-bindings2))
			  (ext (append (fgl-ev-bindinglist-minmaj (mv-nth 0 (lambda-nest-to-bindinglist x)) minor-bindings major-bindings1) major-bindings2 ext0))))))))

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
    (implies (and
	      (consp bindings)
	      (equal-list-forall-extensions
	       (cmr::binding->args (car bindings))
	       (append minor-bindings-ev major-bindings-ev0))
	      (equal-bindinglist-forall-extensions
	       (cdr bindings)
	       (append (pairlis$ (cmr::binding->formals (car bindings)) (fgl-ev-list (cmr::binding->args (car bindings)) (append minor-bindings-ev major-bindings-ev0))) minor-bindings-ev)
	       major-bindings-ev)
	      (eval-alist-extension-p major-bindings-ev major-bindings-ev0))
	     (equal-bindinglist-forall-extensions bindings minor-bindings-ev major-bindings-ev))
    :hints ((acl2::witness :ruleset equal-bindinglist-forall-extensions-witnessing)
	    (and stable-under-simplificationp
		 '(
		   :use ((:instance
			  equal-bindinglist-forall-extensions-necc
			  (bindings (cdr bindings))
			  (minor-alist
			   (append (pairlis$ (cmr::binding->formals (car bindings)) (fgl-ev-list (cmr::binding->args (car bindings)) (append minor-bindings-ev major-bindings-ev0))) minor-bindings-ev))
			  (major-alist major-bindings-ev)
			  (ext ext0))
			 (:instance
			  equal-list-forall-extensions-necc
			  (terms (cmr::binding->args (car bindings)))
			  (eval-alist (append minor-bindings-ev major-bindings-ev0))
			  (ext (append minor-bindings-ev major-bindings-ev ext0)))
			 (:instance equal-list-forall-extensions-necc
			  (terms (cmr::binding->args (car bindings)))
			  (eval-alist (append minor-bindings-ev major-bindings-ev0))
			  (ext (append minor-bindings-ev major-bindings-ev))))
		   :expand ((:free (maj) (fgl-ev-bindinglist-minmaj bindings minor-bindings-ev maj)))))))

  (defthm equal-bindinglist-forall-extensions-atom-bindings
    (implies (and (not (consp bindings))
		  (alistp minor-bindings))
	     (equal-bindinglist-forall-extensions bindings minor-bindings major-bindings-ev))
    :hints (("goal" :expand ((equal-bindinglist-forall-extensions bindings minor-bindings major-bindings-ev)
			     (:free (maj)
			      (fgl-ev-bindinglist-minmaj
			       bindings minor-bindings
			       maj)))))))


(define equal?-bindinglist-forall-extensions ((contexts equiv-contextsp)
                                              bindings minor-alist major-alist)
  :verify-guards nil
  (if (equal (equiv-contexts-fix contexts) nil)
      (equal-bindinglist-forall-extensions bindings minor-alist major-alist)
    t))


(defsection-progn fgl-interp-bvar-db-evaluation-support

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

  (defthm fgl-object-eval-of-normalize-equal-order
    (equal (fgl-object-eval (normalize-equal-order x) env)
	   (fgl-object-eval x env))
    :hints(("Goal" :in-theory (enable normalize-equal-order
				      fgl-apply)
	    :expand ((fgl-objectlist-eval (g-apply->args x) env)
		     (fgl-objectlist-eval (cdr (g-apply->args x)) env)))))

  (defret interp-st-bvar-db-ok-of-add-term-bvar-implies
    (implies (and (case-split (interp-st-bvar-db-ok new-interp-st env))
		  (equal logicman (interp-st->logicman new-interp-st))
		  (not (interp-st->errmsg new-interp-st)))
	     (iff* (gobj-bfr-eval bfr env logicman)
		   (fgl-object-eval x env logicman)))
    :fn interp-st-add-term-bvar
    :hints(("Goal" :in-theory (enable interp-st-add-term-bvar)
	    :use ((:instance interp-st-bvar-db-ok-necc
		   (interp-st new-interp-st)
		   (n (next-bvar (interp-st->bvar-db interp-st))))))))

  (defret interp-st-bvar-db-ok-of-add-term-bvar-unique-implies
    (implies (and (case-split (interp-st-bvar-db-ok new-interp-st env))
		  (equal logicman  (interp-st->logicman new-interp-st))
		  (not (interp-st->errmsg new-interp-st)))
	     (iff* (gobj-bfr-eval bfr env logicman)
		   (fgl-object-eval x env logicman)))
    :fn interp-st-add-term-bvar-unique
    :hints(("Goal" :in-theory (enable interp-st-add-term-bvar-unique)
	    :use ((:instance interp-st-bvar-db-ok-necc
		   (interp-st new-interp-st)
		   (n (next-bvar (interp-st->bvar-db interp-st))))
		  (:instance interp-st-bvar-db-ok-necc
		   (interp-st new-interp-st)
		   (n (get-term->bvar (normalize-equal-order x) (interp-st->bvar-db interp-st))))))))

  (defthm interp-st-bvar-db-ok-necc-reverse
    (implies (interp-st-bvar-db-ok interp-st env)
	     (b* ((bvar-db (interp-st->bvar-db interp-st))
		  (logicman (interp-st->logicman interp-st)))
	       (implies (and (<= (base-bvar$c bvar-db) (nfix n))
			     (< (nfix n) (next-bvar$c bvar-db)))
			(iff* (gobj-bfr-eval (bfr-var n) env logicman)
			      (fgl-object-eval (get-bvar->term$c n bvar-db) env logicman)))))))


(defthm iff-forall-extensions-of-meta-extract-formula
  (implies (and (fgl-ev-meta-extract-global-facts :state state0)
                (equal (w state) (w state0)))
	   (iff-forall-extensions (meta-extract-formula name state) eval-alist))
  :hints (("Goal" :in-theory (enable iff-forall-extensions))))


(in-theory (disable interp-st-bvar-db-ok-necc))


(defret logicman-pathcond-eval-preserved-by-logicman-pathcond-assume
  (implies (and (logicman-pathcond-eval env pathcond)
                (bfr-eval x env)
                (not contradictionp))
	   (logicman-pathcond-eval env new-pathcond logicman))
  :hints (("goal" :cases ((pathcond-enabledp pathcond))))
  :fn logicman-pathcond-assume)


(local (acl2::use-trivial-ancestors-check))


;; (local (in-theory (disable bfr-listp-when-not-member-witness)))


(defsection check-equiv-replacement-correct
  (local (std::set-define-current-function check-equiv-replacement))
  (local (in-theory (e/d (check-equiv-replacement
                          fgl-ev-context-fix-equal-by-eval
                          fgl-apply
                          fgl-objectlist-eval)
                         (kwote-lst))))
  (defret check-equiv-replacement-correct
    (implies (and ok
		  (fgl-object-eval equiv-term env))
	     (equal (fgl-ev-context-fix contexts (fgl-object-eval equiv env))
		    (fgl-ev-context-fix contexts (fgl-object-eval x env))))))


(defsection try-equivalence-correct
  (local (std::set-define-current-function try-equivalence))
  (local (in-theory (enable try-equivalence)))

  (defthm try-equivalence-of-pathcond-fix
    (equal (try-equivalence x bvars contexts (pathcond-fix pathcond) bvar-db logicman state)
	   (try-equivalence x bvars contexts pathcond bvar-db logicman state)))

  ;; (local (in-theory (e/d (eval-equal-bit-of-logicman-pathcond-implies)
  ;;                        (eval-when-logicman-pathcond-implies))))

  (local (defthm bfr-eval-of-fgl-env->bfr-vars
	   (equal (bfr-eval bfr (fgl-env->bfr-vals env))
		  (gobj-bfr-eval bfr env))
	   :hints(("Goal" :in-theory (enable gobj-bfr-eval)))))

  (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

  ;; (local (in-theory (enable interp-st-bvar-db-ok-necc)))

  (defret try-equivalence-correct
    :pre-bind ((logicman (interp-st->logicman interp-st))
	       (bvar-db (interp-st->bvar-db interp-st))
	       (pathcond (interp-st->pathcond interp-st)))
    (implies (and ok
		  (logicman-pathcond-eval (fgl-env->bfr-vals env)
					  (interp-st->pathcond interp-st)
					  (interp-st->logicman interp-st))
		  (interp-st-bvar-db-ok interp-st env)
		  (interp-st-bfrs-ok interp-st)
		  (<= (base-bvar (interp-st->bvar-db interp-st)) (nfix bvar))
		  (< (nfix bvar) (next-bvar (interp-st->bvar-db interp-st))))
	     (equal (fgl-ev-context-fix
		     contexts
		     (fgl-object-eval new-x env))
		    (fgl-ev-context-fix
		     contexts
		     (fgl-object-eval x env))))
    :hints (("goal" :use ((:instance eval-when-logicman-pathcond-implies
			   (x (bfr-var (nfix bvar) (interp-st->logicman interp-st)))
			   (pathcond (interp-st->pathcond interp-st))
			   (logicman (interp-st->logicman interp-st))
			   (env (fgl-env->bfr-vals env))))
	     :in-theory (e/d (bool->bit)
			     (eval-when-logicman-pathcond-implies))
	     :do-not-induct t))))


(defsection try-equivalences-correct
  (local (std::set-define-current-function try-equivalences))
  (local (in-theory (enable try-equivalences)))

  (defthm try-equivalences-of-pathcond-fix
    (equal (try-equivalences x bvars contexts (pathcond-fix pathcond) bvar-db logicman state)
	   (try-equivalences x bvars contexts pathcond bvar-db logicman state)))

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
	     :in-theory (enable (:i len) bvar-list-okp$c)
	     :expand ((:free (logicman pathcond bvar-db) <call>))))))


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


(defsection fgl-interp-equivalence-replacement-correctness

  (defretd interp-st-try-equivalences-correct
    (b* ((logicman (interp-st->logicman interp-st)))
      (implies (and (not (interp-st->errmsg new-interp-st))
		    (logicman-pathcond-eval (fgl-env->bfr-vals env)
					    (interp-st->pathcond interp-st)
					    (interp-st->logicman interp-st))
		    (interp-st-bvar-db-ok interp-st env)
		    (interp-st-bfrs-ok interp-st))
	       (equal (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval xobj env))
		      (fgl-ev-context-fix
		       (interp-st->equiv-contexts interp-st)
		       (fgl-object-eval x env)))))
    :hints(("Goal" :in-theory (enable <fn>)))
    :fn interp-st-try-equivalences)

  (defret interp-st-try-equivalences-correct-rw
    (implies (and
	      (logicman-pathcond-eval (fgl-env->bfr-vals env)
				      (interp-st->pathcond interp-st)
				      (interp-st->logicman interp-st))
	      (interp-st-bfrs-ok interp-st)
	      (equal contexts (interp-st->equiv-contexts interp-st))
	      (equal logicman (interp-st->logicman interp-st))
	      (case-split (and (interp-st-bvar-db-ok interp-st env)
			       (not (interp-st->errmsg new-interp-st)))))
	     (equal (fgl-ev-context-fix
		     contexts
		     (fgl-object-eval xobj env))
		    (fgl-ev-context-fix
		     contexts
		     (fgl-object-eval x env))))
    :hints(("Goal" :in-theory (enable interp-st-try-equivalences-correct)))
    :fn interp-st-try-equivalences))


(defsection-progn fgl-interp-stack-binding-accessors

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
    :hints(("Goal" :in-theory (enable stack$a-bindings stack$a-set-bindings)))))


(defsection-progn fgl-interp-bindings-evaluation-support

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
				      stack-bindings-extension-p)))))


;; this dumb thing is important for urewrite-clause-proc in combination with my-by-hint-cp


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


(defsection-progn fgl-interp-context-evaluation-support

  (defthm fgl-ev-when-iff-forall-extensions
    (implies (and (iff-forall-extensions (conjoin hyps) al)
		  (iff (fgl-ev (conjoin hyps) al) t)
		  (eval-alist-extension-p al2 al))
	     (fgl-ev (conjoin hyps) al2))
    :hints (("goal" :in-theory (enable iff-forall-extensions-necc))))

  (defthm fgl-ev-context-fix-of-rewrite-rule-rhs
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
		   :in-theory (enable fgl-ev-of-fncall-args)))))





  (defthm fgl-ev-context-equiv-forall-extensions-when-constant
    (implies (or (pseudo-term-case term :null) (pseudo-term-case term :const))
	     (fgl-ev-context-equiv-forall-extensions contexts term eval-alist))
    :hints (("Goal" :in-theory (enable fgl-ev-context-equiv-forall-extensions))))

  (defthm fgl-ev-context-equiv-forall-extensions-of-boolean-fncall
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
		    (x res-obj) (interp-st ist))))))

  (defthm len-of-fgl-ev-list
    (equal (len (fgl-ev-list x env))
	   (len x))
    :hints(("Goal" :in-theory (enable len)))))


(define fgl-arglist-new-bindings ((x fgl-arglist-p)
                                  (bindings fgl-object-bindings-p))
  :returns (newly-bound fgl-object-bindings-p)
  (b* (((when (atom x)) nil)
       (x1 (car x))
       ((when (fgl-arg-case x1 :obj))
        (fgl-arglist-new-bindings (cdr x) bindings))
       (var (fgl-arg-unbound->var x1))
       (look (assoc-eq var (fgl-object-bindings-fix bindings)))
       ((when look)
        (cons look
	      (fgl-arglist-new-bindings (cdr x) bindings))))
    (fgl-arglist-new-bindings (cdr x) bindings))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal var newly-bound)
	   (and (member-equal var (fgl-arglist-unbounds x))
		(hons-assoc-equal var (fgl-object-bindings-fix bindings))))
    :hints(("Goal" :in-theory (enable fgl-arglist-unbounds))))

  (defret eval-alist-extension-p-of-fgl-arglist-new-bindings
    (eval-alist-extension-p (fgl-object-bindings-eval bindings env)
			    (fgl-object-bindings-eval newly-bound env))
    :hints(("Goal" :in-theory (e/d (acl2::sub-alistp-iff-witness)
				   (<fn>)))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys newly-bound)
	   (intersection-equal (fgl-arglist-unbounds x)
			       (alist-keys (fgl-object-bindings-fix bindings))))
    :hints(("Goal" :in-theory (enable fgl-arglist-unbounds
				      intersection-equal)))))


(local (in-theory (enable sub-alistp-of-cons-when-not-shadowing)))


(define fgl-ev-arglist-contexts-equiv ((contexts equiv-argcontexts-p)
                                       (args fgl-arglist-p)
                                       (terms pseudo-term-listp)
                                       (eval-alist alistp)
                                       (env fgl-env-p)
                                       &optional (logicman 'logicman))
  :measure (+ (len args) (len terms))
  :hints(("Goal" :in-theory (enable len)))
  :guard (lbfr-listp (fgl-arglist-bfrlist args))
  :guard-hints (("goal" :in-theory (enable fgl-arglist-bfrlist
					   fgl-arg-bfrlist
					   bfr-listp$-of-append)
		 :do-not-induct t))
  (if (and (atom args) (atom terms))
      t
    (and (b* ((arg1 (car args))
	      (term1 (car terms)))
	   (fgl-arg-case arg1
	     :unbound t
	     :obj (fgl-ev-context-equiv (equiv-argcontexts-first contexts)
					(fgl-object-eval arg1.obj env)
					(fgl-ev term1 eval-alist))))
         (fgl-ev-arglist-contexts-equiv
	  (equiv-argcontexts-rest contexts) (cdr args) (cdr terms) eval-alist env)))
  ///

  (defthm fgl-ev-arglist-contexts-equiv-of-substitute-newly-bound
    (implies (and (fgl-arglist-unbound-vars-match-p args terms)
		  (eval-alist-extension-p eval-alist (fgl-object-bindings-eval
						      (fgl-arglist-new-bindings args bindings)
						      env logicman))
		  (fgl-ev-arglist-contexts-equiv contexts args terms eval-alist env logicman))
	     (fgl-ev-arglist-contexts-equiv contexts (fgl-arglist-substitute-newly-bound args bindings)
					    terms eval-alist env logicman))
    :hints(("Goal" :in-theory (enable fgl-arglist-substitute-newly-bound
				      fgl-arglist-new-bindings
				      fgl-object-bindings-eval
				      fgl-arglist-unbound-vars-match-p))))

  (local (in-theory (enable  default-car default-cdr)))

  (defthm fgl-ev-arglist-contexts-equiv-when-all-boundp
    (implies (fgl-arglist-all-boundp args)
	     (equal (fgl-ev-arglist-contexts-equiv contexts args terms eval-alist env logicman)
		    (fgl-ev-argcontexts-equiv contexts (fgl-ev-list terms eval-alist)
					      (fgl-objectlist-eval (fgl-arglist->objects args) env logicman))))
    :hints(("Goal" :in-theory (enable fgl-ev-argcontexts-equiv-recursive
				      fgl-objectlist-eval
				      fgl-arglist-unbounds
				      fgl-arglist->objects))))


  (local (defthm consp-of-fgl-ev-list
	   (iff (consp (fgl-ev-list x a))
		(consp x))))

  (defthm fgl-ev-argcontexts-equiv-of-fgl-arglist-eval-with-rev-subst
    (implies (and (fgl-arglist-unbound-vars-match-p args terms)
		  (eval-alist-extension-p eval-alist (acl2::fal-extract (fgl-arglist-unbounds args) rev-subst))
		  (fgl-ev-arglist-contexts-equiv argcontexts args terms eval-alist env)
		  (subsetp-equal (fgl-arglist-unbounds args) (alist-keys rev-subst)))
	     (fgl-ev-argcontexts-equiv argcontexts (fgl-ev-list terms eval-alist)
				       (fgl-arglist-eval-with-rev-subst
					args rev-subst env logicman)))
    :hints(("Goal" :in-theory (enable fgl-ev-argcontexts-equiv-recursive
				      acl2::fal-extract
				      fgl-arglist-unbounds
				      fgl-arglist-eval-with-rev-subst
				      subsetp-equal
				      fgl-arglist-unbound-vars-match-p)
	    :expand ((:free (terms ev)
		      (:with fgl-ev-argcontexts-equiv-recursive
		       (fgl-ev-argcontexts-equiv argcontexts terms ev)))
		     (FGL-ARGLIST-EVAL-WITH-REV-SUBST ARGS REV-SUBST ENV))
	    :induct (fgl-ev-arglist-contexts-equiv argcontexts args terms eval-alist env)
	    :do-not-induct t)))

  (local (in-theory (enable pseudo-term-list-fix fgl-arglist-fix))))


(defsection-progn fgl-interp-argcontexts-support

  (defthm len-of-fgl-arglist->objects
    (equal (len (fgl-arglist->objects x))
	   (len x))
    :hints(("Goal" :in-theory (enable fgl-arglist->objects))))

  (defthm len-of-fgl-objectlist-eval
    (equal (len (fgl-objectlist-eval x env))
	   (len x))
    :hints(("Goal" :in-theory (enable len)
	    :induct (len x)
	    :expand ((fgl-objectlist-eval x env)))))

  (local (in-theory (enable set-difference-equal-under-iff)))

  (local (in-theory (enable intersectp-equal-of-set-diff-when-not-intersectp-first))))


;; Variable-name correspondence is proved separately.  Unbound positions
;; impose no evaluation constraint and do not constrain extension stability.
(define fgl-arglist-bound-contexts ((args fgl-arglist-p)
                                    (contexts equiv-argcontexts-p))
  :returns (new-contexts
	    (and (equiv-argcontexts-p new-contexts)
                 (equal (equal new-contexts t)
                        (equal (equiv-argcontexts-fix contexts) t)))
	    :hints (("Goal" :induct (fgl-arglist-bound-contexts args contexts)
		     :in-theory (enable fgl-arglist-bound-contexts
                                        equiv-argcontexts-p
                                        equiv-argcontexts-fix
                                        equiv-argcontexts-rest
                                        equiv-contextslist-p)
		     :do-not-induct t)))
  :verify-guards nil
  :hooks nil
  (cond ((atom args) (equiv-argcontexts-fix contexts))
        ((eq (equiv-argcontexts-fix contexts) t) t)
        (t (cons (if (fgl-arg-case (car args) :unbound)
		     '(unequiv)
		   (equiv-argcontexts-first contexts))
                 (fgl-arglist-bound-contexts
		  (cdr args) (equiv-argcontexts-rest contexts)))))
  ///
  (verify-guards fgl-arglist-bound-contexts
    :hints (("Goal" :in-theory (enable equiv-argcontexts-p
				       equiv-argcontexts-fix
				       equiv-argcontexts-rest)))))


(defthm equiv-contextslist-p-of-fgl-arglist-bound-contexts
  (implies (not (equal (equiv-argcontexts-fix contexts) t))
	   (equiv-contextslist-p (fgl-arglist-bound-contexts args contexts)))
  :hints (("Goal" :use return-type-of-fgl-arglist-bound-contexts
	   :in-theory (enable equiv-argcontexts-p))))


(defsection fgl-ev-argcontexts-equiv-forall-extensions
  (defun-sk fgl-ev-argcontexts-equiv-forall-extensions (contexts terms eval-alist)
    (forall ext
	    (implies (and (syntaxp (not (equal ext eval-alist)))
			  (eval-alist-extension-p ext eval-alist))
		     (fgl-ev-argcontexts-equiv contexts
					       (fgl-ev-list terms ext)
					       (fgl-ev-list terms eval-alist))))
    :rewrite :direct)
  (in-theory (disable fgl-ev-argcontexts-equiv-forall-extensions fgl-ev-argcontexts-equiv-forall-extensions-necc))
  (local
   (defthm fgl-ev-context-equiv-list-reflexive
     (fgl-ev-context-equiv-list contexts x x)
     :hints (("Goal" :induct (fgl-ev-context-equiv-list contexts x x)
	      :in-theory (enable fgl-ev-context-equiv-list
				 acl2::nth-equiv-recursive
				 fgl-ev-context-equiv-is-equal-of-fixes)))))
  (local (defthmd fgl-ev-arglist-contexts-equiv-with-bound-contexts
	   (implies (fgl-ev-arglist-contexts-equiv contexts args terms eval-alist env logicman)
		    (equal (fgl-ev-arglist-contexts-equiv contexts args terms ext env logicman)
			   (fgl-ev-argcontexts-equiv
			    (fgl-arglist-bound-contexts args contexts)
			    (fgl-ev-list terms ext)
			    (fgl-ev-list terms eval-alist))))
	   :hints (("Goal"
		    :induct (fgl-ev-arglist-contexts-equiv contexts args terms eval-alist env logicman)
		    :in-theory (enable fgl-ev-arglist-contexts-equiv
				       fgl-arglist-bound-contexts
				       fgl-arg-kind
				       fgl-arg-obj->obj
				       default-car default-cdr
				       fgl-ev-argcontexts-equiv
				       fgl-ev-argcontexts-equiv-recursive
				       fgl-ev-context-equiv-list
				       acl2::nth-equiv-recursive
				       fgl-ev-context-equiv-is-equal-of-fixes
				       equiv-argcontexts-fix
				       equiv-argcontexts-p
				       equiv-argcontexts-first
				       equiv-argcontexts-rest)
		    :do-not-induct t))))
  (local (define argcontexts-equiv-induct ((contexts equiv-contextslist-p)
					   (x true-listp) (y true-listp) (z true-listp))
	   :returns (result true-listp)
	   :verify-guards nil :hooks nil
	   (if (atom contexts) (list x y z)
	     (argcontexts-equiv-induct (cdr contexts) (cdr x) (cdr y) (cdr z)))))
  (local (defthmd fgl-ev-argcontexts-equiv-base-change
	   (implies (fgl-ev-argcontexts-equiv contexts y z)
		    (equal (fgl-ev-argcontexts-equiv contexts x y)
			   (fgl-ev-argcontexts-equiv contexts x z)))
	   :hints (("Goal" :induct (argcontexts-equiv-induct contexts x y z)
		    :in-theory (enable argcontexts-equiv-induct fgl-ev-argcontexts-equiv
				       fgl-ev-context-equiv-list
				       fgl-ev-context-equiv-is-equal-of-fixes)
		    :do-not-induct t))))
  (defthm fgl-ev-arglist-contexts-equiv-of-extension
    (implies (and (fgl-ev-argcontexts-equiv-forall-extensions
		   (fgl-arglist-bound-contexts args contexts) terms eval-alist)
		  (fgl-ev-arglist-contexts-equiv contexts args terms eval-alist env logicman)
		  (eval-alist-extension-p ext eval-alist))
	     (fgl-ev-arglist-contexts-equiv contexts args terms ext env logicman))
    :hints (("Goal"
	     :use ((:instance fgl-ev-argcontexts-equiv-forall-extensions-necc
		    (contexts (fgl-arglist-bound-contexts args contexts))))
	     :in-theory (enable fgl-ev-arglist-contexts-equiv-with-bound-contexts))))

  (local (in-theory (enable alist-keys-subsetp-when-sub-alistp)))

  (defthm eval-alist-extension-p-of-append-new-keys-ext
    (implies (and (not (intersectp-equal (alist-keys x) (alist-keys z)))
		  (eval-alist-extension-p y z))
	     (eval-alist-extension-p (append x y) z))
    :hints(("Goal" :in-theory (e/d (;; acl2::sub-alistp
				    sub-alistp-by-witness
				    acl2::hons-assoc-equal-iff-member-alist-keys)
				   (ACL2::ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL)))))

  (local (defthm not-intersectp-of-intersection
	   (implies (not (And (intersectp-equal x y)
			      (intersectp-equal x z)))
		    (not (intersectp-equal x (intersection-equal y z))))
	   :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw)))))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-of-extension
    (implies (and (fgl-ev-argcontexts-equiv-forall-extensions contexts terms eval-alist1)
		  (eval-alist-extension-p eval-alist2 eval-alist1))
	     (fgl-ev-argcontexts-equiv-forall-extensions contexts terms eval-alist2))
    :hints (("Goal"
	     :expand ((fgl-ev-argcontexts-equiv-forall-extensions contexts terms eval-alist2))
	     :use ((:instance fgl-ev-argcontexts-equiv-base-change
		    (x (fgl-ev-list terms (fgl-ev-argcontexts-equiv-forall-extensions-witness contexts terms eval-alist2)))
		    (y (fgl-ev-list terms eval-alist2))
		    (z (fgl-ev-list terms eval-alist1))))
	     :in-theory (enable fgl-ev-argcontexts-equiv-forall-extensions-necc
				eval-alist-extension-p-transitive-1))))

  (local (defthm sub-alistp-fal-extract-lemma
	   (implies (and (acl2::sub-alistp (append minor major) ext)
			 (not (intersectp-equal keys (alist-keys minor))))
		    (acl2::sub-alistp (acl2::fal-extract keys major) ext))
	   :hints (("goal" :in-theory (enable sub-alistp-by-witness)))))

  (local (Defthm fgl-object-bindings-eval-of-new-bindings
	   (equal (fgl-object-bindings-eval (fgl-arglist-new-bindings arglist bindings) env)
		  (acl2::fal-extract (fgl-arglist-unbounds arglist) (fgl-object-bindings-eval bindings env)))
	   :hints(("Goal" :in-theory (enable fgl-arglist-unbounds
					     fgl-arglist-new-bindings
					     fgl-object-bindings-eval
					     acl2::fal-extract)))))

  (local (defthm alist-keys-of-fal-extract
	   (equal (alist-keys (acl2::fal-extract keys x))
		  (intersection-equal keys (alist-keys x)))
	   :hints(("Goal" :in-theory (enable acl2::fal-extract intersection-equal alist-keys)))))

  (local (defthm sub-alistp-fal-extract
	   (acl2::sub-alistp (acl2::fal-extract keys x) x)
	   :hints(("Goal" :in-theory (enable sub-alistp-by-witness)))))

  (local (defthm sub-alistp-fal-extract-trans
	   (implies (acl2::sub-alistp x y)
		    (acl2::sub-alistp (acl2::fal-extract keys x) y))
	   :hints(("Goal" :in-theory (enable eval-alist-extension-p-transitive-1)))))

  (local (defthm subsetp-set-difference
	   (implies (subsetp-equal x y)
		    (subsetp-equal (set-difference-equal x z) y))
	   :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))

  ;; Prove extension stability and pointwise agreement separately.
  (defthm fgl-interp-term-argcontexts-stable
    (implies (and (fgl-ev-argcontexts-equiv-forall-extensions
		   (fgl-arglist-bound-contexts arglist argcontexts)
		   args
		   (append minor
			   (fgl-object-bindings-eval arglist-bindings env arglist-logicman)))
		  (fgl-ev-arglist-contexts-equiv
		   argcontexts
		   arglist
		   args
		   (append minor
			   (fgl-object-bindings-eval arglist-bindings env arglist-logicman))
		   env
		   arglist-logicman)
		  (fgl-arglist-unbound-vars-match-p arglist args)
		  (equal minor-keys (alist-keys minor))
		  (eval-alist-extension-p (fgl-object-bindings-eval fncall-bindings env fncall-logicman)
					  (fgl-object-bindings-eval arglist-bindings env arglist-logicman))
		  (fgl-ev-argcontext-congruence-correct-p
		   contexts fn argcontexts (len args))
		  (not (intersectp-equal minor-keys
					 (fgl-arglist-unbounds arglist)))
		  (subsetp-equal (fgl-arglist-unbounds arglist)
				 (alist-keys (fgl-object-bindings-fix fncall-bindings)))
		  (equal (len arglist) (len args)))
	     (fgl-ev-context-equiv-forall-extensions
	      contexts
	      (pseudo-term-fncall fn args)
	      (append minor
		      (fgl-object-bindings-eval fncall-bindings env fncall-logicman))))
    :hints ((acl2::witness :ruleset fgl-ev-context-equiv-forall-extensions-witnessing)
	    (and stable-under-simplificationp
		 '(:use ((:instance fgl-ev-argcontext-congruence-correct-p-necc
			  (ctx contexts)
			  (arg-ctxs argcontexts)
			  (fn fn)
			  (arity (len args))
			  (args2 (fgl-arglist-eval-with-rev-subst
				  (fgl-arglist-substitute-newly-bound arglist arglist-bindings)
				  (fgl-object-bindings-eval fncall-bindings env fncall-logicman)
				  env arglist-logicman))
			  (args1 (fgl-ev-list args ext0)))
			 (:instance fgl-ev-argcontext-congruence-correct-p-necc
			  (ctx contexts)
			  (arg-ctxs argcontexts)
			  (fn fn)
			  (arity (len args))
			  (args2 (fgl-arglist-eval-with-rev-subst
				  (fgl-arglist-substitute-newly-bound arglist arglist-bindings)
				  (fgl-object-bindings-eval fncall-bindings env fncall-logicman)
				  env arglist-logicman))
			  (args1 (fgl-ev-list args (append minor (fgl-object-bindings-eval fncall-bindings env fncall-logicman))))))
		   :in-theory (enable eval-alist-extension-p-transitive-1
			              eval-alist-extension-p-transitive-2
			              fgl-ev-arglist-contexts-equiv-of-extension
			              fgl-ev-of-fncall-args)))))

  (defthm fgl-interp-term-argcontexts-value
    (implies (and (fgl-ev-argcontexts-equiv-forall-extensions
		   (fgl-arglist-bound-contexts arglist argcontexts)
		   args
		   (append minor
			   (fgl-object-bindings-eval arglist-bindings env arglist-logicman)))
		  (fgl-ev-arglist-contexts-equiv
		   argcontexts
		   arglist
		   args
		   (append minor
			   (fgl-object-bindings-eval arglist-bindings env arglist-logicman))
		   env
		   arglist-logicman)
		  (fgl-arglist-unbound-vars-match-p arglist args)
		  (equal minor-keys (alist-keys minor))
		  (eval-alist-extension-p (fgl-object-bindings-eval fncall-bindings env fncall-logicman)
					  (fgl-object-bindings-eval arglist-bindings env arglist-logicman))
		  (fgl-ev-argcontext-congruence-correct-p
		   contexts fn argcontexts (len args))
		  (not (intersectp-equal minor-keys
					 (fgl-arglist-unbounds arglist)))
		  (subsetp-equal (fgl-arglist-unbounds arglist)
				 (alist-keys (fgl-object-bindings-fix fncall-bindings)))
		  (equal (len arglist) (len args)))
	     (equal
	      (fgl-ev-context-fix
	       contexts
	       (fgl-ev
		(cons (pseudo-fnsym-fix fn) args)
		(append minor
			(fgl-object-bindings-eval fncall-bindings env fncall-logicman))))
	      (fgl-ev-context-fix contexts (fgl-ev
					    (cons
					     (pseudo-fnsym-fix fn)
					     (kwote-lst
					      (fgl-arglist-eval-with-rev-subst
					       (fgl-arglist-substitute-newly-bound arglist arglist-bindings)
					       (fgl-object-bindings-eval fncall-bindings env fncall-logicman)
					       env arglist-logicman)))
					    nil))))
    :hints (("goal" :use ((:instance fgl-ev-argcontext-congruence-correct-p-necc
			   (ctx contexts)
			   (arg-ctxs argcontexts)
			   (fn fn)
			   (arity (len args))
			   (args2 (fgl-arglist-eval-with-rev-subst
				   (fgl-arglist-substitute-newly-bound arglist arglist-bindings)
				   (fgl-object-bindings-eval fncall-bindings env fncall-logicman)
				   env arglist-logicman))
			   (args1 (fgl-ev-list args (append minor (fgl-object-bindings-eval fncall-bindings env fncall-logicman))))))
	     :in-theory (enable fgl-ev-of-pseudo-term-fncall
				fgl-ev-of-fncall-args
				fgl-ev-arglist-contexts-equiv-of-extension))))

  (local (defthm eval-alist-extension-p-append-cons
	   (implies (and (eval-alist-extension-p maj2 maj1)
			 (not (hons-assoc-equal var maj2))
			 (eval-alist-extension-p ext (append min (cons (cons var val) maj2))))
		    (eval-alist-extension-p ext (append min maj1)))
	   :hints(("Goal" :in-theory (enable sub-alistp-by-witness)))))

  ;; Pointwise construction uses evaluation at one alist.  The stability
  ;; constructors below need no interpreted values.
  (defthm fgl-ev-arglist-contexts-equiv-empty
    (implies (not (consp terms))
	     (fgl-ev-arglist-contexts-equiv contexts nil terms eval-alist env logicman))
    :hints (("Goal" :in-theory (enable fgl-ev-arglist-contexts-equiv))))

  (defthm fgl-ev-arglist-contexts-equiv-cons-obj
    (equal (fgl-ev-arglist-contexts-equiv
	    contexts (cons (fgl-arg-obj obj) args) (cons term terms) eval-alist env logicman)
	   (and (fgl-ev-context-equiv (equiv-argcontexts-first contexts)
				      (fgl-object-eval obj env logicman)
				      (fgl-ev term eval-alist))
		(fgl-ev-arglist-contexts-equiv
		 (equiv-argcontexts-rest contexts) args terms eval-alist env logicman)))
    :hints (("Goal" :in-theory (enable fgl-ev-arglist-contexts-equiv))))

  (defthm fgl-ev-arglist-contexts-equiv-cons-unbound
    (equal (fgl-ev-arglist-contexts-equiv
	    contexts (cons (fgl-arg-unbound var) args) (cons term terms) eval-alist env logicman)
	   (fgl-ev-arglist-contexts-equiv
	    (equiv-argcontexts-rest contexts) args terms eval-alist env logicman))
    :hints (("Goal" :in-theory (enable fgl-ev-arglist-contexts-equiv))))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-empty
    (implies (not (consp args))
	     (fgl-ev-argcontexts-equiv-forall-extensions
	      (fgl-arglist-bound-contexts nil argcontexts)
	      args
	      eval-alist))
    :hints(("Goal" :in-theory (enable fgl-ev-argcontexts-equiv-forall-extensions))))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-of-t
    (fgl-ev-argcontexts-equiv-forall-extensions t terms eval-alist)
    :hints (("Goal" :in-theory (enable fgl-ev-argcontexts-equiv-forall-extensions
				       fgl-ev-argcontexts-equiv))))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-of-cons
    (implies (and (consp terms)
		  (fgl-ev-context-equiv-forall-extensions
		   (equiv-argcontexts-first contexts) (car terms) eval-alist)
		  (fgl-ev-argcontexts-equiv-forall-extensions
		   (equiv-argcontexts-rest contexts) (cdr terms) eval-alist))
	     (fgl-ev-argcontexts-equiv-forall-extensions contexts terms eval-alist))
    :hints (("Goal"
	     :expand ((fgl-ev-argcontexts-equiv-forall-extensions contexts terms eval-alist))
	     :use ((:instance fgl-ev-argcontexts-equiv-forall-extensions-necc
		    (contexts (equiv-argcontexts-rest contexts))
		    (terms (cdr terms))
		    (ext (fgl-ev-argcontexts-equiv-forall-extensions-witness contexts terms eval-alist))))
	     :in-theory (enable fgl-ev-argcontexts-equiv-recursive
				fgl-ev-context-equiv-is-equal-of-fixes
				fgl-ev-context-equiv-forall-extensions-necc))))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-of-cons-obj
    (implies (and (fgl-ev-argcontexts-equiv-forall-extensions
		   (fgl-arglist-bound-contexts args (equiv-argcontexts-rest argcontexts))
		   (cdr terms)
		   eval-alist)
		  (consp terms)
		  (fgl-ev-context-equiv-forall-extensions
		   (equiv-argcontexts-first argcontexts)
		   (car terms)
		   eval-alist2)
		  (eval-alist-extension-p eval-alist eval-alist2))
	     (fgl-ev-argcontexts-equiv-forall-extensions
	      (fgl-arglist-bound-contexts (cons (fgl-arg-obj obj) args) argcontexts)
	      terms
	      eval-alist))
    :hints (("Goal"
	     :use ((:instance fgl-ev-argcontexts-equiv-forall-extensions-of-cons
		    (contexts (fgl-arglist-bound-contexts (cons (fgl-arg-obj obj) args) argcontexts))))
	     :in-theory (enable equiv-argcontexts-p fgl-arglist-bound-contexts
				equiv-argcontexts-fix equiv-argcontexts-first equiv-argcontexts-rest
				fgl-ev-context-equiv-is-equal-of-fixes
				fgl-ev-context-equiv-forall-extensions-necc)
	     :do-not-induct t)))

  (defthm fgl-ev-argcontexts-equiv-forall-extensions-of-cons-unbound
    (implies (fgl-ev-argcontexts-equiv-forall-extensions
	      (fgl-arglist-bound-contexts args (equiv-argcontexts-rest argcontexts))
	      terms
	      eval-alist)
	     (fgl-ev-argcontexts-equiv-forall-extensions
	      (fgl-arglist-bound-contexts (cons (fgl-arg-unbound var) args) argcontexts)
	      (cons term terms)
	      eval-alist))
    :hints (("Goal"
	     :use ((:instance fgl-ev-argcontexts-equiv-forall-extensions-of-cons
		    (contexts (fgl-arglist-bound-contexts (cons (fgl-arg-unbound var) args) argcontexts))
		    (terms (cons term terms))))
	     :in-theory (enable fgl-arglist-bound-contexts
				equiv-argcontexts-fix equiv-argcontexts-first equiv-argcontexts-rest)
	     :do-not-induct t))))


(defsection-progn fgl-interp-binding-value-support
  (defthm sub-alistp-when-fgl-bindings-extension-p
    (implies (fgl-bindings-extension-p x y)
	     (acl2::sub-alistp (fgl-object-bindings-fix y) (fgl-object-bindings-fix x)))
    :hints(("Goal" :in-theory (e/d (sub-alistp-by-witness
				    lookup-when-fgl-bindings-extension-p-fix)
				   (hons-assoc-equal-of-fgl-object-bindings-fix))))))


(defsection-progn fgl-interp-sat-and-pathcond-evaluation-support

  (defthm interp-st-sat-check-not-unsat-when-eval
    (b* (((mv status & &)
	  (interp-st-sat-check params bfr interp-st state)))
      (implies (and (bind-free '((env . env)) (env))
		    (interp-st-bfrs-ok interp-st)
		    (interp-st-bfr-p bfr)
		    (gobj-bfr-eval bfr env (interp-st->logicman interp-st))
		    (logicman-pathcond-eval (fgl-env->bfr-vals env)
					    (interp-st->pathcond interp-st)
					    (interp-st->logicman interp-st))
		    (logicman-pathcond-eval (fgl-env->bfr-vals env)
					    (interp-st->constraint interp-st)
					    (interp-st->logicman interp-st)))
	       (not (equal status :unsat)))))

  (encapsulate nil
    (local (defthm pathcond-rewind-when-not-enabled
	     (implies (not (pathcond-enabledp pathcond))
		      (equal (pathcond-rewind bfr-mode pathcond)
			     (pathcond-fix pathcond)))
	     :hints(("Goal" :in-theory (enable pathcond-rewind)))))
    (def-updater-independence-thm pathcond-eval-of-rewind-when-pathcond-eval-checkpoints-equiv
      (implies (and (equal (logicman-pathcond-eval-checkpoints!
			    env (interp-st->pathcond new)
			    (interp-st->logicman new))
			   (logicman-pathcond-eval-checkpoints!
			    env (interp-st->pathcond old)
			    (interp-st->logicman old)))
		    (iff (pathcond-enabledp (interp-st->pathcond old))
			 (pathcond-enabledp (interp-st->pathcond new)))
		    (equal bfr-mode (logicman->mode (interp-st->logicman old)))
		    (equal bfr-mode (logicman->mode (interp-st->logicman new)))
		    (pathcond-rewind-ok bfr-mode (interp-st->pathcond old)))
	       (equal (logicman-pathcond-eval
		       env (pathcond-rewind bfr-mode (interp-st->pathcond new))
		       (interp-st->logicman new))
		      (logicman-pathcond-eval
		       env (pathcond-rewind bfr-mode (interp-st->pathcond old))
		       (interp-st->logicman old))))
      :hints(("Goal" :in-theory (e/d (pathcond-rewind-ok
				      logicman-pathcond-eval-checkpoints!)
				     (logicman-pathcond-eval-checkpoints-of-pathcond-rewind))
	      :expand ((:free (ist)
			(logicman-pathcond-eval-checkpoints
			 env (update-nth *pathcond-enabledp* t (interp-st->pathcond ist))
			 (interp-st->logicman ist)))))))))


(local (in-theory
	(e/d (fgl-ev-context-equiv-forall-extensions-necc
	      iff-forall-extensions-necc iff?-forall-extensions-necc
	      fgl-ev-of-extension-when-equal-forall-extensions
	      equal?-bindinglist-forall-extensions equal?-list-forall-extensions
	      equal-list-forall-extensions-necc equal-bindinglist-forall-extensions-necc
	      equal-subst-forall-extensions-necc)
	     (fgl-ev-when-pseudo-term-lambda fgl-ev-when-pseudo-term-fncall
					     fgl-interp-lambda-arglist-equiv-contexts))))


(local (in-theory (enable subsetp-set-difference-when-subsetp)))


(local (in-theory (enable subsetp-set-difference-simple)))


;; This book exports its main interpreter results and the supporting lemmas below.
;; Support lemmas are nonlocal so other interpreter proof books can reuse them
;; without duplicating proofs. They stay disabled for clients until explicitly
;; enabled through this named theory; ordinary inclusion uses the main results.
(deftheory interp-eval-support-rules
  '(member-equiv-contexts-implies-not-quote
    fgl-interp-equiv-refinementp-implies-context-fix
    eval-under-iff-when-boolean-fix
    iff-forall-extensions-of-conjoin
    iff-forall-extensions-of-quote
    iff-forall-extensions-relieve-hyp-synp
    fgl-ev-test-when-concrete-boolean-fix
    fgl-ev-context-equiv-forall-extensions-of-if-nonbranching-true
    fgl-ev-context-equiv-forall-extensions-of-if-nonbranching-false
    fgl-ev-or-test-of-extension
    fgl-ev-context-fix-of-or-test-of-extension
    fgl-ev-or-test-when-concrete-boolean-fix
    fgl-ev-context-equiv-forall-extensions-of-or-nonbranching-true
    fgl-ev-context-equiv-forall-extensions-of-or-nonbranching-false
    fgl-ev-of-check-equivbind-hyp
    iff-forall-extensions-of-check-equivbind-hyp
    iff-forall-extensions-of-pseudo-term-fix
    iff-forall-extensions-of-match-assums
    fgl-object-eval-of-normalize-equal-order
    fgl-ev-when-iff-forall-extensions
    fgl-ev-context-fix-of-rewrite-rule-rhs
    fgl-ev-context-equiv-forall-extensions-when-constant
    fgl-ev-context-equiv-forall-extensions-of-boolean-fncall
    len-of-fgl-ev-list
    sub-alistp-when-fgl-bindings-extension-p
    interp-st-sat-check-not-unsat-when-eval
    pathcond-eval-of-rewind-when-pathcond-eval-checkpoints-equiv))
(in-theory
 (disable fgl-ev-context-equiv-of-equiv-rel
          fgl-ev-context-fix-equal-by-eval
          iff-forall-extensions-of-negated
          interp-eval-support-rules))