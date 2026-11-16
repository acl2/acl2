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

; Shared private support for the interpreter's definitions and proofs.
; The interpreter books include this book locally.  Keep its dependencies below
; interp-defs (in particular, independent of tracing and fancy evaluation), so
; certification can overlap those dependencies.

(in-package "FGL")

(include-book "primitives-stub")
(include-book "centaur/meta/bindinglist" :dir :system)
(include-book "system/f-put-global" :dir :system)

(local (include-book "std/util/defret-mutual-generate" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/meta/resolve-flag-cp" :dir :system))
(local (include-book "centaur/meta/urewrite" :dir :system))
(local (include-book "centaur/meta/let-abs" :dir :system))
(local (include-book "centaur/meta/flatten-clause" :dir :system))

(local (std::make-returnspec-config :hints-sub-returnnames t))

(deflabel fgl-interp-proof-support-start)

(local (std::add-default-post-define-hook :fix))

(local (in-theory (e/d (acl2::kwote-lst-redef)
		       (kwote-lst))))

(defthm interp-st-bfrs-ok-of-update-reclimit
  (implies (interp-st-bfrs-ok interp-st)
	   (interp-st-bfrs-ok (update-interp-st->reclimit reclimit interp-st))))

(defthm interp-st-bfrs-ok-of-update-equiv-contexts
  (implies (interp-st-bfrs-ok interp-st)
	   (interp-st-bfrs-ok (update-interp-st->equiv-contexts equiv-contexts interp-st))))

(defthm interp-st->logicman-of-update-reclimit
  (equal (interp-st->logicman (update-interp-st->reclimit reclimit interp-st))
	 (interp-st->logicman interp-st)))

(defthm interp-st->logicman-of-update-equiv-contexts
  (equal (interp-st->logicman (update-interp-st->equiv-contexts equiv-contexts interp-st))
	 (interp-st->logicman interp-st)))

(defthm interp-st->logicman-of-update-stack
  (equal (interp-st->logicman (update-interp-st->stack equiv-contexts interp-st))
	 (interp-st->logicman interp-st)))

(defthm interp-st->logicman-of-update-errmsg
  (equal (interp-st->logicman (update-interp-st->errmsg equiv-contexts interp-st))
	 (interp-st->logicman interp-st)))

(local (in-theory (disable w)))

(defthm assoc-when-key
  (implies k
	   (equal (assoc k a)
		  (hons-assoc-equal k a))))

(defthm pseudo-var-list-p-of-append
  (implies (and (pseudo-var-list-p x)
		(pseudo-var-list-p y))
	   (pseudo-var-list-p (append x y))))

(local (in-theory (disable pseudo-termp acl2::magic-ev)))

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

(defthm len-equal-0
  (equal (equal (len x) 0)
	 (not (consp x))))

(defthm pseudo-term-bindinglist-count-when-consp
  (implies (consp x)
	   (< (+ (pseudo-term-binding-count (car x))
		 (pseudo-term-list-binding-count (cdr x)))
	      (pseudo-term-list-binding-count x)))
  :rule-classes :linear)

(defthm len-of-cons
  (equal (len (cons a b))
	 (+ 1 (len b))))

(defthm and*-hyp
  (implies (acl2::rewriting-negative-literal `(acl2::binary-and* ,a ,b))
	   (iff (and* a b) (and a b))))

(defun len-is (x n)
  (if (zp n)
      (and (eql n 0) (atom x))
    (and (consp x)
	 (len-is (cdr x) (1- n)))))

(defthm open-len-is
  (implies (syntaxp (quotep n))
	   (equal (len-is x n)
		  (if (zp n)
		      (and (eql n 0) (atom x))
		    (and (consp x)
			 (len-is (cdr x) (1- n)))))))

(defthm equal-len-hyp
  (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
			     (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
			 (quotep n)))
	   (equal (equal (len x) n)
		  (len-is x n))))

(defthm mv-nth-of-cons
  (equal (mv-nth n (cons a b))
	 (if (zp n) a (mv-nth (1- n) b)))
  :hints(("Goal" :in-theory (enable mv-nth))))

(defthm len-cdr-less-when-consp
  (implies (consp x)
	   (< (len (cdr x)) (len x)))
  :rule-classes :linear)

(defthm stack$a-open-nth-scratch
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
		   (:free (a b) (minor-stack-scratch-len (cons a b)))))))

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
			   append
			   get-term->bvar$c-updater-independence)))

(deflabel fgl-interp-bfr-listp-rules-start)

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
			       stack$a-push-scratch)
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
			       stack$a-update-scratch)
	    :expand ((major-stack-bfrlist stack)
		     (minor-stack-bfrlist (major-frame->minor-stack (car stack))))
	    :do-not-induct t)))

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

  (defthm bfr-listp-of-fgl-object-bfrlist-car
    (implies (bfr-listp (fgl-objectlist-bfrlist x))
	     (bfr-listp (fgl-object-bfrlist (car x))))
    :hints(("Goal" :expand ((fgl-objectlist-bfrlist x))
	    :in-theory (enable default-car))))

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
	    (scratchobj-tmplsubsts (set-difference-equal
				    *scratchobj-types*
				    (acl2::fal-extract
				     '(:bfr :bfrlist :fnsym :formals)
				     *scratchobj-types*)))))))

  (defcong interp-st-scratch-isomorphic interp-st-scratch-isomorphic
    (update-interp-st->reclimit reclimit interp-st) 2
    :hints(("Goal" :in-theory (enable interp-st-scratch-isomorphic))))

  (Defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic
    (stack$a-push-scratch obj stack) 2
    :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

  (Defcong major-stack-scratch-isomorphic major-stack-scratch-isomorphic
    (stack$a-pop-scratch stack) 1
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defthm fgl-arglist-bfrlist-of-cons-obj
    (set-equiv (fgl-arglist-bfrlist (cons (fgl-arg-obj obj) rest))
	       (append (fgl-object-bfrlist obj)
		       (fgl-arglist-bfrlist rest)))
    :hints(("Goal" :in-theory (enable fgl-arg-bfrlist
				      fgl-arglist-bfrlist))))

  (defthm fgl-arglist-bfrlist-of-cons-unbound
    (set-equiv (fgl-arglist-bfrlist (cons (fgl-arg-unbound var) rest))
	       (fgl-arglist-bfrlist rest))
    :hints(("Goal" :in-theory (enable fgl-arglist-bfrlist
				      fgl-arg-bfrlist)))))

(deftheory fgl-interp-bfr-listp-rules
  (set-difference-theories (current-theory :here)
                           (current-theory 'fgl-interp-bfr-listp-rules-start)))

(deflabel fgl-interp-scratch-isomorphic-rules-start)

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
    :hints(("Goal" :in-theory (enable stack$a-push-scratch)))))

(deftheory fgl-interp-scratch-isomorphic-rules
  (set-difference-theories (current-theory :here)
                           (current-theory 'fgl-interp-scratch-isomorphic-rules-start)))

(defthm fgl-arg-bfrlist-of-fgl-arg-obj
  (equal (fgl-arg-bfrlist (fgl-arg-obj x))
	 (fgl-object-bfrlist x))
  :hints (("Goal" :in-theory (enable fgl-arg-bfrlist))))

(defun find-flag-is-hyp (clause)
  (if (atom clause)
      nil
    (let ((lit (car clause)))
      (case-match lit
	(('not ('acl2::flag-is ('quote val))) val)
	(& (find-flag-is-hyp (cdr clause)))))))

(defun fgl-interp-default-hint
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
	      '(:clause-processor cmr::dumb-flatten-clause-proc)
	      '(:clause-processor (cmr::let-abstract-lits-clause-proc clause 'xxx))
	      (and (or (not ',wait-til-stablep) stable-under-simplificationp)
		   (expand-marked)))
	     :in-theory (disable . ,fns)
	     :do-not-induct t
	     :clause-processor (cmr::resolve-flags-cp
				clause
				',(cons 'fgl::flag fns))))))

(local (in-theory (disable BFR-LISTP$-WHEN-SUBSETP-EQUAL
			   acl2::subsetp-append1
			   acl2::subsetp-of-cons
			   acl2::subsetp-trans2)))

(defthm len-update-nth-when-less
  (implies (< (nfix n) (len x))
	   (equal (len (update-nth n v x))
		  (len x))))

(defthm stack$a-nth-scratch-of-stack$a-update-scratch
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
		   (:free (stack) (minor-stack-nth-scratch m stack))))))

(defthm bfr-p-of-equal
  (bfr-p (equal x y))
  :hints(("Goal" :cases ((equal x y)))))

(defret fgl-unify-term/gobj-fn/args-masked-bfrs-ok
  (implies (and (bfr-listp (fgl-arglist-bfrlist x-args) bfrstate)
		(bfr-listp (fgl-object-bindings-bfrlist alist) bfrstate))
	   (bfr-listp (fgl-object-bindings-bfrlist new-alist) bfrstate))
  :hints (("Goal" :in-theory (enable fgl-unify-term/gobj-fn/args-masked)))
  :fn fgl-unify-term/gobj-fn/args-masked)

(defthm stack$a-top-scratch-of-set-term-index
  (equal (stack$a-top-scratch (stack$a-set-term-index idx stack))
	 (stack$a-top-scratch stack))
  :hints(("Goal" :in-theory (enable stack$a-top-scratch
				    stack$a-set-term-index))))

(defthm stack$a-top-scratch-of-set-term
  (equal (stack$a-top-scratch (stack$a-set-term idx stack))
	 (stack$a-top-scratch stack))
  :hints(("Goal" :in-theory (enable stack$a-top-scratch
				    stack$a-set-term))))

(local (in-theory (disable nth update-nth)))

(defthm not-member-of-append
  (implies (and (not (member v a))
		(not (member v b)))
	   (not (member v (append a b)))))

(local (in-theory (disable not
                           acl2::member-equal-append
                           acl2::member-of-append
                           bfr-listp$-of-append
                           w)))

(defthm len-cinstlist-when-scratchobj-isomorphic-rw
  (implies (and (scratchobj-isomorphic y (double-rewrite x))
		(syntaxp (not (equal y x)))
		(scratchobj-case y :cinstlist))
	   (equal (len (scratchobj-cinstlist->val x))
		  (len (scratchobj-cinstlist->val y)))))

(defthm len-fgl-objlist-when-scratchobj-isomorphic-rw
  (implies (and (scratchobj-isomorphic y (double-rewrite x))
		(syntaxp (not (equal y x)))
		(scratchobj-case y :fgl-objlist))
	   (equal (len (scratchobj-fgl-objlist->val x))
		  (len (scratchobj-fgl-objlist->val y)))))

(defthm intersectp-equal-of-set-diff
  (not (intersectp-equal x (set-difference-equal y x)))
  :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw))))

(defthm alist-keys-of-fgl-object-bindings-concretize
  (equal (alist-keys (fgl-object-bindings-concretize x env))
	 (alist-keys (fgl-object-bindings-fix x)))
  :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
				    fgl-object-bindings-fix
				    alist-keys))))

(Defthm fgl-bindings-extension-p-of-append
  (implies (and (not (intersectp-equal
		      (alist-keys (fgl-object-bindings-fix a))
		      (alist-keys (fgl-object-bindings-fix bb))))
		(no-duplicatesp-equal (alist-keys (fgl-object-bindings-fix a)))
		(fgl-bindings-extension-p bb b))
	   (fgl-bindings-extension-p (Append a bb) b))
  :hints(("Goal" :in-theory (enable fgl-bindings-extension-p
				    alist-keys
				    append
				    fgl-object-bindings-fix))))

;; The proof books share these settings.  interp-defs enables smaller groups
;; while introducing definitions; the later books can activate the whole phase.
;; General-purpose facts are imported locally by the interpreter books.
;; Keep them separate from FGL-specific support and enable them at their use sites.

(defsection fgl-interp-alist-proof-support

  (defthm alist-fix-of-append
    (equal (acl2::alist-fix (append a b))
	   (append (acl2::alist-fix a) (acl2::alist-fix b)))
    :hints(("Goal" :in-theory (enable append))))

  (defthmd sub-alistp-by-witness
    (implies (acl2::Rewriting-positive-literal `(acl2::sub-alistp ,a ,b))
	     (iff (acl2::sub-alistp a b)
		  (let ((x (acl2::not-sub-alistp-witness a b)))
		    (implies (hons-assoc-equal x a)
			     (equal (hons-assoc-equal x a)
				    (hons-assoc-equal x b))))))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-iff-witness))))

  (defthm hons-assoc-equal-when-sub-alistp
    (implies (and (acl2::sub-alistp a b)
		  (hons-assoc-equal k a))
	     (equal (hons-assoc-equal k b)
		    (hons-assoc-equal k a)))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-hons-assoc-equal))))

  (defthm sub-alistp-of-cons-when-not-shadowing
    (implies (or (not (consp pair))
	         (not (hons-assoc-equal (car pair) rest))
	         (equal (hons-assoc-equal (car pair) rest) pair))
	     (equal (acl2::sub-alistp (cons pair rest) ext)
		    (and (or (not (consp pair))
			     (equal (hons-assoc-equal (car pair) ext) pair))
		         (acl2::sub-alistp rest ext))))
    :hints (("goal" :cases ((acl2::sub-alistp rest ext)))
	    (and stable-under-simplificationp
	         '(:in-theory (enable sub-alistp-by-witness)))))

  (defthm alist-keys-subsetp-when-sub-alistp
    (implies (acl2::sub-alistp x y)
	     (subsetp-equal (alist-keys x) (alist-keys y)))
    ::hints(("Goal" :in-theory (e/d (acl2::subsetp-witness-rw
				     acl2::alist-keys-member-hons-assoc-equal))))))

(defsection fgl-interp-set-proof-support

  (defthm subsetp-when-set-diff-subsetp
    (implies (and (subsetp-equal (set-difference-equal x y) z)
		  (subsetp-equal y z))
	     (subsetp-equal x z))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)
	    :cases ((member-equal (acl2::subsetp-witness x z) (set-difference-equal x y))))))

  (defthm set-difference-equal-under-iff
    (iff (set-difference-equal x y)
	 (not (subsetp-equal x y)))
    :hints(("Goal" :in-theory (enable subsetp-equal set-difference-equal))))

  (defthm intersectp-equal-of-set-diff-when-not-intersectp-first
    (implies (not (intersectp-equal x y))
	     (not (intersectp-equal x (set-difference-equal y z))))
    :hints(("Goal" :in-theory (enable acl2::intersectp-witness-rw))))

  (defthm subsetp-set-difference-when-subsetp
    (implies (subsetp-equal x y)
	     (subsetp-equal (set-difference-equal z y) (set-difference-equal z x)))
    :hints ((acl2::set-reasoning)))

  (defthm subsetp-set-difference-simple
    (subsetp-equal (set-difference-equal z y) z)
    :hints ((acl2::set-reasoning))))

(defsection fgl-interp-term-proof-support

  (defthm conjoin-of-atom
    (implies (not (consp x))
	     (equal (conjoin x) ''t))
    :hints(("Goal" :in-theory (enable conjoin))))

  (defthmd pseudo-term-kind-of-cons
    (implies (pseudo-fnsym-p fn)
	     (equal (pseudo-term-kind (cons fn args))
		    :fncall))
    :hints(("Goal" :in-theory (enable pseudo-term-kind
				      pseudo-term-fix))))

  (defthmd pseudo-term-call->args-of-cons
    (implies (pseudo-fnsym-p fn)
	     (equal (pseudo-term-call->args (cons fn args))
		    (pseudo-term-list-fix args)))
    :hints(("Goal" :in-theory (enable pseudo-term-call->args
				      pseudo-term-fix
				      pseudo-term-kind-of-cons)))))

(deftheory fgl-interp-proof-enabled-rules
  '((:executable-counterpart len-is)
    (:type-prescription len-is)
    (:executable-counterpart find-flag-is-hyp)
    (:type-prescription find-flag-is-hyp)
    acl2::kwote-lst-redef
    interp-st-bfrs-ok-of-update-reclimit
    interp-st-bfrs-ok-of-update-equiv-contexts
    interp-st->logicman-of-update-reclimit
    interp-st->logicman-of-update-equiv-contexts
    interp-st->logicman-of-update-stack
    interp-st->logicman-of-update-errmsg
    assoc-when-key
    pseudo-var-list-p-of-append
    major-stack-bfrlist-of-stack$a-set-bindings
    len-equal-0
    pseudo-term-bindinglist-count-when-consp
    len-of-cons
    and*-hyp
    len-is
    open-len-is
    equal-len-hyp
    mv-nth-of-cons
    len-cdr-less-when-consp
    stack$a-open-nth-scratch
    fgl-arg-bfrlist-of-fgl-arg-obj
    find-flag-is-hyp
    len-update-nth-when-less
    stack$a-nth-scratch-of-stack$a-update-scratch
    bfr-p-of-equal
    fgl-unify-term/gobj-fn/args-masked-bfrs-ok
    stack$a-top-scratch-of-set-term-index
    stack$a-top-scratch-of-set-term
    not-member-of-append
    len-cinstlist-when-scratchobj-isomorphic-rw
    len-fgl-objlist-when-scratchobj-isomorphic-rw
    intersectp-equal-of-set-diff
    alist-keys-of-fgl-object-bindings-concretize
    fgl-bindings-extension-p-of-append
    fgl-interp-bfr-listp-rules
    fgl-interp-scratch-isomorphic-rules))
(deftheory fgl-interp-proof-disabled-rules
  '( kwote-lst
     w
     pseudo-termp
     acl2::magic-ev
     (tau-system)
     len
     default-car
     default-cdr
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
     get-term->bvar$c-updater-independence
     member-equal
     BFR-LISTP$-WHEN-SUBSETP-EQUAL
     acl2::subsetp-append1
     acl2::subsetp-of-cons
     acl2::subsetp-trans2
     nth
     update-nth
     acl2::member-equal-append
     acl2::member-of-append
     bfr-listp$-of-append))

;; The clients enable these facts at their original proof stages.  Importing
;; this book should not enable the entire collection at once.
(deftheory fgl-interp-proof-support-rules
  (set-difference-theories (universal-theory :here)
                           (universal-theory 'fgl-interp-proof-support-start)))
(in-theory
 (disable fgl-interp-proof-support-rules))
