
;;
;; Can wrapper functions be used somehow to eliminate recursion?
;;

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; ACL2 provides support for congruence-based rewriting.  This allows
;; ACL2 to treat certain equivalence relations "just like equality"
;; under appropriate conditions, and allows certain propositional
;; statements to be used as rewrite rules to guide the simplification
;; process.  This capability can be very powerful and quite addictive.
;;
;; Unfortunately ACL2's implementation of equivalences/congruences is
;; very restricted.  Perhaps the most significant restriction is the
;; fact that the equivalence relations must be binary. This fact
;; precludes perhaps the most natural application of congruence: its
;; use in modular arithmetic.
;;
;; There has been some reluctance on the part of the ACL2 developers
;; to generalize equivalence relations.  Messing around with such a
;; fundamental aspect of the theorem prover is, without question, a
;; daunting prospect.  One must also consider overall performance:
;; what impact on performance would be acceptable, given that such
;; generality (although powerful) is used so rarely.
;;
;; Below are some thoughts on how ACL2's current capabilities could be
;; extended to better support more arbitrary notions of congruence.
;; The primary thrust of this discussion involves how one might
;; generalize the concept of congruence by extending ACL2's notion of
;; a rewriting context.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; ACL2 already has a simple notion of rewriting context: the rewriter
;; modifies its behavior depending on the equivalence relation being
;; satisfied at the time.  In other words, the currently active
;; equivalence relation defines the context.  A more general context
;; might be one that involved, not just a particular function symbol,
;; but some number of terms.  In the case of mod, this additional term
;; might include the modulus.  The rewriter would then be capable of
;; pushing this context in to terms that it was rewriting, enabling it
;; to detect simplifications that might otherwise be too difficult to
;; detect using only simple rewrite rules.
;;
;; Currently the specification of a new equivalence relation can be
;; used to extend ACL2's notion of equivalence, .
;;
;; (defequiv (set-equal x y))
;;
;; In order to extend ACL2's context rewriting capability, one might
;; define a new function context:
;;
;; (defcontext (mod x n) 1)
;;
;; This tells the rewriter that (mod _ n) is a valid rewriting
;; context.  Now, any time the rewriter encounters a term of the form
;; (mod x n), it knows that x can be rewritten in a (mod _ n) context.
;;
;; Extending ACL2's notion of congruence requires that one prove
;; the following rule:
;;
;; (defcong set-equal set-equal (set-insert x y) 2)
;;
;; Which results in the following obligation:
;;
;; (implies
;;  (set-equal y y-equiv)
;;  (set-equal (set-insert x y)
;; 	       (set-insert x y-equiv)))
;;
;; Extending context congruence might involve an obligation along
;; the lines of:
;;
;; (implies
;;   (and
;;     (rationalp n)
;;     (not (equal n 0))
;;     (equiv1 x (mod a n))
;;     (equiv1 y (mod b n)))
;;   (equiv2 (mod (+ a b) n)
;;           (mod (+ x y) n)))
;;
;; Much like a congruence rule, this rule is not used as a rewrite
;; rule per-se. Rather, it reprograms the behavior of the rewriter,
;; letting it know the conditions under which it can rewrite certain
;; terms under a new context.
;;
;; If this were a simple rewrite rule, it would perform the following
;; transformation:
;;
;; (mod (+ x y) n) => (mod (+ (mod x n) (mod y n)) n)
;;
;; However, because because (mod _ n) is a known context, the rewriter
;; merely activates a (mod _ n) context when rewriting each term.  Thus,
;; plausable appliations of this rule might include:
;;
;; (mod (+ x y) n) => (mod (+ x y) n)
;;
;; (mod (+ (mod x n) y) n) => (mod (+ x y) n)
;;
;; (mod (+ n x y) n) => (mod (+ x y) n)
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; The mechanics of contextual rewriting might be very similar to the
;; way our poor man's rules work below.  In the theory below, we
;; present ACL2 with a "congruence" theorem of the form:
;;
;; (implies
;;   (and
;;     ( .. check for recursion .. )
;;     (rationalp a)
;;     (rationalp n)
;;     (not (equal n 0))
;;     ( .. syntactic check for when a = (mod v n) ..)
;;     (equal z (mod a n))
;;     (equal x ( .. syntactic manipulation when z = (mod w n) ..))
;;     ( validity checks )
;;     ( .. syntax check for a != x ..)
;;     )
;;   (equal (foo a n)
;;          (foo x n))
;;
;; The first hypothesis is supposed to check to make sure we don't
;; call this function recursively on the rewritten RHS of this
;; function.  This currently works only under :brr t
;;
;; The first syntactic check for a = (mod v n) tells us that, if
;; a = (mod v n), we probably won't be able to reduce it mod n
;; anyway.
;;
;; If a != (mov v n), we create a term of the form (mod a n) and
;; bind it to z.  This causes the rewriter to simplify a mod n
;; and binds the simplified term to z.
;;
;; The next syntactic manipulation takes terms of the form (mod w n)
;; and extracts the "w" portion, binding it to x.  If the term is not
;; of this form, x is bound to z.  By "unwrapping" the resulting term,
;; we keep from "littering" unsimplified terms with (mod _ n)
;; expressions.
;;
;; Because we are unwrapping terms syntactically, we need logical
;; tests to guarantee that we have not "broken" anything.
;;
;; The final syntactic check tells us whether we have actually
;; done anything.  If term a has actually changed in the course
;; of this process, we rewrite (foo a n) into (foo x n).
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; How might ACL2 rewrite in a given "context"?  Imagine that we are
;; rewriting term0 in a context like (mod _ n) under the equivalence
;; relation equiv.
;;
;; 1. Rewrite term0 using the weakest equivalence available for
;;    the 1st position of mod to produce term1
;;
;; 2. Create a new term2 = `(mod ,term1 n)
;;
;; 3. rewrite term2 under equiv to produce term3
;;
;; 4. If term3 is different from term2, set term0 = term3 and goto 1.
;;
;; 5. If term3 == term2, then return term1
;;
;; (Note that the "context" function must be idempotent in its "free"
;;  position in order for this to work)
;;
;; What would cause ACL2 to enter a new context?
;;
;; - Encountering a term whose leading function symbol is a known
;;   context.  We then rewrite the "free" argument of that term
;;   in the context suggested by the function.
;;
;; - Encountering a term that triggers a "context congruence" rule.
;;   We may then rewrite selected arguments in the contexts suggested
;;   by the "context congruence" rule.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Note that congruence based rewriting can often (always?) be
;; emulated with context rewriting if we define an appropriate
;; "fix" function and use that as a context.
;;
;; (defcontext (fix-set x) 1)
;;
;; (implies
;;   (equal x (fix-set a))
;;   (equal (fix-set (set-insert v a))
;;          (fix-set (set-insert v x))))
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; While (mod _ n) is one of the more obvious contexts in which this
;; technique would be useful, there would also be a significant
;; advantage to employing rewriting contexts in standard interpreter
;; analysis.
;;
;; Imagine a function (cp list st1 st2) that copies a list of address
;; locations from st1 to st2.  (cp list _ nil) could be defined as a
;; "context" and used to "fix" the memory such that only those values
;; used by a particular function would be retained.  Thus we would
;; have:
;;
;; (implies
;;   (equal st2 (cp (foo-use-set) st1 nil))
;;   (equal (foo st1)
;;          (foo st2)))
;;
;;
;; And terms like:
;;
;;   (foo (s a v r))
;;
;; would rewrite "automagically" to
;;
;;   (foo r)
;;
;; if "a" was not in the "use set" of foo.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Is there a useful notion of context "refinement" similar to ACL2's
;; current notion of refinement?  How might that work?
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Potential actions:
;;
;; 1. Forget generalized contexts.  Just fix the rewrite cache to
;;    re-simplify under weaker equivalences and call it good.
;;
;; 2. The poor man approch is good enough.  Provide support so that
;;    "non-recursive" works correctly under :brr nil and, possibly,
;;    provide (equiv x (term)) the same behavior as (equal x (term))
;;    when x is free in the hypothesis of a theorem.
;;
;; 3. Extend the rewriter to support more generalized contexts and/or
;;    to provide an efficient implementation of the basic functionality
;;    demonstrated below.
;;
;; 4. Go all the way and actually extend the current binary equivalence
;;    relations to include n-ary equivalence relations.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Below is an example that can be used to program the ACL2 rewriter
;; to perform a poor man's version of contextual rewriting.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(in-package "ACL2")

;;(include-book "syntax" :dir :syntax)


(defun unhide (x)
  (declare (type t x))
  x)

(defthm unhide-unhidden
  (implies
   (syntaxp (or (not (consp x)) (not (equal (car x) 'hide))))
   (equal (unhide x) x)))

(defthm unide-hide
  (equal (unhide (hide x))
	 x)
  :hints (("Goal" :expand (hide x))))

(in-theory (disable unhide))

;;
;; Construction to allow us to emulate "skip-rewrite" functionality
;;
(defmacro skip-rewrite (x)
  `(unhide (hide ,x)))

(set-state-ok t)

(defun ith (i list)
  (declare (type (integer 0 *) i))
  (if (consp list)
      (if (zp i) (car list)
	(ith (1- i) (cdr list)))
    nil))

(defun remove-ith (i list)
  (declare (type (integer 0 *) i))
  (if (consp list)
      (if (zp i) (cdr list)
	(cons (car list) (remove-ith (1- i) (cdr list))))
    nil))

(defun replace-ith (i v list)
  (declare (type (integer 0 *) i))
  (if (consp list)
      (if (zp i) (cons v (cdr list))
	(cons (car list) (replace-ith (1- i) v (cdr list))))
    nil))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Following are some functions that query some undocumented portions
;; of the mfc data structure looking for recursive calls of a
;; particular theorem.
;;
;; Unfortunately, the correct behavior of the final "non-recursive"
;; predicate relies on :brr t (sigh)
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun rewrite-rhs? (element)
  (and (consp element)
       (equal (car element) 'REWRITE)
       (consp (cdr element))
       (equal (cadr element) 'RHS)))

(defun rewrite-with-lemma? (lemma element)
  (and (consp element)
       (equal (car element) 'REWRITE-WITH-LEMMA)
       (member lemma (ith 4 element))))

(defun rewriting-rhs? (lemma stack)
  (and (consp stack)
       (consp (cdr stack))
       (rewrite-rhs? (cadr stack))
       (consp (cddr stack))
       (rewrite-with-lemma? lemma (caddr stack))))

;; <<<<<<< nary.lisp
;; (defun print-gstack (state)
;; =======
;; ;; jcd - added nil to cw-gstack-fn call, for ACL2 v2.9.2
;; (defun print-gstack (mfc state)
;; >>>>>>> 1.2
;;   (declare (xargs :mode :program))
;; <<<<<<< nary.lisp
;;   ;(prog2$
;;   ; (MFC-ANCESTORS mfc)
;;    (cw-gstack-fn (term-evisc-tuple t state)))
;;   ;)
;; =======
;;   (prog2$
;;    (MFC-ANCESTORS mfc)
;;    (cw-gstack-fn (term-evisc-tuple t state) nil)))
;; >>>>>>> 1.2

(defun non-recursive (lemma mfc state)
  (declare (xargs :mode :program)
	   (ignore lemma mfc state)
	   )
;  (prog2$
;   (cw "attempting lemma ~p0 ~%" lemma)
;   (prog2$
;    (cw "~p0 ~%" (len mfc))
;   (prog2$
;    (print-gstack state)
;    (if (rewriting-rhs? lemma (ith 9 mfc)) nil
      `((ok . 't)))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; Support for defcontext, defcong+
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun symbol-term (term)
  (declare (type t term))
  (if (consp term)
      (if (consp (car term))
	  (and (symbol-term (car term))
	       (symbol-term (cdr term)))
	(and (symbolp (car term))
	     (symbol-term (cdr term))))
    (symbolp term)))

(defun term-contains (var term)
  (declare (type t var term))
  (if (consp term)
      (if (consp (car term))
	  (or (term-contains var (car term))
	      (term-contains var (cdr term)))
	(or (equal var (car term))
	    (term-contains var (cdr term))))
    (equal var term)))

(defun equiv-exp (val term)
  (declare (type t val term))
  (and
   (consp term)
   (symbolp (car term))
   ;; May now be any equivalence
   ;(equal (car term) 'equal)
   (consp (cdr term))
   (symbolp (cadr term))
   (consp (cddr term))
   (term-contains val (caddr term))))

(defun wf-cong (cong)
  (declare (type t cong))
  (and (consp cong)
       (symbolp (car cong))
       (consp (cdr cong))
       (equiv-exp (car cong) (cadr cong))))

(defun wf-cong-list (congs)
  (declare (type t congs))
  (if (consp congs)
      (and (wf-cong (car congs))
	   (wf-cong-list (cdr congs)))
    (null congs)))

(defun in-pkg-of (symbol witness)
  (eql (intern-in-package-of-symbol (symbol-name symbol) witness) symbol))

(defun in-lisp-pkg (symbol)
  ;(eql (intern-in-package-of-symbol (symbol-name symbol) 'lisp::mod) symbol)
  (equal "COMMON-LISP" (symbol-package-name symbol)))

(defun fn-witness (symbol)
  (if (in-lisp-pkg symbol) 'acl2::defthm symbol))

(defun safe-symbol (lst witness)
  (declare (xargs :mode :program))
  (packn-pos lst (fn-witness witness)))

(defun replace-var-term (ovar nvar term)
  (if (consp term)
      (if (consp (car term))
	  (cons (replace-var-term ovar nvar (car term))
		(replace-var-term ovar nvar (cdr term)))
	(if (eql ovar (car term))
	    (cons nvar (replace-var-term ovar nvar (cdr term)))
	  (cons (car term) (replace-var-term ovar nvar (cdr term)))))
    (if (eql ovar term)
	nvar
      term)))

(defun replace-cong-term (cong term)
  (let* ((ovar (car cong))
	 (eex  (cadr cong))
	 (nvar (cadr eex)))
    (replace-var-term ovar nvar term)))

(defun replace-cong-terms (congs term)
  (if (consp congs)
      (let ((term (replace-cong-term (car congs) term)))
	(replace-cong-terms (cdr congs) term))
    term))

(defun prefix-list (fn oargs)
  (declare (xargs :mode :program))
  (if (consp oargs)
      (cons (safe-symbol (list fn "-" (car oargs)) (car oargs))
	    (prefix-list fn (cdr oargs)))
    nil))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; The defcontext macro just defines a set of helper functions that we
;; need in order to use a particular fix function (or "context")
;; within a defcong+ theorem.
;;
;; The expression:
;;
;; (defcontext (mod x a) 1)
;;
;; tells us that we will use the "mod" function to fix our values and
;; that every position but the 1st position is considered "context".
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

;;
;; Should we really have to do this (dequote)??
;;

(defun dequote (term)
  (if (consp term)
      (if (equal (car term) 'quote)
	  (cadr term)
	term)
    term))

(defun compare-args-to-term (list1 index position term)
  (if (consp list1)
      (if (equal position index)
	  (compare-args-to-term (cdr list1) (1+ index) position term)
	(cons `(equal (dequote ,(car list1)) (dequote (ith ,index ,term)))
	      (compare-args-to-term (cdr list1) (1+ index) position term)))
    nil))

(defun defcontext-fn (term position)
  (declare (xargs :mode :program))
  (let* ((fix-fn     (car term))
	 (args       (cdr term))
	 (nargs      (prefix-list fix-fn args))
	 (var        (ith position term))
	 (fn-witness (fn-witness fix-fn))
	 (fix-fn-unfix (safe-symbol (list fix-fn "_UNFIX") fn-witness))
	 (fix-fn-unfix-check (safe-symbol (list fix-fn "_UNFIX_CHECK") fn-witness))
	 (fix-fn-unfix-check-reduction-1 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_1") fn-witness))
	 (fix-fn-unfix-check-reduction-2 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_2") fn-witness))
	 (fix-fn-unfix-check-reduction-3 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_3") fn-witness))
	 (wrapped-var      (safe-symbol (list var "-wrapped") var))
	 (wrapped-var?     (safe-symbol (list var "-wrapped?") var))
	 (wrapped-var-hyps (safe-symbol (list var "-wrapped-hyps") var))
	 )
    `(encapsulate
      ()

      (defun ,fix-fn-unfix (term ,@args wrapped unwrap hyp)
	(declare (ignore ,(ith (1- position) args)))
	(if (and (equal (len term) (1+ ,(len args)))
		 (equal (car term) ',fix-fn)
		 ,@(compare-args-to-term args 1 position 'term))
	    `((,wrapped . `t)
	      (,unwrap  . ,(ith ,position term))
	      (,hyp     . `t))
	  `((,wrapped . `nil)
	    (,unwrap  . ,term)
	    (,hyp     . `t))))

      (defun ,fix-fn-unfix-check (,wrapped-var? ,wrapped-var ,var ,wrapped-var-hyps ,@nargs)
	(declare (ignore ,wrapped-var-hyps ,(ith (1- position) nargs)))
	(if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@(replace-ith (1- position) var nargs)))
	  (equal ,wrapped-var ,var)))

      (defthm ,fix-fn-unfix-check-reduction-1
	(,fix-fn-unfix-check t (,fix-fn ,@(replace-ith (1- position) var nargs))
			     ,var ,wrapped-var-hyps ,@nargs))

      (defthm ,fix-fn-unfix-check-reduction-2
	(,fix-fn-unfix-check nil ,wrapped-var ,wrapped-var ,wrapped-var-hyps ,@nargs))

      (defthm ,fix-fn-unfix-check-reduction-3
	(implies
	 (in-conclusion-check (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,var ,wrapped-var-hyps ,@nargs))
	 (equal (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,var ,wrapped-var-hyps ,@nargs)
		(if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@(replace-ith (1- position) var nargs)))
		  (equal ,wrapped-var ,var)))))

      (in-theory (disable ,fix-fn-unfix-check))

      )))

(defmacro defcontext (term position)
  (defcontext-fn term position))

(defun locate (val list)
  (declare (type t val list))
  (if (consp list)
      (if (equal val (car list)) 0
	(1+ (locate val (cdr list))))
    0))


(defund imp (a x)
  (if x t a))

(defthm implies-imp
  (implies
   a
   (imp a x))
  :hints (("goal" :in-theory (enable imp))))

(set-state-ok t)

(defun appears-in-clause (fn args fapp clause)
  (declare (type t fn args clause))
  (if (consp clause)
      (if fapp
	  (or (and (equal fn (car clause))
		   (equal args (cdr clause)))
	      (appears-in-clause fn args nil (cdr clause)))
	(or (appears-in-clause fn args t (car clause))
	    (appears-in-clause fn args nil (cdr clause))))
    nil))

(defun in-conclusion-fn (term mfc state)
  (declare (ignore state)
	   (type t term))
  (if (not (acl2::mfc-ancestors mfc))
      (and (if (consp term) (appears-in-clause (car term) (cdr term) nil (acl2::mfc-clause mfc)) t)
	   (list (cons 'in-conclusion-free-variable `(quote t))))
    nil))

(defmacro in-conclusion ()
  `(bind-free (in-conclusion-fn nil acl2::mfc acl2::state)
	      (in-conclusion-free-variable)))

(defun quote-list (list)
  (declare (type t list))
  (if (consp list)
      (cons `(quote ,(car list))
	    (quote-list (cdr list)))
    nil))

(defun equal_len (n list)
  (declare (type (integer 0 *) n))
  (if (consp list)
      (if (zp n) nil
	(equal_len (1- n) (cdr list)))
    (and (null list) (= n 0))))

(defun syn__consp (term)
  (declare (type t term))
  (and
   (equal_len 3 term)
   (equal (car term) 'cons)))

(defun syn__cdr (term)
  (declare (type (satisfies syn__consp) term))
  (caddr term))

(defun syn__car (term)
  (declare (type (satisfies syn__consp) term))
  (cadr term))

(defun syn__quotep (term)
  (declare (type t term))
  (and (equal_len 2 term)
	     (equal (car term) 'quote)))

(defun syn__dequote (term)
  (declare (type (satisfies syn__quotep) term))
  (cadr term))

(defun delist (args)
  (declare (type t args))
  (cond
   ((syn__consp args)
    (cons (syn__car args)
	  (delist (syn__cdr args))))
   ((syn__quotep args)
    (quote-list (syn__dequote args)))
   (t
    nil)))

(defun in-conclusion-check-fn (fn args mfc state)
  (declare (ignore state)
	   (type t args))
  (if (not (acl2::mfc-ancestors mfc))
      (let ((args (delist args)))
	(and (appears-in-clause fn args nil (acl2::mfc-clause mfc))
	     (list (cons 'in-conclusion-free-variable `(quote t)))))
    nil))

(defmacro in-conclusion-check (term)
  (declare (xargs :guard (consp term)))
  `(and
    (equal in-conclusion-check-term (list ,@(cdr term)))
    (bind-free (in-conclusion-check-fn ',(car term) in-conclusion-check-term acl2::mfc acl2::state)
	       (in-conclusion-free-variable))))

(defthm open-imp-in-conclusion
  (implies
   (in-conclusion-check (imp a x))
   (equal (imp a x) (if x t a)))
  :hints (("Goal" :in-theory (enable imp))))

(defmacro => (x a)
  `(iff ,x (imp ,a (hide ,x))))

(defun remove-any-keywords (list)
  (if (consp list)
      (if (and (symbolp (car list))
	       (in-pkg-of (car list) :key))
	  (remove-any-keywords (cdr list))
	(cons (car list)
	      (remove-any-keywords (cdr list))))
    nil))

(defun generate-cong-hyp (p cong)
  (declare (xargs :mode :program))
  (let* ((ovar  (car cong))
	 (eex   (cadr cong))
	 (equiv (car eex))
	 (nvar  (cadr eex))
	 (exp   (caddr eex)))
    (let* ((ctx-fn        (car exp))
	   (fn-witness    (fn-witness ctx-fn))
	   (fix-args      (remove-any-keywords (cdr exp)))
	   (fix-fn-unfix  (safe-symbol (list ctx-fn "_UNFIX") fn-witness))
	   (fix-fn-unfix-check  (safe-symbol (list ctx-fn "_UNFIX_CHECK") fn-witness))
	   (var-wrapped?  (safe-symbol (list ovar "-wrapped?")  ovar))
	   (var-hyps      (safe-symbol (list ovar "-hyps")  ovar))
	   (unwrapped-var (safe-symbol (list ovar "-unwrapped") ovar))
	   (wrapped-var           (safe-symbol (list nvar "-wrapped")   nvar))
	   (wrapped-var-hyps      (safe-symbol (list nvar "-wrapped-hyps")   nvar))
	   (wrapped-var-wrapped?  (safe-symbol (list nvar "-wrapped?")  nvar))
	   (unwrapped-wrapped-var nvar)
	   )
      `(
	,@
	(and (not p)
	     `((bind-free (,fix-fn-unfix ,ovar ,@fix-args ',var-wrapped? ',unwrapped-var ',var-hyps)
			  (,var-wrapped? ,unwrapped-var ,var-hyps))))

	;; var-wrapped => (ovar == (fn .. unwrapped-var ..))

	;; We now ask ACL2 to rewrite under the new context .. if the bound
	;; variable was not already in such a context.

	,(cond
	  (p      `(,equiv ,wrapped-var ,exp))
	  ((not (equal equiv 'equal))
	          `(,equiv ,wrapped-var (double-rewrite (if ,var-wrapped? ,ovar ,exp))))
	  (t      `(,equiv ,wrapped-var (if ,var-wrapped? ,ovar ,exp))))

	(bind-free (,fix-fn-unfix ,wrapped-var ,@fix-args ',wrapped-var-wrapped? ',unwrapped-wrapped-var ',wrapped-var-hyps)
		   (,wrapped-var-wrapped? ,unwrapped-wrapped-var ,wrapped-var-hyps))

	;; wrapped-var-wrapped? => (wrapped-var == (fn .. unwrapped-wrapped-var ..))

	;; After rewriting in the new context, we evaluate the resulting term.
	;; If the term is still (syntactically) wrapped in the context, we
	;; remove the context.

	;; Of course, we have to justify our actions when we remove the
	;; syntactic wrapper.  To avoid re-rewriting the term, we have defined
	;; fix-fn-unfix-check, which knows how to compare the new term with the
	;; expected value without actually re-wrapping it in the context.

	(,fix-fn-unfix-check ,wrapped-var-wrapped? ,wrapped-var ,unwrapped-wrapped-var ,wrapped-var-hyps ,@fix-args)

	)

      )))

(defun wrapped-hyp (cong)
  (declare (xargs :mode :program))
  (let* ((eex   (cadr cong))
	 (nvar  (cadr eex)))
    (let* ((wrapped-var-wrapped?  (safe-symbol (list nvar "-wrapped?")  nvar)))
      wrapped-var-wrapped?)))

(defun wrapped-hyps (congs)
  (declare (xargs :mode :program))
  (if (consp congs)
      (cons (wrapped-hyp (car congs))
	    (wrapped-hyps (cdr congs)))
    nil))

(defun generate-asymmetric-hyps (congs)
  (declare (xargs :mode :program))
  `(and ,@(wrapped-hyps congs)))

(defun generate-cong-hyps (p congs)
  (declare (xargs :mode :program))
  (if (consp congs)
      (append (generate-cong-hyp p (car congs))
	      (generate-cong-hyps p (cdr congs)))
    nil))

(defun generate-cong-syntax-hyp (cong)
  (let* ((ovar (car cong))
	 (eex  (cadr cong))
	 (nvar (cadr eex)))
    `(not (equal ,ovar ,nvar))))

(defun generate-cong-syntax-hyps-rec (congs)
  (if (consp congs)
      (cons (generate-cong-syntax-hyp (car congs))
	    (generate-cong-syntax-hyps-rec (cdr congs)))
    nil))

(defun generate-cong-syntax-hyps (congs)
  `(syntaxp (or ,@(generate-cong-syntax-hyps-rec congs))))

(defun cong-equivs (congs)
  (declare (xargs :mode :program))
  (if (consp congs)
      (let ((cong (car congs)))
	(let ((eex (cadr cong)))
	  (let (;(equiv (car eex))
		(term (caddr eex)))
	    (let ((fix-fn (car term)))
	      (cons (safe-symbol (list fix-fn "_EQUIV")
			       (fn-witness fix-fn))
		    (cong-equivs (cdr congs)))))))
    nil))

(defmacro bind-context (cong)
  (declare (xargs :guard (or (wf-cong-list cong)
			     (wf-cong cong))))
  (let ((cong (if (wf-cong-list cong) cong (list cong))))
    `(and ,@(generate-cong-hyps nil cong)
	  ,(generate-cong-syntax-hyps cong))))

(defmacro bind-contextp (cong)
  (declare (xargs :guard (or (wf-cong-list cong)
			     (wf-cong cong))))
  (let ((cong (if (wf-cong-list cong) cong (list cong))))
    `(and ,@(generate-cong-hyps t cong)
	  ,(generate-cong-syntax-hyps cong))))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; The defequiv+ macro extends the notion of equivalance relations to
;; include arbitrary boolean relations.  In particular, we want to be
;; able to rewrite a term while preserving the truth of some boolean
;; relation.  Usually, this involves making the term "more true" such
;; as by rewriting the set {a,b} into {a,b,c} preserving (subset x {a
;; b}).  The macro accepts a predicate term expression and a number of
;; keywords as below:
;;
;; (defequiv+
;;  (< n x)
;;  :rhs     n
;;  :pred    <-pred
;;  :context <-ctx
;;  :equiv   <-equiv
;;  )
;;
;; The :rhs term identifies which variable in the predicate expression
;; will be construed as the rewritten term.  If left blank, we assume
;; a binary relation and we use the second argument.
;;
;; The name of the "equivlance relation" constructed by the macro can
;; be specified by the user via the :equiv keyword.  By default it is
;; computed from the leading function symbol of the provided term by
;; concatenating it with "_EQUIV".  Note, however, that the generated
;; "equivalence relation" is merely a macro that expands into an
;; equality between two predicates.  Thus, the equivalance relation
;; should only be used to define rewrite rules and not be used to
;; express hypotheses.
;;
;; Rules expressed in terms of the generated equivalence relation will
;; key off of (will rewrite) :context expressions.  The user can
;; supply the name of the :context via the macro keyword, or it will
;; be computed from the leading function symbol of the provided term
;; by concatenating it with "_CTX".  When using defequiv+ terms in
;; conjunction with defcong+, we express the congruences as:
;;
;; :cong ((z (<-ctx v)))
;;
;; Which is to say, we place the terms we want to rewrite in the
;; :context in which we want them rewritten.
;;
;; The :pred keyword can be used to specify the name of a function
;; defined to be exactly the term supplied to the macro.  This
;; function helps to differentiate "rewrite" rules associated with the
;; relation from predicate rules that hang on the relation itself.
;; Such rules can otherwise cause the "equivlalence" rewriting to
;; result in "TRUE" which turns out to be not particularly useful for
;; our purposes.
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defun replace-term (x y list)
  (declare (type t x y list))
  (if (consp list)
      (if (equal (car list) x)
	  (cons y (cdr list))
	(cons (car list) (replace-term x y (cdr list))))
    nil))

(defun make-keyargs (args)
  (if (consp args)
      (cons `(,(car args) ',(car args))
	    (make-keyargs (cdr args)))
    nil))

(defun bind-keyargs (args)
  (if (consp args)
      (cons (intern-in-package-of-symbol (symbol-name (car args)) :key)
	    (cons (car args)
		  (bind-keyargs (cdr args))))
    nil))

(defun defequiv-fun (term lhs rhs pred context equiv chaining keywords)
  (declare (xargs :mode :program))
  (let* ((context-macro (if keywords context (safe-symbol (list context "-macro") context)))
	 (context-fn    (if keywords (safe-symbol (list context "-fn") context) context))
	 (context       (if keywords context-macro context-fn))
	 (fn-witness   (fn-witness (if pred pred (car term))))
	 (fix-fn       (or pred (safe-symbol (list (car term) "-pred") fn-witness)))
	 (hyps         (safe-symbol (list fix-fn "-backchain-hyps") fn-witness))
	 (args         (cons hyps (cdr term)))
	 (args--       (cdr term))
	 (lhs-args     (remove rhs args))
	 (lhs-args--   (remove rhs args--))
	 (new-rhs      (safe-symbol (list rhs "_replacement") fn-witness))
	 (rhs-args--   (replace-term rhs new-rhs args--))
	 (lhs-rhs--    (replace-term lhs rhs lhs-args--))
	 (macroargs    (replace-term lhs 'lhs (replace-term rhs 'rhs args--)))
	 (keyargs      (make-keyargs macroargs))
	 (fix-fn-unfix (safe-symbol (list context "_UNFIX") fn-witness))
	 (fix-fn-unfix-check (safe-symbol (list context "_UNFIX_CHECK") fn-witness))
	 (fix-fn-unfix-check-reduction-1 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_1") fn-witness))
	 (fix-fn-unfix-check-reduction-2 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_2") fn-witness))
	 (fix-fn-unfix-check-reduction-3 (safe-symbol (list fix-fn-unfix-check "_REDUCTION_3") fn-witness))
	 (fix-fn-context-reduction (safe-symbol (list context "_REDUCTION") fn-witness))
	 (wrapped-var  (safe-symbol (list rhs "-wrapped") fn-witness))
	 (wrapped-var? (safe-symbol (list rhs "-wrapped?") fn-witness))
	 (fix-fn-chaining  (safe-symbol (list fix-fn "-CHAINING") fn-witness))
	 )
    `(encapsulate
      ()

      (set-ignore-ok t)
      (SET-IRRELEVANT-FORMALS-OK t)

      (defun ,context-fn (,@lhs-args--)
	t)

      (defmacro ,context-macro (,lhs &key ,@(make-keyargs (remove lhs lhs-args--)))
	`(,',context-fn ,@(list ,@lhs-args--)))

      (defthm ,fix-fn-context-reduction
	(implies
	 (in-conclusion-check (,context-fn ,@lhs-args--))
	 (equal (,context-fn ,@lhs-args--) t)))

      (in-theory (disable (:type-prescription ,context-fn) ,context-fn (,context-fn)))

      (defund ,fix-fn (,@args)
	(if (not ,hyps) nil (not (not ,term))))

      (in-theory (disable (:type-prescription ,fix-fn) (,fix-fn)))

      (defthm ,(safe-symbol (list fix-fn "-OPEN") fix-fn)
	(implies
	 (in-conclusion-check (,fix-fn ,@args))
	 (equal (,fix-fn ,@args)
		(if (not ,hyps) nil (not (not ,term)))))
	:hints (("Goal" :in-theory (enable ,fix-fn))))

      (defun ,fix-fn-unfix (term ,@lhs-args-- wrapped unwrap hyp)
	(declare (type t term))
	(and (consp term)
	     (cond
	      ((equal (car term) ',fix-fn)
	       `((,wrapped . 't)
		 (,unwrap  . ,(ith ,(1+ (locate rhs term)) term))
		 (,hyp     . ,(ith 1 term))))
	      ((equal (car term) ',context-fn)
	       `((,wrapped . 'nil)
		 (,unwrap  . ,,lhs)
		 (,hyp     . 't)))
	      ((equal term '(quote t))
	       (cw "~%Boolean Binding reduced ~p0 to TRUE~%" ',fix-fn))
	      (t
	       (cw "~%Boolean Binding Failure on returned term:~%~p0~%" term)))))

      ;;
      ;; Note that this includes the "hyp" parameter in lhs-args ..
      ;;
      (defun ,fix-fn-unfix-check (,wrapped-var? ,wrapped-var ,rhs ,@lhs-args)
	(if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@args))
	  (equal ,rhs ,lhs)))

      (defthm ,fix-fn-unfix-check-reduction-1
	(implies
	 (in-conclusion-check (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,rhs ,@lhs-args))
	 (equal (,fix-fn-unfix-check ,wrapped-var? ,wrapped-var ,rhs ,@lhs-args)
		(if ,wrapped-var? (equal ,wrapped-var (,fix-fn ,@args))
		  (equal ,rhs ,lhs)))))

      (defthm ,fix-fn-unfix-check-reduction-2
	(,fix-fn-unfix-check t (,fix-fn ,@args) ,rhs ,@lhs-args))

      (defthm ,fix-fn-unfix-check-reduction-3
	(,fix-fn-unfix-check nil ,wrapped-var ,lhs ,@lhs-args))

      (in-theory (disable ,fix-fn-unfix-check))

      (defmacro ,equiv ,(if keywords `(&key (hyp 'nil) (skip 'nil) ,@keyargs) `(,@macroargs &key (hyp 'nil) (skip 'nil)))
	(let ((,lhs lhs)
	      (,rhs rhs))
	  (let ((hyp (if hyp `(hide ,hyp) `t)))
	    `(equal (,',context-fn ,@(list ,@lhs-args--))
		    ,(if skip
			 `(skip-rewrite (,',fix-fn ,hyp ,@(list ,@args--)))
		       `(,',fix-fn ,hyp ,@(list ,@args--)))))))

      ,@(and chaining
	     `(
	       (defthm ,fix-fn-chaining
		 (implies
		  (bind-contextp (,rhs (equal ,new-rhs ,(if keywords
							    `(,context-macro ,rhs ,@(bind-keyargs (remove rhs lhs-rhs--)))
							  `(,context ,@lhs-rhs--)))))
		  (equal (,fix-fn ,@args)
			 (,fix-fn (hide (,fix-fn ,@args)) ,@rhs-args--)))
		 :hints (("Goal" :expand (:free (x) (hide x)))))
	       ))

      )))

(defmacro defequivp+ (term &key  (lhs 'nil) (rhs 'nil) (pred 'nil) (context 'nil)
			   (equiv 'nil) (chaining 't) (keywords 'nil))
  (declare (xargs :guard (and (symbolp lhs)
			      (symbolp rhs)
			      (symbolp pred)
			      (symbolp context)
			      (symbolp equiv)
			      (implies
			       (not rhs)
			       (= (len term) 3))
			      (implies rhs (member rhs term))
			      (<= 3 (len term))
			      (symbol-listp term))))
  (let* ((pred-fn  (or pred    (ith 0 term)))
	 (equiv    (or equiv   (safe-symbol (list pred-fn "-EQUIV") pred-fn)))
	 (lhs      (or lhs     (ith 1 term)))
	 (rhs      (or rhs     (ith 2 term)))
	 (context  (or context (safe-symbol (list pred-fn "-CTX") pred-fn))))
    (defequiv-fun term lhs rhs pred context equiv chaining keywords)))

;; Depricated
(defmacro defequiv+ (&rest args)
  `(defequivp+ ,@args))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; The defcong+ macro defines a single theorem which causes ACL2 to
;; push one or more "contexts" into specific argument locations of an
;; expression and then remove them.
;;
;; The expression:
#|
(defcong+ mod-+-cong

  (mod (+ a b) n)

  :hyps (and
	     (rationalp n)
	     (rationalp a)
	     (rationalp b)
	     (not (equal n 0)))
  :cong ((a (equal x (mod a n)))
	 (b (equal y (mod b n))))
  :check (and (rationalp x)
	      (rationalp y))
  :hints (("goal" :in-theory (enable mod-+-fixpoint-helper)))
  )
|#
;;
;; Tells us that we will be considering terms of the form (mod (+ a b)
;; n).  The :hyps are the hypothesis under which this operation is
;; allowed.  The :cong term tell us to rewrite (mod (+ a b) n) into
;; (mod (+ x y) n) as follows: the "a" term of (mod (+ a b) n)
;; rewrites into "x" using the context (mod _ n) and the "b" term
;; rewrites into "y" using the context (mod _ n).  When we have done
;; this simplification, check the :check conditions to make sure the
;; resulting terms justify this transformation.  Perform the proof
;; using the supplied :hints.
;;
;; defcongp+ creates a theorem context in which ACL2 will appear to
;; rewrite terms while preserving a boolean context.  From a user's
;; perspective, the primary difference between defcong+ and defcongp+
;; is that the latter supports a "rhs" keyword that allows the RHS of
;; the rule to differ substantially from the LHS.  The formulation of
;; the RHS term should reflect the substitution hinted at by the :cong
;; relations provided.  In the case below, this means replacing the
;; variable "list" by "z".
;;
#|
(defcongp+ <-pred-memberp=>

  (bag::memberp x list)

  :rhs (bag::memberp x z)

  :hyps (and
	 (syntaxp (not (cw "Here"))))

  :cong ((list (equal z (<-pred list list))))

  :equiv =>

  :hints (("goal" :expand (:free (x) (hide x))
	   :in-theory (enable <-pred_equiv <-pred)))
  )
|#
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(defmacro defcong+ (name term &key (hyps 'nil) (cong 'nil) (check 'nil) (hints 'nil) (equiv 'equal))
  (declare (type (satisfies wf-cong-list) cong))

  `(defthm ,name
     (implies
      (and

       ;; This bad boy is supposed to help stop us from calling ourselves
       ;; recursively on the rewritten RHS of this theorem.  When it works, it
       ;; reduces the cost of this rule from quardratic to linear.
       ;; Unfortunately, it only works when :Brr is enabled.  Help!

       ;; (bind-free (non-recursive ',name acl2::mfc acl2::state) (ok))

       ;; Check the hyps

       ,@(if hyps `(,hyps) nil)

       ;; Simplify selected arguments in their new context

       ,@(generate-cong-hyps nil cong)

       ;; See if anything has changed ..

       ,(generate-cong-syntax-hyps cong)

       ;; Check the types of our results

       ,@(if check `(,check) nil))
      (,equiv ,term
	      (skip-rewrite ,(replace-cong-terms cong term))))
     ,@(if hints `(:hints ,hints) nil)
     ;;`(:hints (("Goal" :in-theory (enable ,@(cong-equivs cong)))))))
     )
  )

(defmacro defcongp+ (name term &key (rhs 'nil) (hyps 'nil) (cong 'nil) (check 'nil) (hints 'nil) (equiv 'equal))
  (declare (type (satisfies wf-cong-list) cong))

  `(defthm ,name
     (implies
      (and

       ;; This bad boy is supposed to help stop us from calling ourselves
       ;; recursively on the rewritten RHS of this theorem.  When it works, it
       ;; reduces the cost of this rule from quardratic to linear.
       ;; Unfortunately, it only works when :Brr is enabled.  Help!

       ;; (bind-free (non-recursive ',name acl2::mfc acl2::state) (ok))

       ;; Check the hyps

       ,@(if hyps `(,hyps) nil)

       ;; Simplify selected arguments in their new context

       ,@(generate-cong-hyps t cong)

       ,@(and rhs (generate-asymmetric-hyps cong))

       ;; See if anything has changed ..

       ,(generate-cong-syntax-hyps cong)

       ;; Check the types of our results

       ,@(if check `(,check) nil)
       )

      (,equiv ,term
	      ,(if (not rhs) (replace-cong-terms cong term)
		 rhs)))
     ,@(if hints `(:hints ,hints) nil)
     ;; `(:hints (("Goal" :in-theory (enable ,@(cong-equivs cong)))))))
     )
  )
