;; Copyright (C) 2015, University of British Columbia
;; Written by Chris Chen (May 2024)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/osets/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "tterm-change")
(include-book "tterm-clause-cp")
(include-book "returns-judgement")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

(local (in-theory (e/d
  (ev-smtcp-of-fncall-args)
  (pseudo-termp pseudo-term-listp symbol-listp  ; Mark is impatient
   boolean-listp member-equal consp-of-pseudo-lambdap
   pseudo-lambdap-of-fn-call-of-pseudo-termp lambda-of-pseudo-lambdap
   default-car
   (:type-prescription pseudo-lambdap)))))

;; Utility functions from old-bottom-up
(define judge-ev-lst ((lst judge-list-p) (term pseudo-termp) (a alistp))
  :returns (x true-listp)
  (if (consp lst)
    (cons (judge-ev (car lst) term a)
	  (judge-ev-lst (cdr lst) term a))
    nil)
  ///
  (more-returns
    (x :name judge-ev-list-when-consp
      (implies (consp lst)
	(equal x (cons (judge-ev (car lst) term a)
		       (judge-ev-lst (cdr lst) term a)))))
    (x :name judge-ev-list-of-atom
      (implies (not (consp lst)) (not x)))))

(define parse-conjunct-helper
    ((term pseudo-termp) (acc pseudo-term-listp))
  :returns (conjuncts pseudo-term-listp)
  :verify-guards nil
  (b* ((term (pseudo-term-fix term))
       (acc (pseudo-term-list-fix acc))
       ((if (equal term ''t)) acc)
       ((unless (and (consp term) (consp (cdr term)) (consp (cddr term))
		     (consp (cdddr term)) (not (cddddr term))
		     (equal (car term) 'if)
		     (equal (cadddr term) ''nil)))
	(cons term acc))
       (condx (cadr term))
       (thenx (caddr term)))
    (parse-conjunct-helper
     thenx
     (parse-conjunct-helper condx acc)))
  ///
  (verify-guards parse-conjunct-helper)

  (more-returns
    (conjuncts :name correctness-of-parse-conjunct-helper
      (equal (all-list<pseudo-term-ev> conjuncts a)
	     (and (ev-smtcp (pseudo-term-fix term) a)
		  (ev-and-list (pseudo-term-list-fix acc) a)))
      :hints(("Goal"
	:in-theory (e/d (parse-conjunct-helper pseudo-term-ev)
			(pseudo-term-list-equiv-implies-equal-ev-and-list-1)))))))

(define parse-conjunct ((term pseudo-termp))
  :returns pset
  (std::mergesort (parse-conjunct-helper term nil))
  ///
  (more-returns
    (pset :name pseudo-term-set-p-of-parse-conjunct
      (pseudo-term-set-p pset))

    (pset :name correctness-of-parse-conjunct
      (iff (all<pseudo-term-ev> pset a)
	   (ev-smtcp (pseudo-term-fix term) a)))))


(defines parse-judge
  :verify-guards nil
  :prepwork (
    (local (defrule lemma-quote
      (implies (and (pseudo-termp x) (equal (car x) 'quote))
	       (and (consp (cdr x)) (not (cddr x))))
      :in-theory (enable pseudo-termp))))
  :returns-hints(("Goal" :in-theory (enable judge-p judge-list-p)))

  (define parse-judge-term ((x pseudo-termp) (expr pseudo-termp))
    :returns (mv (erp booleanp) (new-term judge-p))
    :flag term
    (b* ((x (pseudo-term-fix x))
	 ((if (equal x expr)) (mv nil 'smt::x))
	 ((unless x) (mv nil x))
	 ((unless (consp x)) (mv t nil))
	 ((if (equal (car x) 'quote)) (mv nil x))
	 ((unless (symbolp (car x))) (mv t nil))
	 ((mv err-args arg-list) (parse-judge-args (cdr x) expr))
	 ((if err-args) (mv t nil)))
      (mv nil (cons (car x) arg-list))))

  (define parse-judge-args ((args pseudo-term-listp) (expr pseudo-termp))
    :returns (mv (erp booleanp) (new-args judge-list-p))
    :flag args
    (b* (((unless (consp args)) (mv nil nil))
	 ((cons hd tl) args)
	 ((mv err-hd new-hd) (parse-judge-term hd expr))
	 ((if err-hd) (mv t nil))
	 ((mv err-tl new-tl) (parse-judge-args tl expr))
	 ((if err-tl) (mv t nil)))
      (mv nil (cons new-hd new-tl))))
  ///
  (local (defrule guard-lemma
    (mv-let (erp new-args)
	    (parse-judge-args args expr)
	    (implies (not erp)
		     (equal (consp new-args) (consp args))))
    :in-theory (enable parse-judge-args)
    :induct (len args)))
  (verify-guards parse-judge-term)

  (local (encapsulate nil ; prepwork for correctness theorems
    (defrule parse-judge-args-when-atom
      (mv-let (erp new-args)
	      (parse-judge-args args expr)
	      (implies (not (consp args))
		       (and (not erp) (not new-args))))
      :in-theory (enable parse-judge-args))

    (defrule parse-judge-args-when-consp
      (b* (((mv erp new-args) (parse-judge-args args expr))
	   ((cons hd tl) args)
	   ((cons new-hd new-tl) new-args)
	   ((mv erp-hd na-hd) (parse-judge-term hd expr))
	   ((mv erp-tl na-tl) (parse-judge-args tl expr)))
	(implies (and (not erp) (consp args))
		 (and (not erp-hd)
		      (equal new-hd na-hd)
		      (not erp-tl)
		      (equal new-tl na-tl))))
      :in-theory (enable parse-judge-args)
      :induct (len args))

    (defrule consp-of-parse-judge-args
      (implies
	 (not (mv-nth 0 (parse-judge-args args expr)))
	 (equal (consp (mv-nth 1 (parse-judge-args args expr)))
		(consp args)))
      :in-theory (enable parse-judge-args)
      :induct (len args))

    (local (in-theory (enable parse-judge-term parse-judge-args judge-ev judge-ev-lst)))
    (defthm-parse-judge-flag
      (defthm correctness-lemma-term
	(mv-let (erp new-term)
		(parse-judge-term x expr)
		(implies (not erp)
			 (equal (judge-ev new-term expr a)
				(ev-smtcp (pseudo-term-fix x) a))))
	:flag term)

      (defthm correctness-lemma-args
	(mv-let (erp new-args)
		(parse-judge-args args expr)
		(implies (not erp)
			 (and (equal (judge-ev-lst new-args expr a)
				     (ev-smtcp-lst (pseudo-term-list-fix args) a))
			      (equal (ev-smtcp-lst new-args (cons (cons 'smt::x (ev-smtcp expr a)) nil))
				     (ev-smtcp-lst (pseudo-term-list-fix args) a)))))
	:flag args))
    (local (in-theory (disable parse-judge-term parse-judge-args judge-ev judge-ev-lst)))))

  (defrule correctness-of-parse-judge-term
    (mv-let (erp new-term)
	    (parse-judge-term x expr)
	    (implies (not erp)
		     (equal (judge-ev new-term expr a)
			    (ev-smtcp (pseudo-term-fix x) a)))))

  (defrule correctness-of-parse-judge-args
    (mv-let (erp new-args)
	    (parse-judge-args args expr)
	    (implies (not erp)
		     (iff (all-list<judge-ev> new-args expr a)
			  (all-list<pseudo-term-ev> args a))))
    :in-theory (enable all-list<judge-ev> all-list<pseudo-term-ev> pseudo-term-ev)
    :induct (pairlis$ args new-args)))

; an example -- change to use make-test
; (parse-judge-term
;   '(if (integerp (binary-+ x y))
;      (< '0 (binary-+ x y)))
;   '(binary-+ x y))

(define parse-judge-set((term pseudo-termp) (judge-pt pseudo-termp))
  :returns (jset judge-set-p)
  :guard-debug t
  (b* ((j-lst (parse-conjunct judge-pt))
       ((mv erp jx) (parse-judge-args j-lst term))
       ((if erp)
	(prog2$
	  (er hard? 'top-level
	      (concatenate 'string
			   "Badly formed judgements for term ~q0~%"
			   "  judgements ~q1~%")
	      term judge-pt jx)
	  '((smt::bad-judgement x)))))
    (std::mergesort jx))
  ///
  (more-returns
    (jset :name correctness-of-parse-judge-set
      (implies
	(not (equal jset '((bad-judgement x))))
	(iff (all<judge-ev> jset term a)
	     (ev-smtcp (pseudo-term-fix judge-pt) a))))))


(defines judge-flat-expr
  :returns-hints(("Goal" :in-theory (enable pseudo-termp)))
  :flag-local nil
  :verify-guards nil
  (define judge-flat-expr ((x judge-p) (expr pseudo-termp))
    :returns (x-flat pseudo-termp)
    :flag term
    (if (consp x)
	(if (equal (car x) 'quote)
	  (and (consp (cdr x)) (equal (cddr x) nil) x)
	  (and (symbolp (car x))
	       (cons (car x)
		     (judge-list-flat-expr (cdr x) expr))))
	(and (equal x 'x) (pseudo-term-fix expr))))

  (define judge-list-flat-expr ((lst judge-list-p) (expr pseudo-termp))
    :returns (lst-flat pseudo-term-listp)
    :flag list
    (if (consp lst)
	(cons (judge-flat-expr (car lst) expr)
	      (judge-list-flat-expr (cdr lst) expr))
	nil))
  ///
  (verify-guards judge-flat-expr
    :hints(("Goal" :in-theory (enable judge-p))))

  (local (in-theory (enable judge-flat-expr judge-list-flat-expr judge-p judge-ev judge-ev-lst)))
  (local (defrule lemma-1
    (implies (and (judge-list-p lst) (pseudo-termp expr))
      (equal (judge-ev-lst lst expr a)
	     (ev-smtcp-lst lst (list (cons 'x (ev-smtcp expr a))))))))

  (defthm-judge-flat-expr-flag
    (defthm correctness-of-judge-flat-expr
       (implies (and (judge-p x) (pseudo-termp expr))
		(equal (ev-smtcp (judge-flat-expr x expr) a)
		       (judge-ev x expr a)))
       :flag term)
    (defthm correctness-of-judge-list-flat-expr
       (implies (and (judge-list-p lst) (pseudo-termp expr))
		(equal (ev-smtcp-lst (judge-list-flat-expr lst expr) a)
		       (judge-ev-lst lst expr a)))
      :flag list)))

(define args->judgements-expr ((args tterm-list-p))
  :returns (judge-expr pseudo-termp)
  (if (consp args)
    (and-expr
      (and-list-expr (judge-list-flat-expr (tterm->judgements (car args))
					   (tterm->expr (car args))))
      (args->judgements-expr (cdr args)))
    ''t)
  ///
  (defrule ev-smtcp-of-args->judgements-expr
    (implies (and (tterm-list-correct-p args a)
		  (args->path-cond-ev args a))
	     (ev-smtcp (args->judgements-expr args) a))
    :in-theory (enable args->judgements-expr args->path-cond-ev ev-and)
    :prep-lemmas (
      (defrule lemma-1
	(implies
	  (and (judge-list-p j) (pseudo-termp expr))
	  (equal
	    (and-list (judge-ev-lst j expr a))
	    (all-list<judge-ev> j expr a)))
	:rule-classes (
	  (:rewrite :corollary (implies (and (judge-set-p j) (pseudo-termp expr))
					(equal (and-list (judge-ev-lst j expr a))
					       (all<judge-ev> j expr a))))))

      (defrule lemma-2
	(implies
	  (pseudo-term-listp lst)
	  (equal (all-list<pseudo-term-ev> lst a)
		 (and-list (ev-smtcp-lst lst a))))
	  :in-theory (enable and-list pseudo-term-ev))

      (defrule lemma-3
	(let ((j (tterm->judgements tterm))
	      (expr (tterm->expr tterm)))
	  (equal (ev-smtcp (and-list-expr (judge-list-flat-expr j expr)) a)
		 (tterm->judgements-ev tterm a)))
	:expand ((tterm->judgements-ev tterm a))))))

;; --- top-town-continues

(defval *top-down-priority*
  '((rationalp smt::x)
    (integerp smt::x)
    (natp smt::x)
    (booleanp smt::x)
    (symbolp smt::x)
    (maybe-int-sym-consp smt::x)
    (int-sym-consp smt::x)
    (int-sym-alist-p smt::x)
    (int-sym-array-p smt::x)
    (maybe-nat-sym-consp smt::x)
    (nat-sym-consp smt::x)
    (nat-sym-alist-p smt::x)
    (nat-sym-array-p smt::x)))


(defval *bool-judgement*
  (set::insert (judge-fix '(booleanp smt::x))
               '()))


(defines top-down-precond-p
  :verify-guards nil
  :well-founded-relation l<

  (define top-down-args-precond-p ((args tterm-list-p))
    :measure (list (tterm-list->expr-list-count args) 1 0)
    :returns (ok booleanp)
    (b* ((args (tterm-list-fix args))
	 ((if (endp args)) t)
	 ((if (consp args))
	  (and (top-down-precond-p (car args))
	       (top-down-args-precond-p (cdr args)))))
      nil))

  (define top-down-precond-p ((tterm tterm-p))
    :measure (list (tterm->expr-count tterm) 2 0)
    :returns (ok booleanp)
    (b* ((tterm (tterm-fix tterm))
	 ((unless (set::emptyp (tterm->smt-judgements tterm)))
          nil))
      (case (tterm->kind tterm)
	(:quote t)
	(:var t)
	(:if (and (top-down-precond-p (tterm->condx tterm))
		  (top-down-precond-p (tterm->thenx tterm))
		  (top-down-precond-p (tterm->elsex tterm))))
	(:fncall (top-down-args-precond-p (tterm->args tterm))))))
  ///
  (verify-guards top-down-precond-p)
  (fty::deffixequiv-mutual top-down-precond-p))


(defines top-down-postcond-p
  :verify-guards nil
  :well-founded-relation l<

  (define top-down-args-postcond-p ((args1 tterm-list-p)
			     (args2 tterm-list-p))
    :measure (list (tterm-list->expr-list-count args1) 1 0)
    :returns (ok booleanp)
    (b* ((args1 (tterm-list-fix args1))
	 (args2 (tterm-list-fix args2))
	 ((if (and (endp args1)
		   (endp args2)))
	  t)
	 ((if (and (consp args1)
		   (consp args2)))
	  (and (top-down-postcond-p (car args1)
			     (car args2))
	       (top-down-args-postcond-p (cdr args1)
				  (cdr args2)))))
      nil))

  (define top-down-postcond-p ((tt1 tterm-p)
			(tt2 tterm-p))
    :measure (list (tterm->expr-count tt1) 2 0)
    :returns (ok booleanp)
    (b* ((tt1 (tterm-fix tt1))
	 (tt2 (tterm-fix tt2))
	 ((unless (and (tterm->kind-equiv tt1 tt2)
		       (tterm->path-cond-equiv tt1 tt2)
		       (tterm->judgements-equiv tt1 tt2)
		       (set::subset (tterm->smt-judgements tt2)
				    (tterm->judgements tt1))))
	  nil))
      (case (tterm->kind tt1)
	(:quote (tterm->val-equiv tt1 tt2))
	(:var (tterm->name-equiv tt1 tt2))
	(:if (and (top-down-postcond-p (tterm->condx tt1)
				(tterm->condx tt2))
		  (top-down-postcond-p (tterm->thenx tt1)
				(tterm->thenx tt2))
		  (top-down-postcond-p (tterm->elsex tt1)
				(tterm->elsex tt2))))
	(:fncall (and (tterm->f-equiv tt1 tt2)
		      (top-down-args-postcond-p (tterm->args tt1)
					 (tterm->args tt2)))))))
  ///
  (verify-guards top-down-postcond-p)
  (fty::deffixequiv-mutual top-down-postcond-p)

  (defthm-top-down-postcond-p-flag
    (defthm top-down-args-postcond-p-expr-path-equivs
      (implies (top-down-args-postcond-p args1 args2)
	       (and (tterm-list->expr-list-equiv args1 args2)
		    (tterm-list->path-cond-equiv args1 args2)))
      :flag top-down-args-postcond-p
      :rule-classes :forward-chaining)
    (defthm top-down-postcond-p-expr-path-equivs
      (implies (top-down-postcond-p tt1 tt2)
	       (and (tterm->expr-equiv tt1 tt2)
		    (tterm->path-cond-equiv tt1 tt2)))
      :flag top-down-postcond-p
      :rule-classes :forward-chaining)
    :hints (("Goal"
	      :expand ((top-down-postcond-p tt1 tt2)
		       (top-down-args-postcond-p args1 args2))
	      :in-theory (enable tterm->path-cond-equiv
			         tterm->path-cond
			         tterm->expr-equiv
			         tterm->expr))))

  (local
   (defrule top-down-postcond-p-fncall-expr-equiv
     (implies (and (top-down-args-postcond-p (tterm->args tt1)
				             (tterm->args tt2))
		   (tterm->kind-equiv tt1 tt2)
		   (equal (tterm->kind tt1) :fncall)
		   (tterm->f-equiv tt1 tt2))
	      (tterm->expr-equiv tt1 tt2))
     :in-theory (enable tterm->expr-equiv
		        tterm->expr)
     :rule-classes :forward-chaining))

  (local
   (defrule top-down-postcond-p-if-expr-equiv
    (implies (and (top-down-postcond-p (tterm->condx tt1)
				(tterm->condx tt2))
		  (top-down-postcond-p (tterm->thenx tt1)
				(tterm->thenx tt2))
		  (top-down-postcond-p (tterm->elsex tt1)
				(tterm->elsex tt2))
		  (tterm->kind-equiv tt1 tt2)
		  (equal (tterm->kind tt1) :if))
	     (tterm->expr-equiv tt1 tt2))
    :in-theory (enable tterm->expr-equiv
		       tterm->expr)
    :rule-classes :forward-chaining))

  (local
   (defrule top-down-postcond-p-var-expr-equiv
    (implies (and (tterm->kind-equiv tt1 tt2)
		  (equal (tterm->kind tt1) :var)
		  (tterm->name-equiv tt1 tt2))
	     (tterm->expr-equiv tt1 tt2))
    :in-theory (enable tterm->expr-equiv
		       tterm->expr)
    :rule-classes :forward-chaining))

  (local
   (defrule top-down-postcond-p-quote-expr-equiv
    (implies (and (tterm->kind-equiv tt1 tt2)
		  (equal (tterm->kind tt1) :quote)
		  (tterm->val-equiv tt1 tt2))
	     (tterm->expr-equiv tt1 tt2))
    :in-theory (enable tterm->expr-equiv
		       tterm->expr)
    :rule-classes :forward-chaining))

  (local
   (defrule top-down-postcond-p-smt-judgements-ev
    (implies (and (tterm->judgements-ev tt1 a)
		  (set::subset (tterm->smt-judgements tt2)
			       (tterm->judgements tt1))
		  (tterm->expr-equiv tt1 tt2))
	     (tterm->smt-judgements-ev tt2 a))
    :in-theory (e/d (tterm->judgements-ev
		     tterm->smt-judgements-ev
		     all-subset<judge-ev>)
		    (all-strategy<judge-ev>))))

  (local
   (defrule top-down-postcond-p-fncall-inductive-case
    (implies (and (tterm->kind-equiv tt1 tt2)
		  (tterm->path-cond-equiv tt1 tt2)
		  (tterm->judgements-equiv tt1 tt2)
		  (set::subset (tterm->smt-judgements tt2)
			       (tterm->judgements tt1))
		  (equal (tterm->kind tt1) :fncall)
		  (tterm->f-equiv tt1 tt2)
		  (tterm-list-correct-p (tterm->args tt2)
					a)
		  (tterm-correct-p tt1 a)
		  (top-down-args-postcond-p (tterm->args tt1)
				     (tterm->args tt2)))
	     (tterm-correct-p tt2 a))
    :expand ((tterm-correct-p tt1 a)
	     (tterm-correct-p tt2 a))
    :in-theory (e/d (top-down-postcond-p-fncall-expr-equiv
		     top-down-postcond-p-smt-judgements-ev)
		    (tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))
    :use ((:instance tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))))

  (local
   (defrule top-down-postcond-p-if-inductive-case
    (implies (and (tterm->kind-equiv tt1 tt2)
		  (tterm->judgements-equiv tt1 tt2)
		  (set::subset (tterm->smt-judgements tt2)
			       (tterm->judgements tt1))
		  (equal (tterm->kind tt1) :if)
		  (top-down-postcond-p (tterm->condx tt1)
				(tterm->condx tt2))
		  (top-down-postcond-p (tterm->thenx tt1)
				(tterm->thenx tt2))
		  (tterm-correct-p (tterm->condx tt2)
				   a)
		  (tterm-correct-p (tterm->thenx tt2)
				   a)
		  (tterm-correct-p (tterm->elsex tt2)
				   a)
		  (tterm-correct-p tt1 a)
		  (tterm->path-cond-equiv tt1 tt2)
		  (top-down-postcond-p (tterm->elsex tt1)
				(tterm->elsex tt2)))
	     (tterm-correct-p tt2 a))
    :expand ((tterm-correct-p tt1 a)
	     (tterm-correct-p tt2 a))
    :in-theory (e/d (top-down-postcond-p-if-expr-equiv
		     top-down-postcond-p-smt-judgements-ev)
		    (tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))
    :use ((:instance tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))))

  (local
   (defrule top-down-postcond-p-var-case
    (implies (and (tterm->kind-equiv tt1 tt2)
		  (tterm->judgements-equiv tt1 tt2)
		  (set::subset (tterm->smt-judgements tt2)
			       (tterm->judgements tt1))
		  (equal (tterm->kind tt1) :var)
		  (tterm-correct-p tt1 a)
		  (tterm->path-cond-equiv tt1 tt2)
		  (tterm->name-equiv tt1 tt2))
	     (tterm-correct-p tt2 a))
    :expand ((tterm-correct-p tt1 a)
	     (tterm-correct-p tt2 a))
    :in-theory (e/d (top-down-postcond-p-var-expr-equiv
		     top-down-postcond-p-smt-judgements-ev)
		    (tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))
    :use ((:instance tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))))

  (local
   (defrule top-down-postcond-p-quote-case
    (implies (and (tterm->kind-equiv tt1 tt2)
		  (tterm->judgements-equiv tt1 tt2)
		  (set::subset (tterm->smt-judgements tt2)
			       (tterm->judgements tt1))
		  (equal (tterm->kind tt1) :quote)
		  (tterm-correct-p tt1 a)
		  (tterm->path-cond-equiv tt1 tt2)
		  (tterm->val-equiv tt1 tt2))
	     (tterm-correct-p tt2 a))
    :expand ((tterm-correct-p tt1 a)
	     (tterm-correct-p tt2 a))
    :in-theory (e/d (top-down-postcond-p-quote-expr-equiv
		     top-down-postcond-p-smt-judgements-ev)
		    (tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))
    :use ((:instance tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal))))

  (defthm-top-down-postcond-p-flag
    (defthm top-down-args-postcond-p-impl-tterm-list-correct-p
      (implies (top-down-args-postcond-p args1 args2)
               (implies (tterm-list-correct-p args1 a)
	                (tterm-list-correct-p args2 a)))
      :flag top-down-args-postcond-p)
    (defthm top-down-postcond-p-impl-tterm-correct-p
      (implies (top-down-postcond-p tt1 tt2)
               (implies (tterm-correct-p tt1 a)
	                (tterm-correct-p tt2 a)))
      :flag top-down-postcond-p)
    :hints (("Goal"
	      :in-theory (enable top-down-postcond-p-fncall-inductive-case
			         top-down-postcond-p-if-inductive-case
			         top-down-postcond-p-var-case
			         top-down-postcond-p-quote-case)
	      :expand ((top-down-postcond-p tt1 tt2)
		       (top-down-args-postcond-p args1 args2))))))


(define refine-judgement-helper ((recognizers pseudo-term-listp)
                                 (judgements judge-set-p))
  :measure (acl2-count recognizers)
  :returns (rv judge-set-p)
  (b* ((judgements (judge-set-fix judgements))
       (recognizers (pseudo-term-list-fix recognizers))
       ((if (set::emptyp judgements)) nil)
       ((unless (consp recognizers)) nil)
       ((cons head tail) recognizers))
    (if (set::in head judgements)
        (set::insert head nil)
      (refine-judgement-helper tail judgements)))
  ///
  (fty::deffixequiv refine-judgement-helper)
  (more-returns
   (rv :name refine-judgement-helper-subset-superset-judgements
       (implies (and (judge-set-p judgements)
		     (set::subset judgements superset))
		(set::subset rv superset))
       :hints (("Goal" :in-theory (enable set::subset-in))))))


(define refine-judgement ((judgements judge-set-p)
                          (top judge-set-p))
  :returns (rv judge-set-p)
  (b* ((judgements (judge-set-fix judgements))
       (recognizers (pseudo-term-list-fix *top-down-priority*))
       (top (judge-set-fix top))
       (permissible (set::intersect judgements top)))
    (refine-judgement-helper recognizers permissible))
  ///
  (fty::deffixequiv refine-judgement)
  (more-returns
   (rv :name refine-judgement-subset-judgements-top
       (implies (and (judge-set-p judgements)
		     (judge-set-p top))
                (and (set::subset rv judgements)
		     (set::subset rv top))))))


(define refine-terminal ((tterm tterm-p)
                         (top judge-set-p))
  :guard (or (equal (tterm->kind tterm) :quote)
             (equal (tterm->kind tterm) :var))
  :returns (rv tterm-p)
  (b* ((tterm (tterm-fix tterm))
       (top (judge-set-fix top))
       ((unless (mbt (or (equal (tterm->kind tterm) :quote)
                         (equal (tterm->kind tterm) :var))))
        (make-tterm-trivial nil))
       (judgements (tterm->judgements tterm))
       (new-judgement (refine-judgement judgements top)))
    (tterm-add-smt-judge-set tterm new-judgement))
  ///
  (fty::deffixequiv refine-terminal)
  (more-returns
   (rv :name refine-terminal-implements-top-down-postcond-p
       (implies (and (top-down-precond-p tterm)
                  (not (equal rv
                              (make-tterm-trivial nil))))
             (top-down-postcond-p tterm
                           (refine-terminal tterm top)))
       :hints (("Goal"
                 :in-theory (e/d (top-down-postcond-p)
                                 (refine-judgement-of-judge-set-fix-top
			          refine-judgement-judge-set-equiv-congruence-on-top))
                 :expand ((top-down-precond-p tterm)
                          (refine-terminal tterm top)
                          (top-down-postcond-p
                            tterm
                            (tterm-add-smt-judge-set
                              tterm
                              (refine-judgement (tterm->judgements tterm)
                                                (judge-set-fix top))))))))))


(define parse-judge-sets-correct-p ((judge-sets judge-set-list-p)
                                    (terms pseudo-term-listp)
                                    (judge-pts pseudo-term-listp)
                                    (a alistp))
  :returns (ok booleanp)
  :measure (len judge-sets)
  (b* ((judge-sets (judge-set-list-fix judge-sets))
       (terms (pseudo-term-list-fix terms))
       (judge-pts (pseudo-term-list-fix judge-pts))
       ((unless (and (consp judge-sets)
                     (consp terms)
                     (consp judge-pts)))
        t)
       (judge-set (judge-set-fix (car judge-sets)))
       (term (pseudo-term-fix (car terms)))
       (judge-pt (pseudo-term-fix (car judge-pts))))
    (and (implies
           (not (equal judge-set '((bad-judgement x))))
           (iff (all<judge-ev> judge-set term a)
                (ev-smtcp judge-pt a)))
         (parse-judge-sets-correct-p (cdr judge-sets)
                                     (cdr terms)
                                     (cdr judge-pts)
                                     a))))


(define parse-judge-sets ((terms pseudo-term-listp)
                          (judge-pts pseudo-term-listp))
  :returns (rv judge-set-list-p)
  (b* ((terms (pseudo-term-list-fix terms))
       (judge-pts (pseudo-term-list-fix judge-pts))
       ((unless (consp terms)) nil)
       ((unless (consp judge-pts)) nil))
    (cons (parse-judge-set (car terms) (car judge-pts))
          (parse-judge-sets (cdr terms) (cdr judge-pts))))
  ///
  (fty::deffixequiv parse-judge-sets)
  (more-returns
   (rv :name parse-judge-sets-correct
       (parse-judge-sets-correct-p rv terms judge-pts a)
       :hints (("Goal"
                 :in-theory (enable parse-judge-sets-correct-p)
                 :induct (parse-judge-sets terms judge-pts))))))

(encapsulate ()
  (local
    (defrule osets-list-set-equivalents
      (implies (judge-set-p j-set)
	       (and
	         (equal (car j-set)
		        (set::head j-set))
	         (equal (cdr j-set)
		        (set::tail j-set))))
      :in-theory (enable set::head
		         set::tail)))


  (local
    (defrule and-list-judge-ev-lst-equals-all-judge-ev
      (implies (and (judge-set-p j-set)
                    (pseudo-termp tterm))
	       (equal (and-list (judge-ev-lst j-set tterm a))
                      (all<judge-ev> j-set tterm a)))
      :in-theory (enable set::emptyp
		         set::cardinality)
      ;;		     osets-list-set-equivalents)
      :induct (set::cardinality j-set)))


  (define tterm-smt-judgement-expr ((tterm tterm-p))
    :returns (rv pseudo-termp)
    (b* ((tterm (tterm-fix tterm)))
      (and-list-expr
        (judge-list-flat-expr (tterm->smt-judgements tterm)
                              (tterm->expr tterm))))
    ///
    (fty::deffixequiv tterm-smt-judgement-expr)
    (more-returns
     (rv :name tterm-smt-judgement-expr-correct
         (equal (ev-smtcp rv a)
	        (tterm->smt-judgements-ev tterm a))
         :hints (("Goal"
                   :in-theory (e/d () ;; (and-list-judge-ev-lst-equals-all-judge-ev)
			           (and-list--expr/ev))
	           :expand ((tterm-smt-judgement-expr tterm)
		            (tterm->smt-judgements-ev tterm a))))))))


(defines refine-tterm
  :verify-guards nil
  :well-founded-relation l<

  (define refine-if ((tterm tterm-p)
                     (top judge-set-p)
                     (options type-options-p)
                     state)
    :measure (list (tterm->expr-count tterm) 2 0)
    :guard (equal (tterm->kind tterm)
                  :if)
    :returns (rv tterm-p)
    (b* ((tterm (tterm-fix tterm))
         (top (judge-set-fix top))
         (options (type-options-fix options))
         ((unless (mbt (equal (tterm->kind tterm) :if)))
          (make-tterm-trivial nil))
         (judgements (tterm->judgements tterm))
         (permissible (refine-judgement judgements top))
         (new-condx (refine-tterm (tterm->condx tterm)
                                  *bool-judgement*
                                  options
                                  state))
         (new-thenx (refine-tterm (tterm->thenx tterm)
                                  permissible
                                  options
                                  state))
         (new-elsex (refine-tterm (tterm->elsex tterm)
                                  permissible
                                  options
                                  state))
         ((if (or (equal new-condx
                         (make-tterm-trivial nil))
                  (equal new-thenx
                         (make-tterm-trivial nil))
                  (equal new-elsex
                         (make-tterm-trivial nil))))
          (make-tterm-trivial nil))
         (new-guts (make-tterm-guts-if :condx new-condx
                                       :thenx new-thenx
                                       :elsex new-elsex)))
      (tterm-add-smt-judge-set (tterm-change-guts tterm new-guts)
                               permissible)))

  (define zip-refine ((tterms tterm-list-p)
                      (tops judge-set-list-p)
                      (options type-options-p)
                      state)
    :measure (list (tterm-list->expr-list-count tterms) 1 0)
    :returns (mv (err booleanp)
                 (val tterm-list-p))
    (b* ((tterms (tterm-list-fix tterms))
         (tops (judge-set-list-fix tops))
         (options (type-options-fix options))
         ((unless (top-down-args-precond-p tterms))
          (mv t nil))
         ((unless (and (consp tterms)
                       (consp tops)))
          (mv nil nil))
         (new-head (refine-tterm (car tterms) (car tops) options state))
         ((if (equal new-head
                     (make-tterm-trivial nil)))
          (mv t nil))
         ((mv err new-tail)
          (zip-refine (cdr tterms) (cdr tops) options state))
         ((if err) (mv t nil)))
      (mv nil (cons new-head new-tail))))

  (define refine-fn ((tterm tterm-p)
                     (top judge-set-p)
                     (options type-options-p)
                     state)
    :measure (list (tterm->expr-count tterm) 2 0)
    :guard (equal (tterm->kind tterm)
                  :fncall)
    :returns (rv tterm-p)
    (b* ((tterm (tterm-fix tterm))
         (top (judge-set-fix top))
         (options (type-options-fix options))
         ((unless (mbt (equal (tterm->kind tterm) :fncall)))
          (make-tterm-trivial nil))
         ((unless (top-down-args-precond-p (tterm->args tterm)))
          (make-tterm-trivial nil))
         (judgements (tterm->judgements tterm))
         (permissible (refine-judgement judgements top))
         (tterm-new (tterm-add-smt-judge-set tterm permissible))
         ;; We construct a original-style `term substituted for variable'
         ;; judgement because of the way choose-returns works
         (top-judgement-expr (tterm-smt-judgement-expr tterm-new))
         (path-cond-expr (tterm->path-cond-expr tterm-new))
         (f (tterm->f tterm-new))
         (args (tterm->args tterm-new))
         (args-expr (tterm-list->expr-list args))
         (args-judgement-exprs (args->judgements-expr args))
         (functions (type-options->functions options))
         (conspair (assoc-equal f functions))
         ((unless conspair) (make-tterm-trivial nil))
         (permissible-args (choose-returns top-judgement-expr
                                           f
                                           args-expr
                                           args-judgement-exprs
                                           path-cond-expr
                                           (cdr conspair)
                                           options
                                           state))
         (permissible-judge-sets (parse-judge-sets args-expr
                                                   permissible-args))
         ;; TODO show that the downstream functions actually preserve list length?
         ((unless (= (len (tterm->args tterm))
                     (len permissible-judge-sets)))
          (make-tterm-trivial nil))
         ((mv err new-args) (zip-refine args permissible-judge-sets options state))
         ((if err) (make-tterm-trivial nil))
         (new-guts (make-tterm-guts-fncall :f f :args new-args)))
      (tterm-add-smt-judge-set (tterm-change-guts tterm new-guts)
                               permissible)))

  (define refine-tterm ((tterm tterm-p)
                        (top judge-set-p)
                        (options type-options-p)
                        state)
    :measure (list (tterm->expr-count tterm) 3 0)
    :returns (rv tterm-p)
    (b* ((tterm (tterm-fix tterm))
         (top (judge-set-fix top))
         (options (type-options-fix options))
         ((unless (top-down-precond-p tterm))
          (make-tterm-trivial nil)))
      (case (tterm->kind tterm)
        (:quote (refine-terminal tterm top))
        (:var (refine-terminal tterm top))
        (:if (refine-if tterm top options state))
        (:fncall (refine-fn tterm top options state)))))
  ///
  (verify-guards refine-tterm)
  (fty::deffixequiv-mutual refine-tterm)

  (local
   (defrule refine-tterm-fncall-inductive-case
     (implies
       (and
         (equal (tterm->kind tterm) :fncall)
         (assoc-equal (tterm->f tterm)
                      (type-options->functions options))
         (top-down-args-postcond-p
           (tterm->args tterm)
           new-args)
         (top-down-precond-p tterm)
         (judge-set-p top))
       (top-down-postcond-p
         tterm
         (tterm-add-smt-judge-set
           (tterm-change-guts
             tterm
             (tterm-guts-fncall
               (tterm->f tterm)
               new-args))
           (refine-judgement (tterm->judgements tterm)
                             top))))
     :in-theory (enable tterm-change-guts
                        tterm-add-smt-judge-set)
     :expand ((top-down-precond-p tterm)
              (top-down-postcond-p tterm
                                   (tterm (tterm->path-cond tterm)
                                          (tterm->judgements tterm)
                                          (refine-judgement (tterm->judgements tterm)
                                                            top)
                                          (tterm-guts-fncall (tterm->f tterm)
                                                             new-args))))))

  (local
   (defrule refine-tterm-if-inductive-case
     (implies
       (and (equal (tterm->kind tterm) :if)
            (top-down-postcond-p (tterm->condx tterm)
                                 new-condx)
            (top-down-postcond-p (tterm->thenx tterm)
                                 new-thenx)
            (top-down-postcond-p (tterm->elsex tterm)
                                 new-elsex)
            (top-down-precond-p tterm)
            (judge-set-p top))
       (top-down-postcond-p
         tterm
         (tterm-add-smt-judge-set
           (tterm-change-guts
             tterm
             (tterm-guts-if new-condx
                            new-thenx
                            new-elsex))
           (refine-judgement (tterm->judgements tterm)
                             top))))
     :in-theory (enable tterm-change-guts
                        tterm-add-smt-judge-set)
     :expand ((top-down-precond-p tterm)
              (top-down-postcond-p tterm
                                   (tterm (tterm->path-cond tterm)
                                          (tterm->judgements tterm)
                                          (refine-judgement (tterm->judgements tterm)
                                                            top)
                                          (tterm-guts-if new-condx new-thenx
                                                         new-elsex))))))

  (local
   (defrule refine-tterm-zip-inductive-case
     (implies (and (consp tterms)
                   (consp tops)
                   (not (equal new-head
                               (make-tterm-trivial nil)))
                   (top-down-postcond-p (car tterms)
                                        new-head)
                   (top-down-args-postcond-p (cdr tterms)
                                             new-tail)
                   (tterm-list-p tterms)
                   (top-down-args-precond-p tterms)
                   (judge-set-list-p tops))
              (top-down-args-postcond-p tterms
                                        (cons new-head new-tail)))
     :in-theory (enable top-down-args-postcond-p)))

  (local
   (defrule refine-tterm-zip-degenerate-case-0
     (implies (consp tterms)
              (not (equal (len tterms) 0)))))

  (defthm-refine-tterm-flag
    (defthm refine-if-implements-top-down-postcond-p
      (implies (and (tterm-p tterm)
                    (judge-set-p top)
                    (type-options-p options)
                    (top-down-precond-p tterm)
                    (equal (tterm->kind tterm) :if)
                    (not (equal (refine-if tterm top options state)
                                (make-tterm-trivial nil))))
	       (top-down-postcond-p tterm (refine-if tterm top options state)))
      :flag refine-if
      :skip t
      :hints ('(:expand ((refine-if tterm top options state)))))

    (defthm zip-refine-implements-top-down-args-postcond-p
      (mv-let (err rv) (zip-refine tterms tops options state)
        (implies (and (tterm-list-p tterms)
                      (judge-set-list-p tops)
                      (type-options-p options)
                      (= (len tterms)
                         (len tops))
                      (not err))
	         (top-down-args-postcond-p tterms rv)))
      :flag zip-refine
      :skip t
      :hints ('(:expand ((zip-refine tterms tops options state)
                         (top-down-args-postcond-p tterms nil)))))

    (defthm refine-fn-implements-top-down-postcond-p
      (implies (and (tterm-p tterm)
                    (judge-set-p top)
                    (type-options-p options)
                    (top-down-precond-p tterm)
                    (equal (tterm->kind tterm) :fncall)
                    (not (equal (refine-fn tterm top options state)
			        (make-tterm-trivial nil))))
	       (top-down-postcond-p tterm (refine-fn tterm top options state)))
      :skip t
      :flag refine-fn
      :hints ('(:expand ((refine-fn tterm top options state)))))

    (defthm refine-tterm-implements-top-down-postcond-p
      (implies (not (equal (refine-tterm tterm top options state)
			   (make-tterm-trivial nil)))
	       (top-down-postcond-p tterm (refine-tterm tterm top options state)))
      :flag refine-tterm
      :hints ('(:expand ((refine-tterm tterm top options state)))))

    :hints (("Goal"
	      :in-theory (disable (:executable-counterpart
	                           make-tterm-trivial)))))

  (defrule refine-tterm-satisfies-clause-processor-relations
    (let ((rv (refine-tterm tterm top options state)))
      (implies (top-down-postcond-p tterm rv)
               (and
                 (equal (ev-smtcp (tterm->expr rv)
                                  a)
                        (ev-smtcp (tterm->expr tterm)
                                  a))
                 (implies
                   (tterm-correct-p tterm a)
                   (tterm-correct-p rv a)))))))


(define refine-tterm-wrapper ((tterm tterm-p)
                              (options type-options-p)
                              state)
  :returns (new-tt tterm-p)
  (refine-tterm tterm *bool-judgement* options state)
  ///
  (defthmd refine-tterm-wrapper-implements-top-down-postcond-p
    (b* ((new-tt (refine-tterm-wrapper tterm options state)))
      (implies (not (equal new-tt
                           (make-tterm-trivial nil)))
               (top-down-postcond-p tterm new-tt))))

  (defthmd refine-tterm-wrapper-satisfies-clause-processor-relations-hypo
    (b* ((new-tt (refine-tterm-wrapper tterm options state)))
      (implies (top-down-postcond-p tterm new-tt)
               (and
                 (equal (ev-smtcp (tterm->expr new-tt)
                                  a)
                        (ev-smtcp (tterm->expr tterm)
                                  a))
                 (implies
                   (tterm-correct-p tterm a)
                   (tterm-correct-p new-tt a))))))

  (defrule refine-tterm-wrapper-satisfies-clause-processor-relations
    (let ((new-tt (refine-tterm-wrapper tterm options state)))
      (and
        (implies (ev-smtcp (tterm->expr new-tt) a)
                 (ev-smtcp (tterm->expr tterm) a))
        (implies (tterm-correct-p tterm a)
                 (tterm-correct-p new-tt a))))
    :in-theory (e/d (refine-tterm-wrapper-implements-top-down-postcond-p
                     refine-tterm-wrapper-satisfies-clause-processor-relations-hypo)
                    ((:executable-counterpart make-tterm-trivial)))
    :cases ((equal (refine-tterm-wrapper tterm options state)
                   (make-tterm-trivial nil)))))


(define map-top-down ((tterms tterm-list-p)
                      (options type-options-p)
                      (state t))
  :measure (tterm-list-count tterms)
  :returns (rv tterm-list-p)
  (b* ((tterms (tterm-list-fix tterms))
       (options (type-options-fix options)))
    (if (consp tterms)
        (cons (refine-tterm-wrapper (car tterms) options state)
              (map-top-down (cdr tterms) options state))
      nil))
  ///
  (fty::deffixequiv map-top-down)
  (defrule map-top-down-preserves-expr-eval-backwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
        	  (alistp a)
        	  (tterm-list-p tterms)
        	  (ev-smtcp (disjoin (tterm-list->expr-list
        			       (map-top-down tterms opts state)))
        		    a))
             (ev-smtcp (disjoin (tterm-list->expr-list tterms)) a))
    :in-theory (disable ev-smtcp-of-disjoin))
  (defrule map-top-down-preserves-correct-p-forwards
    (implies (and (ev-smtcp-meta-extract-global-facts)
                  (alistp a)
                  (tterm-list-p tterms)
                  (tterm-list-correct-p tterms a))
             (tterm-list-correct-p (map-top-down tterms opts state)
        			   a))))


(define type-judge-top-down-cp ((cl pseudo-term-listp)
                                (hint t)
                                state)
  (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
       ((unless (smtlink-hint-p hint)) (mv t nil state))
       ((mv fail tterms) (tterm-parse-clause2 cl))
       ((if fail) (mv t nil state))
       (next-cp (cdr (assoc-equal 'type-judge-top-down *SMT-architecture*)))
       ((if (null next-cp)) (mv t nil state))
       (type-opt (construct-type-options hint (disjoin cl)))
       (new-tts (map-top-down tterms type-opt state))
       (the-hint
         `(:clause-processor (,next-cp clause ',hint state)))
       (new-cl (tterms->tterm-clauses new-tts))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (value (list hinted-goal))))


(defrule correctness-of-type-judge-top-down-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                  (conjoin-clauses
                    (acl2::clauses-result
                      (type-judge-top-down-cp cl hint state)))
                  a))
           (ev-smtcp (disjoin cl) a))
  :in-theory (disable ev-smtcp-of-disjoin)
  :expand (type-judge-top-down-cp cl hint state)
  :use ((:functional-instance
          correctness-of-tterm-map-fn-cp
          (tterm-map-fn-cp type-judge-top-down-cp)
          (tterm-map-fn map-top-down)
          (tterm-trans-fn refine-tterm-wrapper)
          (env-trans-fn (lambda (x) x))
          (current-cp-fn (lambda () 'type-judge-top-down))))
  :rule-classes :clause-processor)
