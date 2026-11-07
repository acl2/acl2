;; Copyright (C) 2022, University of British Columbia)
;; Initial version by Mark Greenstreet.
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")

; This book has three main exports:
;   Function that make correct tterm and tterm-args values from pseudo-termp
;       and pseudo-term-listp objects respectively.  The functions we export
;       are
;     make-tterm-trivial and make-tterm-args-trivial.
;   Theorems that show that these functions produce values satisfying
;       tterm-correct-p and tterm-args-correct-p.  These theorems are
;     tterm-correct-p-of-make-tterm-trivial and
;     tterm-args-correct-p-of-mke-tterm-args-trivial.
;   Theorems that show that if a term satisfies pseudo-term-syntax-p, then
;       (equal (tterm->term (make-tterm-trivial term)) term)
;     and likewise for make-tterm-args-trivial.  These theorems are
;       make-tterm-trivial-when-pseudo-term-syntax-p and
;       make-tterm-args-trivial-when-pseudo-term-list-syntax-p and

(include-book "tterm")

(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

; Time to certify on a M1 Pro Macbook
;   If we don't disable useless rules:                22.75s
;   If we disable all useless rules:                   2.66s
;   Disable until :frame one-tenth of worst offender:  3.04s -- this is what I do below
;   Disable top 10 useless runes:                      3.30s
(local (in-theory (disable
  acl2::true-listp-of-car-when-true-list-listp
  true-list-listp true-listp symbol-listp default-car default-cdr
  acl2::true-list-listp-of-cdr-when-true-list-listp
  acl2::pseudo-lambdap-of-car-when-pseudo-termp
  pseudo-lambdap-of-fn-call-of-pseudo-termp consp-of-cdr-of-pseudo-lambdap
  pseudo-term-listp-of-cdr-of-pseudo-termp consp-of-pseudo-lambdap
  acl2::symbolp-of-car-when-symbol-listp lambda-of-pseudo-lambdap
  acl2::symbol-listp-when-not-consp pseudo-term-listp-of-symbol-listp
  acl2::pseudo-termp-when-member-equal-of-pseudo-term-listp
  acl2::symbol-listp-of-cdr-when-symbol-listp member-equal
  acl2::pseudo-termp-cadr-from-pseudo-term-listp
  acl2::pseudo-termp-car all-tail<judge-ev> acl2::subsetp-car-member)))


(defines make-tterm-trivial
  :verify-guards nil
  :ruler-extenders :all

  (define make-tterm-trivial ((term pseudo-termp))
    :returns (tterm tterm-p)
    :flag term
    (make-tterm
      :path-cond nil
      :judgements nil
      :smt-judgements nil
      :guts
	(b* (((if (symbolp term))
	      (make-tterm-guts-var :name term))
	     ((unless (mbt (consp term))) (make-tterm-guts-var :name 'bad-term))
	     ((cons fn args) term)
	     ((if (equal fn 'quote))
	      (make-tterm-guts-quote :val (cadr term)))
	     ((if (equal fn 'if))
	      (make-tterm-guts-if
		:condx (make-tterm-trivial (car args))
		:thenx (make-tterm-trivial (cadr args))
		:elsex (make-tterm-trivial (caddr args))))
	     ((if (symbolp fn))
	      (make-tterm-guts-fncall :f fn :args (make-tterm-list-trivial args))))
	    (make-tterm-guts-var :name 'bad-term))))

  (define make-tterm-list-trivial ((lst pseudo-term-listp))
    :returns (ttlst tterm-list-p)
    :flag list
    (if (consp lst)
       (cons (make-tterm-trivial (car lst))
	     (make-tterm-list-trivial (cdr lst)))
       nil))
  ///
  (verify-guards make-tterm-trivial
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp))))

  (encapsulate nil
    (local (defrule args->path-cond-ev-of-make-tterm-list-trivial
      (args->path-cond-ev (make-tterm-list-trivial lst) a)
      :induct (len lst)
      :in-theory (enable args->path-cond-ev make-tterm-list-trivial)
      :prep-lemmas (
	(defrule tterm->path-cond-ev-of-make-tterm-trivial
	  (tterm->path-cond-ev (make-tterm-trivial term) a)
	  :in-theory (enable tterm->path-cond-ev)
	  :expand ((make-tterm-trivial term))))))

    (local (defrule tterm->path-cond-ev-of-make-tterm-trivial
      (tterm->path-cond-ev (make-tterm-trivial term) a)
      :in-theory (enable tterm->path-cond-ev)
      :expand (make-tterm-trivial term)))

    (local (acl2::defruled tterm->judgements-evs-of-make-tterm-trivial
             (and
               (tterm->judgements-ev (make-tterm-trivial term) a)
               (tterm->smt-judgements-ev (make-tterm-trivial term) a))
             :in-theory (enable tterm->judgements-ev tterm->smt-judgements-ev)
             :expand (make-tterm-trivial term)))

    (defthm-make-tterm-trivial-flag
      (defthm tterm-correct-p-of-make-tterm-trivial
	(tterm-correct-p (make-tterm-trivial term) a)
	:flag term)

      (defthm tterm-list-correct-p-of-make-tterm-trivial
	(tterm-list-correct-p (make-tterm-list-trivial lst) a)
	:flag list)
      :hints(
        ("Goal" :in-theory (enable tterm-correct-p tterm-list-correct-p
				   make-tterm-trivial))
	; a computed hint because all of the subgoals for make-tterm-trivial
	; need an instantiation of tterm->judgements-ev-of-make-tterm-trivial.
	(and (member-equal '(not (acl2::flag-is 'term)) clause)
	     '(:use ((:instance tterm->judgements-evs-of-make-tterm-trivial))))))))


(defines pseudo-term-syntax
  (define pseudo-term-syntax-p ((term pseudo-termp))
    :returns (ok booleanp)
    :flag term
    (b* (((if (not (consp term))) (symbolp term))
	 ((cons fn args) term)
	 ((if (equal fn 'quote))
	  (and (consp args) (not (cdr args))))
	 ((if (equal fn 'if))
	  (and
	    (consp args)        (pseudo-term-syntax-p (car args))
	    (consp (cdr args))  (pseudo-term-syntax-p (cadr args))
	    (consp (cddr args)) (pseudo-term-syntax-p (caddr args))
	    (not (cdddr args))))
	 ((if (symbolp fn)) (pseudo-term-list-syntax-p args)))
      nil))

  (define pseudo-term-list-syntax-p ((lst pseudo-term-listp))
    :returns (ok booleanp)
    :flag list
    (if (consp lst)
      (and (pseudo-term-syntax-p (car lst))
	   (pseudo-term-list-syntax-p (cdr lst)))
      (not lst)))
  ///
  (defthm-pseudo-term-syntax-flag
    (defthm pseudo-termp-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term) (pseudo-termp term))
      :rule-classes :type-prescription
      :flag term)
    (defthm pseudo-term-listp-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p lst) (pseudo-term-listp lst))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal" :in-theory (enable pseudo-termp pseudo-term-listp))))

  (defthm-pseudo-term-syntax-flag
    (defthm make-tterm-trivial-when-pseudo-term-syntax-p
      (implies (pseudo-term-syntax-p term)
	       (equal (tterm->expr (make-tterm-trivial term)) term))
      :flag term)

    (defthm make-tterm-list-trivial-when-pseudo-term-list-syntax-p
      (implies (pseudo-term-list-syntax-p lst)
	       (equal (tterm-list->expr-list (make-tterm-list-trivial lst)) lst))
      :flag list)

    :hints(("Goal"
      :in-theory (enable pseudo-term-syntax-p pseudo-term-list-syntax-p
			 make-tterm-trivial make-tterm-list-trivial
			 tterm->expr tterm-list->expr-list)))))
