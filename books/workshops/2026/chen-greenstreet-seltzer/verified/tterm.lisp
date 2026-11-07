;; Copyright (C) 2015, University of British Columbia)
;; Originally written by Yan Peng (December 30th 2019)
;; Edited by Mark Greenstreet
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;; This book introduces the tterm, tterm-guts, and tterm-list types.
;; These types provide annotations to terms for type-inference and other
;; reasoning about terms in Smtlink.  The name tterm is a placeholder.
;; It should by typed-term (or similar), but only when the integration
;; into the Smtlink code is complete (because there already is a typed-term
;; data structure in the existing code).

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/osets/quantify" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/basics")
(include-book "evaluator")

(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

; time to certify (M1 Macbook Pro):
;  without disabling any runes below: 136s
;  disabling the runes following 7.7s
(local (in-theory (disable pseudo-termp ;; Mark is impatient
  symbol-listp pseudo-term-listp-of-cdr-of-pseudo-termp
  acl2::pseudo-lambdap-of-car-when-pseudo-termp set::insert-identity
  pseudo-term-listp-of-symbol-listp acl2::pseudo-termp-list-cdr set::in-tail
  acl2::true-listp-of-car-when-true-list-listp integerp-when-maybe-integerp
  true-list-listp acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  acl2::symbol-listp-when-not-consp consp-of-cdr-of-pseudo-lambdap
  member-equal acl2::pseudo-termp-car set::nonempty-means-set set::union-in
  acl2::pseudo-termp-cadr-from-pseudo-term-listp maybe-integerp-when-integerp
  acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp
  acl2::integerp-of-car-when-integer-listp integer-listp rational-listp
  acl2::rationalp-of-car-when-rational-listp default-cdr
  acl2::pseudo-lambdap-when-member-equal-of-pseudo-lambda-listp
  acl2::integer-listp-of-cdr-when-integer-listp)))

(define consp-equiv (x y) ; perhaps this should move to ../utils/basics.lisp
  :returns (ok booleanp)
  (equal (consp x) (consp y))
  ///
  (more-returns
    (ok :name consp-equiv-when-equal
      (implies (equal (consp x) (consp y)) ok)))
  (defequiv consp-equiv)
  (defcong consp-equiv equal (consp x) 1))

(defrefinement pseudo-term-list-equiv consp-equiv
  :hints(("Goal"
    :in-theory (enable pseudo-term-list-fix)
    :induct (pairlis$ x y))))

(defsection simple-ev/expr
  (define ev-and ((x pseudo-termp) (y pseudo-termp) (a alistp))
    :returns (x^y acl2::any-p)
    (and ;(mbt (and (pseudo-termp x) (pseudo-termp y)))
	 (ev-smtcp (pseudo-term-fix x) a)
	 (ev-smtcp (pseudo-term-fix y) a))
    ///
    (defcong pseudo-term-equiv equal (ev-and x y a) 1)
    (defcong pseudo-term-equiv equal (ev-and x y a) 2))

  (define and-expr ((x pseudo-termp) (y pseudo-termp))
    :returns (x^y pseudo-termp)
    (list 'if (pseudo-term-fix x) (pseudo-term-fix y) ''nil)
    ///
    (more-returns
      (x^y :name ev-smtcp-of-and-expr
	(equal (ev-smtcp x^y a)
	       (and (ev-smtcp (pseudo-term-fix x) a)
		    (ev-smtcp (pseudo-term-fix y) a))))
      (x^y :name and--expr/ev
         (equal (ev-smtcp x^y a) (ev-and x y a))
	 :hints(("Goal" :in-theory (enable ev-and)))))
    (defcong pseudo-term-equiv equal (and-expr x y) 1)
    (defcong pseudo-term-equiv equal (and-expr x y) 2))

  (define and-list ((lst true-listp))
    :returns (x booleanp)
    (if (consp lst)
      (and (car lst) (and-list (cdr lst)))
      t)
    ///
    (more-returns
      (x :name and-list-when-consp
	(implies (consp lst)
		 (equal x (and (car lst) (and-list (cdr lst))))))))

  (define ev-and-list ((lst pseudo-term-listp) (a alistp))
    :returns (x booleanp)
    (if (consp lst)
      (and (ev-smtcp (pseudo-term-fix (car lst)) a)
	   (ev-and-list (cdr lst) a))
      t)
    ///
    (more-returns
      (x :name ev-and-list-when-consp
	 (implies
	   (consp lst)
	   (equal x
		  (and (ev-smtcp (pseudo-term-fix (car lst)) a)
		       (ev-and-list (cdr lst) a)))))
      (x :name ev-and-list-of-atom
	(implies (not (consp lst)) x)))

    (defcong pseudo-term-list-equiv equal (ev-and-list lst a) 1
      :hints(("Goal" :induct (pairlis$ lst lst-equiv)))))

  (define and-list-expr ((lst pseudo-term-listp))
    :returns (x pseudo-termp)
    (if (consp lst)
      (list 'if (pseudo-term-fix (car lst))
	    (and-list-expr (cdr lst)) ''nil)
      ''t)
    ///
    (more-returns
      (x :name ev-smtcp-of-and-list-expr
	 (implies (pseudo-term-listp lst)
		  (equal (ev-smtcp x a)
			 (and-list (ev-smtcp-lst lst a)))))
      (x :name and-list--expr/ev
	(equal (ev-smtcp x a) (ev-and-list lst a))
	:hints(("Goal" :in-theory (enable ev-and-list)))))
    (defcong pseudo-term-list-equiv equal (and-list-expr lst) 1
      :hints(("Goal" :induct (pairlis$ lst lst-equiv)))))

  (define equal-expr ((x pseudo-termp) (y pseudo-termp))
    :returns (x=y pseudo-termp)
    (and (pseudo-termp x) (pseudo-termp y) `(equal ,x ,y))
    ///
    (more-returns
     (x=y :name ev-smtcp-of-equal-expr
          (implies (and (pseudo-termp x) (pseudo-termp y) (alistp a))
                   (equal (ev-smtcp x=y a)
		          (equal (ev-smtcp x a) (ev-smtcp y a)))))))

  (define implies-expr ((x pseudo-termp) (y pseudo-termp))
    :returns (x=>y pseudo-termp)
    (and (pseudo-termp x) (pseudo-termp y) `(if ,x (if ,y 't 'nil) 't))
    ///
    (more-returns
      (x=>y :name ev-smtcp-of-implies-expr
        (implies (and (pseudo-termp x) (pseudo-termp y) (alistp a))
           (equal (ev-smtcp x=>y a)
		  (implies (ev-smtcp x a) (ev-smtcp y a))))))))

(defsection judge ; type judgements
  (defines judge
    :flag-local nil
    (define judge-p ((x acl2::any-p))
      :returns (ok booleanp)
      :flag term
      (if (consp x)
	(if (equal (car x) 'quote)
	  (and (consp (cdr x)) (equal (cddr x) nil))
	  (and (symbolp (car x)) (judge-list-p (cdr x))))
	(and (symbolp x)
	     (or (equal x 'x) (not x)))))
    (define judge-list-p ((lst acl2::any-p))
      :returns (ok booleanp)
      :flag list
      (if (consp lst)
	(and (judge-p (car lst)) (judge-list-p (cdr lst)))
	(not lst)))
    ///
    (define judge-fix ((j judge-p))
      :returns (j-fix judge-p)
      (mbe :logic (and (judge-p j) j) :exec j)
      ///
      (more-returns
	(j-fix :name judge-fix-when-judge-p
	  (implies (judge-p j) (equal j-fix j)))
	(j-fix :name idempotence-of-judge-fix
	       (equal (judge-fix j-fix) j-fix))))

    (deffixtype judge
      :pred judge-p
      :equiv judge-equiv
      :fix judge-fix
      :define t
      :forward t
      :topic judge)

    (deflist judge-list
      :pred judge-list-p
      :elt-type judge-p
      :fix judge-list-fix
      :true-listp t)

    (defthm-judge-flag
      (defthm pseudo-termp-when-judge-p
	(implies (judge-p x) (pseudo-termp x))
	:rule-classes ((:rewrite) (:forward-chaining))
	:flag term)
      (defthm pseudo-term-listp-when-judge-list-p
	(implies (judge-list-p lst) (pseudo-term-listp lst))
	:rule-classes ((:rewrite) (:forward-chaining))
	:flag list)
      :hints(("Goal" :in-theory (enable judge-p judge-list-p
					pseudo-termp pseudo-term-listp))))

    (define judge-ev ((j judge-p) (term pseudo-termp) (a alistp))
      :returns (x acl2::any-p)
      (ev-smtcp `((lambda (x) ,(pseudo-term-fix j)) ,term) a))

    (define judge-alist-equiv ((x symbol-alistp) (y symbol-alistp))
      :returns (ok booleanp)
      (equal (assoc-equal 'smt::x x) (assoc-equal 'smt::x y))
      ///
      (defequiv judge-alist-equiv))

    (local (in-theory (enable judge-alist-equiv ev-smtcp-of-fncall-args)))
    (defthm-judge-flag
      (defthm judge-ev-when-judge-alist-equiv
	(implies (and (judge-p x) (judge-alist-equiv a0 a1))
		 (equal (ev-smtcp x a0) (ev-smtcp x a1)))
	:flag term)
      (defthm judge-ev-lst-when-judge-alist-equiv
	(implies (and (judge-list-p lst) (judge-alist-equiv a0 a1))
		 (equal (ev-smtcp-lst lst a0) (ev-smtcp-lst lst a1)))
	:flag list)))


  (fty::defset judge-set
    :elt-type judge-p
    :elementp-of-nil t)

  (defrule acl2-count-of-judge-set-fix
    (<= (acl2-count (judge-set-fix x)) (acl2-count x))
    :rule-classes (:linear :rewrite)
    :in-theory (enable judge-set-fix))

  (defrule judge-set-p-implies-judge-list-p
    (implies (judge-set-p j)
	     (judge-list-p j))
    :rule-classes ((:rewrite) (:forward-chaining))
    :in-theory (enable judge-set-p judge-list-p))

  (defrule judge-set-p-when-judge-list-p-and-setp
    (implies (and (std::setp s) (judge-list-p s))
	     (judge-set-p s))
	:in-theory (enable judge-set-p std::setp))

  (set::quantify-predicate (judge-ev judge term a)
    :set-guard  ((judge-set-p ?set))
    :list-guard ((judge-list-p ?list))
    :arg-guard ((pseudo-termp term) (alistp a))
    :in-package-of judge-ev)

  (define judge-set-expr ((J judge-set-p))
    :returns (x pseudo-termp)
    :verify-guards nil
    (if (set::emptyp J)
      ''t
      (and-expr (pseudo-term-fix (set::head J))
		(judge-set-expr (set::tail J))))
    ///
    (verify-guards judge-set-expr)
    (defrule judge-set--ev/expr
      (equal (ev-smtcp `((lambda (x) ,(judge-set-expr J)) ,term) a)
	     (all<judge-ev> j term a))
      :in-theory (enable judge-set-expr all<judge-ev> judge-ev ev-and)))

  (deflist judge-set-list
    :pred judge-set-list-p
    :elt-type judge-set-p
    :fix judge-set-list-fix
    :true-listp t))


(defsection pseudo-term-set ; added for path-conditions, may find broader uses in Smtlink
  (fty::defset pseudo-term-set
    :elt-type pseudo-termp
    :elementp-of-nil t)

  (defrule acl2-count-of-pseudo-term-set-fix
    (<= (acl2-count (pseudo-term-set-fix x)) (acl2-count x))
    :rule-classes (:linear :rewrite)
    :in-theory (enable pseudo-term-set-fix))

  (defrule pseudo-term-list-p-when-pseudo-term-set-p
    (implies (pseudo-term-set-p x) (pseudo-term-listp x))
    :rule-classes ((:rewrite) (:forward-chaining))
    :in-theory (enable pseudo-term-set-p pseudo-term-listp))

  (defrule pseudo-term-set-p-when-pseudo-term-listp-and-setp
    (implies (and (std::setp s) (pseudo-term-listp s))
	     (pseudo-term-set-p s))
	:in-theory (enable pseudo-term-set-p std::setp))

  (define pseudo-term-ev ((term pseudo-termp) (a alistp))
    :returns (x acl2::any-p)
    (ev-smtcp (pseudo-term-fix term) a))

  (set::quantify-predicate (pseudo-term-ev term a)
      :set-guard  ((pseudo-term-set-p ?set))
      :list-guard ((pseudo-term-listp ?list))
      :arg-guard ((alistp a))
      :in-package-of pseudo-term-ev)

  (defrule ev-and-list-equals-all-list<pseudo-term-ev>
    (implies (pseudo-term-listp x)
	     (equal (ev-and-list x a)
		    (all-list<pseudo-term-ev> x a)))
    :in-theory (enable ev-and-list all-list<pseudo-term-ev> pseudo-term-ev))


  (define pseudo-term-set-expr ((cl pseudo-term-set-p))
    :returns (x pseudo-termp)
    :verify-guards nil
    (if (set::emptyp cl)
      ''t
      (and-expr (set::head cl)
		(pseudo-term-set-expr (set::tail cl))))
    ///
    (verify-guards pseudo-term-set-expr)
    (defrule pseudo-term-set--ev/expr
       (equal (ev-smtcp (pseudo-term-set-expr cl) a)
	      (all<pseudo-term-ev> cl a))
      :in-theory (enable pseudo-term-set-expr pseudo-term-ev all<pseudo-term-ev> ev-and))))

(defsection tterm
  (set-well-founded-relation l<)
  (fty::deftypes tterm
    (defprod tterm
      :measure (list (acl2-count x) 2)
      ((path-cond pseudo-term-set-p :default nil)
       (judgements judge-set-p :default nil)
       (smt-judgements judge-set-p :default nil)
       (guts tterm-guts :default (tterm-guts-var nil))))

    ; (for now) tterm-guts doesn't support lambda-expressions
    ; We assume that the clause has already been through expand-cp.
    (deftagsum tterm-guts
      :measure (list (acl2-count x) 1)
      (:var ((name symbolp)))
      (:quote ((val acl2::any-p)))
      (:if ((condx tterm-p)
	    (thenx tterm-p)
	    (elsex tterm-p)))
      (:fncall ((f symbolp :reqfix (if (not (equal f 'quote)) f 'bad-quote))
	        (args tterm-list-p))
	       :require (not (equal f 'quote))))

    (deflist tterm-list
      :elt-type tterm-p
      :true-listp t
      :measure (list (acl2-count x) 0)))

  (set-well-founded-relation o<)

  (defrefinement tterm-list-equiv consp-equiv
     :rule-classes (:refinement :forward-chaining)
     :hints(("Goal"
       :in-theory (enable tterm-list-equiv consp-equiv)
       :expand ((tterm-list-fix x)
		(tterm-list-fix y)))))

  ; We want tterm objects to be abstracted behind their accessor functions.
  ; To support this, we'll define per-field equivalence relations.
  (defmacro tterm->field-equiv (field-name)
    (let* ((access-fn (symcat 'tterm-> field-name))
	   (equiv-fn (symcat access-fn '-equiv))
	   (equal-implies-equiv (symcat equiv-fn '-when-equal- access-fn)))
      `(define ,equiv-fn ((tt1 tterm-p) (tt2 tterm-p))
	 :returns (ok booleanp)
         (equal (,access-fn tt1) (,access-fn tt2))
         ///
         (defequiv ,equiv-fn)
	 (defcong ,equiv-fn equal (,access-fn tt) 1)
	 (defrefinement tterm-equiv ,equiv-fn)
	 (defrule ,equal-implies-equiv
           (implies (equal (,access-fn tt1) (,access-fn tt2))
		    (,equiv-fn tt1 tt2))))))

  (tterm->field-equiv path-cond)
  (tterm->field-equiv judgements)
  (tterm->field-equiv smt-judgements)
  (tterm->field-equiv guts)

  ; short-cuts to access fields of tterm->guts
  (define tterm->kind ((tt tterm-p))
    :returns (kind keywordp :hints(("Goal" :in-theory (enable tterm-guts-kind))))
    (tterm-guts-kind (tterm->guts tt))
    ///
    (tterm->field-equiv kind)
    (defrefinement tterm->guts-equiv tterm->kind-equiv)
    (defrule tterm->kind-of-tterm
      (equal (tterm->kind (tterm path-cond judgements smt-judgements guts))
	     (tterm-guts-kind guts)))
    (more-returns tterm->kind
      (kind :name tterm->kind-possibilities
        (or (equal kind :var) (equal kind :quote) (equal kind :if) (equal kind :fncall))
	:rule-classes ((:rewrite) (:forward-chaining :trigger-terms ((tterm->kind tt))))
	:hints(("Goal" :expand ((tterm->kind tt)))))))

  (defmacro guts-shortcut (kind field-name field-type field-equiv)
    (let* ((access-fn (symcat 'tterm-> field-name))
	   (guts-access-fn (symcat 'tterm-guts- kind '-> field-name))
	   (equiv-fn (symcat access-fn '-equiv))
	   (equal-implies-equiv (symcat equiv-fn '-when-equal- access-fn))
	   (access-of-constructor (symcat access-fn '-of-tterm)))
      `(define ,access-fn ((tt tterm-p))
	 :returns (,field-name ,field-type)
	 :guard (equal (tterm->kind tt) ,kind)
	 :guard-hints(("Goal" :in-theory (enable tterm->kind)))
	 (,guts-access-fn (tterm->guts tt))
	 ///
	 (defcong tterm->guts-equiv equal (,access-fn tt) 1
	   :hints(("Goal" :in-theory (enable tterm->guts-equiv ,access-fn))))
	 (define ,equiv-fn ((tt1 tterm-p) (tt2 tterm-p))
	   :returns (ok booleanp)
	   :guard (and (equal (tterm->kind tt1) ,kind)
		       (equal (tterm->kind tt2) ,kind))
	   :guard-hints(("Goal" :in-theory (enable tterm->kind)))
	   (,field-equiv (,access-fn tt1) (,access-fn tt2))
	   ///
	   (defequiv ,equiv-fn)
	   (defcong ,equiv-fn ,field-equiv (,access-fn tt) 1)
	   (defrefinement tterm->guts-equiv ,equiv-fn)
	   (defrule ,equal-implies-equiv
	     (implies (equal (,access-fn tt1) (,access-fn tt2))
		      (,equiv-fn tt1 tt2)))
	   (defrule ,access-of-constructor
             (,field-equiv (,access-fn (tterm path-cond judgements smt-judgements guts))
			   (,guts-access-fn guts)))))))

  (guts-shortcut :var name symbolp equal)
  (guts-shortcut :quote val acl2::any-p equal)
  (guts-shortcut :if condx tterm-p tterm-equiv)
  (guts-shortcut :if thenx tterm-p tterm-equiv)
  (guts-shortcut :if elsex tterm-p tterm-equiv)
  (guts-shortcut :fncall f symbolp equal)
  (more-returns tterm->f
    (f :name tterm->f-not-equal-quote
       (not (equal f 'quote))
       :hints(("Goal" :in-theory (enable tterm->f)))))
  (guts-shortcut :fncall args tterm-list-p tterm-list-equiv)

  ; reconstruct the pseudo-termp from a tterm-p, and likewise for tterm-list-p
  (defines tterm->expr
    :hints(("Goal"
      :in-theory (enable tterm->kind tterm->args
			 tterm->condx tterm->thenx tterm->elsex)))
    :returns-hints(("Goal" :in-theory (enable pseudo-termp)))
    (define tterm->expr ((tt tterm-p))
      :returns (expr pseudo-termp)
      :flag term
      :measure (tterm-count tt)
      (case (tterm->kind tt)
	(:var    (tterm->name tt))
	(:quote  (kwote (tterm->val tt)))
	(:if     `(if ,(tterm->expr (tterm->condx tt))
		    ,(tterm->expr (tterm->thenx tt))
		    ,(tterm->expr (tterm->elsex tt))))
	(:fncall (list* (tterm->f tt)
			(tterm-list->expr-list (tterm->args tt))))))

    (define tterm-list->expr-list ((lst tterm-list-p))
      :flag list
      :returns (expr-lst pseudo-term-listp)
      :measure (tterm-list-count lst)
      (if (consp lst)
	(cons (tterm->expr (car lst))
	      (tterm-list->expr-list (cdr lst)))
	nil))
    ///
    (more-returns tterm-list->expr-list
      (expr-lst :name tterm-list->expr-list-when-consp
        (implies (consp lst)
		 (equal expr-lst
		        (cons (tterm->expr (car lst))
			      (tterm-list->expr-list (cdr lst)))))
	:hints(("Goal" :expand ((tterm-list->expr-list lst)))))

      (expr-lst :name tterm-list->expr-list-when-atom
        (implies (not (consp lst)) (not expr-lst))
	:hints(("Goal" :expand ((tterm-list->expr-list lst))))))

    (defrule tterm-list->expr-list-of-cons
      (equal (tterm-list->expr-list (cons tt lst))
	     (cons (tterm->expr tt) (tterm-list->expr-list lst)))))


    (define tterm->expr-equiv ((tt1 tterm-p) (tt2 tterm-p))
      :returns (ok booleanp)
      (equal (tterm->expr tt1) (tterm->expr tt2))
      ///
      (defequiv tterm->expr-equiv)
      (defrefinement tterm->guts-equiv tterm->expr-equiv
        :hints(("Goal"
	  :in-theory (disable tterm->guts-equiv)
	  :expand ((tterm->expr x) (tterm->expr y)))))
      (defcong tterm->expr-equiv equal (tterm->expr tt) 1)
      (defrule tterm->expr-equiv-when-equal
        (implies (equal (tterm->expr tt1) (tterm->expr tt2))
		 (tterm->expr-equiv tt1 tt2))))

    (define tterm-list->expr-list-equiv ((lst1 tterm-list-p) (lst2 tterm-list-p))
      :returns (ok booleanp)
      (equal (tterm-list->expr-list lst1) (tterm-list->expr-list lst2))
      ///
      (defequiv tterm-list->expr-list-equiv)
      (defrefinement tterm-list-equiv tterm-list->expr-list-equiv
	:hints(("Goal"
	  :in-theory (enable tterm-list->expr-list tterm-list-fix)
	  :induct (pairlis$ x y))))
      (defcong tterm-list->expr-list-equiv equal (tterm-list->expr-list lst) 1)

      (defrule tterm-list->expr-equiv-when-equal
        (implies (equal (tterm-list->expr-list lst1)
			(tterm-list->expr-list lst2))
		 (tterm-list->expr-list-equiv lst1 lst2)))

      (defrule tterm-list->expr-list-equiv-of-cons
	(equal (tterm-list->expr-list-equiv (cons tt1 lst1)
					    (cons tt2 lst2))
	       (and (tterm->expr-equiv tt1 tt2)
		    (tterm-list->expr-list-equiv lst1 lst2)))
	:in-theory (enable tterm-list->expr-list-equiv))

      (defrule tterm-list->expr-list-equiv-when-atom
	(iff (tterm-list->expr-list-equiv nil lst)
	     (not (consp lst)))
	:in-theory (enable tterm-list->expr-list)))

  (define tterm->expr-count ((tt tterm-p))
    :returns (d natp)
    (acl2-count (tterm->expr tt))
    ///

      (more-returns tterm->expr-count
	(d :name tterm->condx-decreases-tterm->expr-count
	   (implies (equal (tterm->kind tt) :if)
		    (<  (tterm->expr-count (tterm->condx tt)) d))
	   :hints(("Goal" :expand ((tterm->expr tt))))
	   :rule-classes (:rewrite :linear))

	(d :name tterm->thenx-decreases-tterm->expr-count
	   (implies (equal (tterm->kind tt) :if)
		    (< (tterm->expr-count (tterm->thenx tt)) d))
	   :hints(("Goal" :expand ((tterm->expr tt))))
	   :rule-classes (:rewrite :linear))

	(d :name tterm->elsex-decreases-tterm->expr-count
	   (implies (equal (tterm->kind tt) :if)
		    (< (tterm->expr-count (tterm->elsex tt)) d))
	   :hints(("Goal" :expand ((tterm->expr tt))))
	   :rule-classes (:rewrite :linear))))

  (define tterm-list->expr-list-count ((lst tterm-list-p))
    :returns (d natp)
    (acl2-count (tterm-list->expr-list lst))
    ///
    (more-returns tterm-list->expr-list-count
      (d :name car-decreases-tterm-list->expr-list-count
	 (implies (consp lst)
		  (< (tterm->expr-count (car lst)) d))
	 :hints(("Goal"
	   :expand ((tterm-list->expr-list lst)
		    (tterm->expr-count (car lst)))))
	 :rule-classes (:rewrite :linear))

      (d :name cdr-decreases-tterm-list->expr-list-count
	 (implies (consp lst)
		  (< (tterm-list->expr-list-count (cdr lst)) d))
	 :hints(("Goal"
	   :expand ((tterm-list->expr-list lst))))
	 :rule-classes (:rewrite :linear))

      (d :name tterm-list->expr-list-count-when-consp
	(implies (consp lst)
		 (equal d
			(+ (tterm->expr-count (car lst))
			   (tterm-list->expr-list-count (cdr lst))
			   1)))
       :hints(("Goal" :in-theory (enable tterm->expr-count))))

      (d :name tterm-list->expr-list-count-when-atom
	(implies (not (consp lst)) (equal d 0))
	:hints(("Goal" :expand (
	  (tterm-list->expr-list-count lst)
	  (tterm-list->expr-list lst))))))

    (more-returns tterm->expr-count
      (d :name tterm->args-decreases-tterm->expr-count
	 (implies (equal (tterm->kind tt) :fncall)
		  (< (tterm-list->expr-list-count (tterm->args tt)) d))
	 :hints(("Goal"
	   :in-theory (enable tterm->expr)
	   :expand ((tterm->expr-count tt))))
	 :rule-classes (:rewrite :linear))))

  (define tterm->expr-count-equiv ((tt1 tterm-p) (tt2 tterm-p))
    :returns (ok booleanp)
    (equal (tterm->expr-count tt1) (tterm->expr-count tt2))
    ///
    (defequiv tterm->expr-count-equiv)
    (defcong tterm->expr-count-equiv equal (tterm->expr-count tt) 1
      :rule-classes (:congruence :rewrite))
    (defrefinement tterm->expr-equiv tterm->expr-count-equiv
      :hints(("Goal" :in-theory (enable tterm->expr-count)))))

  (define tterm-list->expr-list-count-equiv ((lst1 tterm-list-p)
					     (lst2 tterm-list-p))
    :returns (ok booleanp)
    (equal (tterm-list->expr-list-count lst1)
	   (tterm-list->expr-list-count lst2))
    ///
    (defequiv tterm-list->expr-list-count-equiv)
    (defcong tterm-list->expr-list-count-equiv equal
	     (tterm-list->expr-list-count lst) 1
      :rule-classes (:congruence :rewrite))
    (defrefinement tterm-list->expr-list-equiv tterm-list->expr-list-count-equiv
      :hints(("Goal" :in-theory (enable tterm-list->expr-list-count)))))

  (define tterm->path-cond-ev ((tt tterm-p) (a alistp))
    :returns (x booleanp)
    (all<pseudo-term-ev> (tterm->path-cond tt) a)
    ///
    (defcong tterm->path-cond-equiv equal (tterm->path-cond-ev tt a) 1))

  (define tterm->path-cond-expr ((tt tterm-p))
    :returns (x pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
    (pseudo-term-set-expr (tterm->path-cond tt))
    ///
    (more-returns
      (x :name tterm->path-cond--expr/ev
	(equal (ev-smtcp x a) (tterm->path-cond-ev tt a))
        :hints(("Goal" :in-theory (enable tterm->path-cond-ev))))))

  (define tterm-list->path-cond-equiv ((lst1 tterm-list-p) (lst2 tterm-list-p))
    :returns (ok booleanp)
    (if (consp lst1)
      (and (consp lst2)
	   (tterm->path-cond-equiv (car lst1) (car lst2))
	   (tterm-list->path-cond-equiv (cdr lst1) (cdr lst2)))
      (not (consp lst2)))
    ///
    (local (defrule reflexivity
      (tterm-list->path-cond-equiv x x)))
    (local (defrule commutativity
      (equal (tterm-list->path-cond-equiv x y)
	     (tterm-list->path-cond-equiv y x))))
    (defrule tterm-list->path-cond-equiv-when-consp
      (implies (consp lst1)
	       (equal (tterm-list->path-cond-equiv lst1 lst2)
		      (and (consp lst2)
			   (tterm->path-cond-equiv (car lst1) (car lst2))
			   (tterm-list->path-cond-equiv (cdr lst1) (cdr lst2))))))
    (defrule tterm-list->path-cond-equiv-when-atom
      (implies (not (consp lst1))
	       (equal (tterm-list->path-cond-equiv lst1 lst2)
		      (not (consp lst2)))))
    (defequiv tterm-list->path-cond-equiv)
    (defrefinement tterm-list-equiv tterm-list->path-cond-equiv)
    (defrefinement tterm-list->path-cond-equiv consp-equiv))

  (define tterm->judgements-and-expr-equiv ((tt1 tterm-p) (tt2 tterm-p))
    :returns (ok booleanp)
    (and (tterm->judgements-equiv tt1 tt2)
	 (tterm->expr-equiv tt1 tt2))
    ///
    (defrule tterm->judgements-and-expr-equiv-when-judgements-and-expr-equal
      (implies (and (tterm->judgements-equiv tt1 tt2)
		    (tterm->expr-equiv tt1 tt2))
	       (tterm->judgements-and-expr-equiv tt1 tt2)))
    (defequiv tterm->judgements-and-expr-equiv)
    (defrefinement tterm->judgements-and-expr-equiv tterm->judgements-equiv)
    (defrefinement tterm->judgements-and-expr-equiv tterm->expr-equiv)
    (defrefinement tterm-equiv tterm->judgements-and-expr-equiv))

  (define tterm->judgements-ev ((tt tterm-p) (a alistp))
    :returns (x booleanp)
    (all<judge-ev> (tterm->judgements tt) (tterm->expr tt) a)
    ///
    (defcong tterm->judgements-and-expr-equiv equal (tterm->judgements-ev tt a) 1))

  (define tterm->judgements-expr ((tt tterm-p))
    :returns (x pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
    (and
      `((lambda (x) ,(judge-set-expr (tterm->judgements tt)))
	,(tterm->expr tt)))
    ///
    (more-returns
      (x :name tterm->judgements--expr/ev
	(equal (ev-smtcp x a) (tterm->judgements-ev tt a))
        :hints(("Goal" :in-theory (enable tterm->judgements-ev))))))

  (define tterm->smt-judgements-and-expr-equiv ((tt1 tterm-p) (tt2 tterm-p))
    :returns (ok booleanp)
    (and (tterm->smt-judgements-equiv tt1 tt2)
	 (tterm->expr-equiv tt1 tt2))
    ///
    (defrule tterm->smt-judgements-and-expr-equiv-when-smt-judgements-and-expr-equal
      (implies (and (tterm->smt-judgements-equiv tt1 tt2)
		    (tterm->expr-equiv tt1 tt2))
	       (tterm->smt-judgements-and-expr-equiv tt1 tt2)))
    (defequiv tterm->smt-judgements-and-expr-equiv)
    (defrefinement tterm->smt-judgements-and-expr-equiv tterm->smt-judgements-equiv)
    (defrefinement tterm->smt-judgements-and-expr-equiv tterm->expr-equiv)
    (defrefinement tterm-equiv tterm->smt-judgements-and-expr-equiv))

  (define tterm->smt-judgements-ev ((tt tterm-p) (a alistp))
    :returns (x booleanp)
    (all<judge-ev> (tterm->smt-judgements tt) (tterm->expr tt) a)
    ///
    (defcong tterm->smt-judgements-and-expr-equiv equal (tterm->smt-judgements-ev tt a) 1))

  (define tterm->smt-judgements-expr ((tt tterm-p))
    :returns (x pseudo-termp :hints(("Goal" :in-theory (enable pseudo-termp))))
    (and
     `((lambda (x) ,(judge-set-expr (tterm->smt-judgements tt)))
       ,(tterm->expr tt)))
    ///
    (more-returns
     (x :name tterm->smt-judgements--expr/ev
	(equal (ev-smtcp x a) (tterm->smt-judgements-ev tt a))
        :hints(("Goal" :in-theory (enable tterm->smt-judgements-ev)))))))


(defsection tterm-correct
  (define args->path-cond-ev ((args tterm-list-p) (a alistp))
    :returns (ok booleanp)
    (if (consp args)
      (and (tterm->path-cond-ev (car args) a)
           (args->path-cond-ev (cdr args) a))
      t)
    ///
    (more-returns
      (ok :name args->path-cond-ev-when-consp
        (implies (consp args)
		 (equal ok (and (tterm->path-cond-ev (car args) a)
				(args->path-cond-ev (cdr args) a)))))
      (ok :name args->path-cond-ev-when-atom
        (implies (not (consp args)) ok)))

    (defcong tterm-list->path-cond-equiv equal (args->path-cond-ev args a) 1
      :hints(("Goal"
	:in-theory (enable args->path-cond-ev tterm-list->path-cond-equiv)
	:induct (pairlis$ args args-equiv)))))

  (define args->path-cond-expr ((args tterm-list-p))
    :returns (expr pseudo-termp)
    (if (consp args)
      (and-expr
	(tterm->path-cond-expr (car args))
	(args->path-cond-expr (cdr args)))
      ''t)
    ///
    (more-returns
      (expr :name args->path-cond--expr/ev
	(equal (ev-smtcp expr a)
	       (args->path-cond-ev args a))
	:hints(("Goal" :in-theory (enable args->path-cond-ev ev-and))))))

  (defines tterm-correct
    (define tterm-correct-p ((tt tterm-p) (a alistp))
      :returns (ok booleanp)
      :flag term
      :measure (tterm->expr-count tt)
      (b* ((path-eval (tterm->path-cond-ev tt a))
	   (judge-eval (tterm->judgements-ev tt a))
           (smt-judge-eval (tterm->smt-judgements-ev tt a))
	   ((unless (and (implies path-eval judge-eval)
                         (implies path-eval smt-judge-eval)))
            nil)
	   ((if (equal (tterm->kind tt) :if))
	    (and (tterm-correct-p (tterm->condx tt) a)
		 (tterm-correct-p (tterm->thenx tt) a)
		 (tterm-correct-p (tterm->elsex tt) a)
		 (implies
		   path-eval
		   (and (tterm->path-cond-ev (tterm->condx tt) a)
			(if (ev-smtcp (tterm->expr (tterm->condx tt)) a)
			  (tterm->path-cond-ev (tterm->thenx tt) a)
			  (tterm->path-cond-ev (tterm->elsex tt) a))))))
	   ((if (equal (tterm->kind tt) :fncall))
	    (and (tterm-list-correct-p (tterm->args tt) a)
		 (implies path-eval
			  (args->path-cond-ev (tterm->args tt) a)))))
      t))

    (define tterm-list-correct-p ((lst tterm-list-p) (a alistp))
      :returns (ok booleanp)
      :flag list
      :measure (tterm-list->expr-list-count lst)
      (if (consp lst)
	(and (tterm-correct-p (car lst) a)
	     (tterm-list-correct-p (cdr lst) a))
	t))
    ///
    (more-returns tterm-correct-p
      (ok :name path-cond-implies-judgements-when-tterm-correct-p
	(implies
	  ok
	  (and (implies (tterm->path-cond-ev tt a)
		        (tterm->judgements-ev tt a))
               (implies (tterm->path-cond-ev tt a)
                        (tterm->smt-judgements-ev tt a)))))
      (ok :name tterm-correct-p-when-if
	(implies (and ok (equal (tterm->kind tt) :if))
		 (and (tterm-correct-p (tterm->condx tt) a)
		      (tterm-correct-p (tterm->thenx tt) a)
		      (tterm-correct-p (tterm->elsex tt) a)))
	:hints(("Goal" :expand (tterm-correct-p tt a))))
      (ok :name tterm-correct-p-when-if-condx
	(implies (and ok (equal (tterm->kind tt) :if)
			 (tterm->path-cond-ev tt a))
		 (tterm->path-cond-ev (tterm->condx tt) a))
	:hints(("Goal" :expand (tterm-correct-p tt a))))
      (ok :name tterm-correct-p-when-if-thenx
	(implies (and ok (equal (tterm->kind tt) :if)
			 (tterm->path-cond-ev tt a)
			 (ev-smtcp (tterm->expr (tterm->condx tt)) a))
		 (tterm->path-cond-ev (tterm->thenx tt) a))
	:hints(("Goal" :expand (tterm-correct-p tt a))))
      (ok :name tterm-correct-p-when-if-elsex
	(implies (and ok (equal (tterm->kind tt) :if)
			 (tterm->path-cond-ev tt a)
			 (not (ev-smtcp (tterm->expr (tterm->condx tt)) a)))
		 (tterm->path-cond-ev (tterm->elsex tt) a))
	:hints(("Goal" :expand (tterm-correct-p tt a))))
      (ok :name tterm-correct-p-when-fncall
	(implies (and ok (equal (tterm->kind tt) :fncall))
		 (and (tterm-list-correct-p (tterm->args tt) a)
		      (implies (tterm->path-cond-ev tt a)
			       (args->path-cond-ev (tterm->args tt) a))))
	:hints(("Goal" :expand (tterm-correct-p tt a)))))

    (more-returns tterm-list-correct-p
      (ok :name tterm-list-correct-p-when-consp
	(implies (consp lst)
		 (equal ok
			(and (tterm-correct-p (car lst) a)
			     (tterm-list-correct-p (cdr lst) a))))
	:hints(("Goal" :expand (tterm-list-correct-p lst a))))
      (ok :name tterm-list-correct-p-when-atom
	(implies (not (consp lst)) ok)
	:hints(("Goal" :expand ((tterm-list-correct-p lst a)))))))

    ; the (defines use-me-for-induction ...) below shows that tterm-correct-p
    ; and tterm-list-correct-p are preserved under tterm-equiv and
    ; tterm-list-equiv respectively.  We make the defines local to avoid
    ; cluttering the logical world when we're done.
    (local (defines use-me-for-induction
      (define induct-term ((tt1 tterm-p) (tt2 tterm-p))
	:flag term
	:measure (tterm->expr-count tt1)
	(and
	  (equal (tterm->kind tt1) (tterm->kind tt2))
	  (case (tterm->kind tt1)
	    (:if (list (induct-term (tterm->condx tt1) (tterm->condx tt2))
		       (induct-term (tterm->thenx tt1) (tterm->thenx tt2))
		       (induct-term (tterm->elsex tt1) (tterm->elsex tt2))))
	    (:fncall (induct-args (tterm->args tt1) (tterm->args tt2)))
	    (otherwise t))))

      (define induct-args ((lst1 tterm-list-p) (lst2 tterm-list-p))
	:flag args
	:measure (tterm-list->expr-list-count lst1)
	(if (and (consp lst1) (consp lst2))
	  (list (consp lst2)
		(induct-term (car lst1) (car lst2))
		(induct-args (cdr lst1) (cdr lst2)))
	  t))
      ///

      (defthm-use-me-for-induction-flag
	(defthm congruence-lemma-term
	  (implies (tterm-equiv tt1 tt2)
		   (equal (tterm-correct-p tt1 a)
			  (tterm-correct-p tt2 a)))
	  :flag term
	  :rule-classes :congruence)
	(defthm congruence-lemma-args
	  (implies (tterm-list-equiv lst1 lst2)
		   (equal (tterm-list-correct-p lst1 a)
			  (tterm-list-correct-p lst2 a)))
	  :flag args
	  :rule-classes :congruence)
	:hints(("Goal" :in-theory (enable tterm-correct-p tterm-list-correct-p))))))

    ; "export" the two congruences from use-me-for-induction
    (defcong tterm-equiv equal (tterm-correct-p tt a) 1)
    (defcong tterm-list-equiv equal (tterm-list-correct-p lst a) 1)


  ; tterm-correct-expr: the expr counterpart of tterm-correct-p
  ;   A "learned from experience" note about functions for traversing tterm objects.
  ;   Initially, I wrote function cliques with a function for tterm, a function
  ;   for tterm-guts, and a function for tterm-list to match the deftypes.
  ;   tterm-correct-p (defined later in this book) makes checks that the path-conditions
  ;   of actual-parameters are implied by the path-condition for the function call
  ;   (possibly strengthened by the if-condition or its negation).  The path-cond
  ;   field is shared for all forms of ttexpr-guts, and thus in part of the tterm
  ;   product.  This means verifying the tterm-guts requires knowing the path-cond
  ;   field from the parent tterm object.  If the path-cond is passed as a parameter
  ;   to a function for handling the tterm-guts, then I need an inducton hypothesis
  ;   for the tterm-guts function that says how the value it returns maintains the
  ;   right properties with respect to its path-cond parameter.  This is painful.
  ;     My solution is to use two functions: one for tterm-term and one for tterm-list.
  ;   The tterm-guts function is just absorbed into tterm-term.  This is easy enough.
  ;   However, this means that the measure-decreasing expressions are often buried
  ;   in the body of the function.  Thus, we often need
  ;     :ruler-extenders :all
  ;   tterm-correct-expr is an example of this.
  (defines tterm-correct-expr
    :verify-guards nil
    :ruler-extenders :all
    (define tterm-correct-expr ((tt tterm-p))
      :returns (expr pseudo-termp)
      :flag term
      :measure (tterm->expr-count tt)
      (b* (;((unless (mbt (tterm-p tt))) nil)
	   (path  (tterm->path-cond-expr  tt))
	   (judge (tterm->judgements-expr tt))
           (smt-judge (tterm->smt-judgements-expr tt))
	   (guts-expr
	     (case (tterm->kind tt)
	       (:var ''t)
	       (:quote ''t)
	       (:if
		 (and-list-expr (list
		   (tterm-correct-expr (tterm->condx tt))
		   (tterm-correct-expr (tterm->thenx tt))
		   (tterm-correct-expr (tterm->elsex tt))
		   (implies-expr
		     path
		     (and-expr
		       (tterm->path-cond-expr (tterm->condx tt))
		       (list 'if (tterm->expr (tterm->condx tt))
			  (tterm->path-cond-expr (tterm->thenx tt))
			  (tterm->path-cond-expr (tterm->elsex tt))))))))
	       (:fncall
		 (and-expr
		   (tterm-list-correct-expr (tterm->args tt))
		   (implies-expr
		     path
		     (args->path-cond-expr (tterm->args tt))))))))
        (and-expr (implies-expr path judge)
                  (and-expr
                    (implies-expr path smt-judge)
                    guts-expr))))

    (define tterm-list-correct-expr ((lst tterm-list-p))
      :returns (expr pseudo-termp)
      :flag list
      :measure (tterm-list->expr-list-count lst)
      (if (consp lst)
	(and-expr (tterm-correct-expr (car lst))
	     (tterm-list-correct-expr (cdr lst)))
	''t ;(kwote (equal lst nil))
	))
    ///
    (verify-guards tterm-correct-expr)

    (defthm-tterm-correct-expr-flag
      (defthm tterm-correct-p-equals-ev-of-expr
	(equal (ev-smtcp (tterm-correct-expr tt) a)
	       (tterm-correct-p tt a))
	:flag term)

      (defthm tterm-correct-list-p-equals-ev-of-expr
	(equal (ev-smtcp (tterm-list-correct-expr lst) a)
	       (tterm-list-correct-p lst a))
	:flag list)
      :hints(("Goal"
	:in-theory (enable tterm-correct-p tterm-list-correct-p
			   ev-and pseudo-term-ev implies-expr)))))

  (defines tterm-correct-smt-expr
    :verify-guards nil
    :ruler-extenders :all
    (define tterm-correct-smt-expr ((tt tterm-p))
      :returns (expr pseudo-termp)
      :flag term
      :measure (tterm->expr-count tt)
      (b* (;((unless (mbt (tterm-p tt))) nil)
	   (path  (tterm->path-cond-expr  tt))
           (smt-judge (tterm->smt-judgements-expr tt))
	   (guts-expr
	     (case (tterm->kind tt)
	       (:var ''t)
	       (:quote ''t)
	       (:if
		 (and-list-expr (list
		   (tterm-correct-expr (tterm->condx tt))
		   (tterm-correct-expr (tterm->thenx tt))
		   (tterm-correct-expr (tterm->elsex tt))
		   (implies-expr
		     path
		     (and-expr
		       (tterm->path-cond-expr (tterm->condx tt))
		       (list 'if (tterm->expr (tterm->condx tt))
			  (tterm->path-cond-expr (tterm->thenx tt))
			  (tterm->path-cond-expr (tterm->elsex tt))))))))
	       (:fncall
		 (and-expr
		   (tterm-list-correct-smt-expr (tterm->args tt))
		   (implies-expr
		     path
		     (args->path-cond-expr (tterm->args tt))))))))
        (and-expr (implies-expr path smt-judge)
                  guts-expr)))

    (define tterm-list-correct-smt-expr ((lst tterm-list-p))
      :returns (expr pseudo-termp)
      :flag list
      :measure (tterm-list->expr-list-count lst)
      (if (consp lst)
	(and-expr (tterm-correct-smt-expr (car lst))
	     (tterm-list-correct-smt-expr (cdr lst)))
	''t ;(kwote (equal lst nil))
	))
    ///
    (verify-guards tterm-correct-smt-expr)))
