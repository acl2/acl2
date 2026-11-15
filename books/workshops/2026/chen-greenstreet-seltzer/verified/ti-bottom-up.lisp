;; Copyright (C) 2026, University of British Columbia
;; Mark Greenstreet (July 30, 2026)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)
;(include-book "kestrel/fty/symbol-pseudoterm-alist" :dir :system)
(include-book "misc/beta-reduce" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "tools/rewrite-dollar" :dir :system)
(include-book "tools/easy-simplify" :dir :system)
;(include-book "tterm-clause-cp")
(include-book "tterm-change")
;(include-book "type-options")
(include-book "tterm-triv")
(include-book "term-rewrite") ; for rewrite$-helper
(include-book "make-test")

(set-state-ok t)
(set-induction-depth-limit 1)
(set-slow-alist-action :break)
(make-event (pprogn (set-warnings-as-errors t '("Use") state)
		    (value '(value-triple nil))))

; We don't need to have pseudo-termp enabled, and enabling it drastically
; slows down certifying or loading this book.
(local (in-theory (disable pseudo-termp)))

(fty::defalist nat-tterm-alist
  :key-type natp
  :val-type tterm-p
  :true-listp nil)  ; fast-alist's are not true-listp's

(fty::defprod proto-judge-acc
  ((next-index natp :default 0)
   (recognizers symbol-listp :default nil)
   (j-alist nat-tterm-alist-p :default nil)))

(local (defsection debug-help
  (defines show-tterm
    (define show-ttermx ((tterm tterm-p) (indent stringp))
      :measure (tterm-count (tterm-fix tterm))
      :returns (nothing null)
      (b* (((tterm tterm) (tterm-fix tterm))
	   (- (cw "~s0( expr -> ~x1~%" indent (tterm->expr tterm)))
	   (indent+ (acl2::implode (list* #\Space #\Space (acl2::explode indent))))
	   (- (cw "~s0 path-cond -> ~x1~%" indent+ tterm.path-cond))
	   (- (cw "~s0 judgements -> ~x1~%" indent+ tterm.judgements))
	   (- (show-guts tterm.guts indent+)))
	(cw "~s0)~%" indent)))

    (define show-guts ((guts tterm-guts-p) (indent stringp))
      :measure (tterm-guts-count (tterm-guts-fix guts))
      :returns (nothing null)
      (tterm-guts-case guts
        :if
	  (b* ((indent+ (acl2::implode (list* #\Space #\Space (acl2::explode indent))))
	       (- (cw "~s0 condx ->~%" indent))
	       (- (show-ttermx guts.condx indent+))
	       (- (cw "~s0 thenx ->~%" indent))
	       (- (show-ttermx guts.thenx indent+))
	       (- (cw "~s0 elsex ->~%" indent))
	       (- (show-ttermx guts.elsex indent+)))
	    nil)
        :fncall
	  (b* ((indent+ (acl2::implode (list* #\Space #\Space (acl2::explode indent))))
	       (- (cw "~s0 args -> (~%" indent))
	       (- (show-args guts.args indent+)))
	    (cw "~s0)~%" indent))
        :otherwise nil))

    (define show-args ((args tterm-list-p) (indent stringp))
      :measure (tterm-list-count (tterm-list-fix args))
      :returns (nothing null)
      (b* ((args (tterm-list-fix args))
	   ((unless args) nil)
	   ((cons hd tl) args)
	   (- (show-ttermx hd indent)))
	(show-args tl indent))))

  (define show-tterm ((tterm tterm-p))
    :returns (nothing null)
    (show-ttermx tterm ""))


  (define flatten-tr (x acc)
    :returns (flat acl2::any-p)
    (if (consp x)
      (flatten-tr (car x) (flatten-tr (cdr x) acc))
      (if x (cons x acc) acc))
    ///
    (more-returns
      (flat :name true-listp-of-flatten-tr
	    (implies (true-listp acc) (true-listp flat)))))

  (define flatten (x)
    :returns (flat acl2::any-p)
    (flatten-tr x nil)
    ///
    (more-returns
      (flat :name true-listp-of-flatten (true-listp flat))))

  (define bad-equal (who x j-alist val)
    :returns (v acl2::any-p)
    (prog2$
      (and (member 'ti-equal (flatten val))
	   (er hard? 'bad-equal "bad ti-equal: (~x0 ~x1 ~x2) -> ~x3~%" who x j-alist val))
      val)
    ///
    (more-returns (v :name bad-equal-is-identity (equal v val))))

  (define show-j-alist-help ((a nat-tterm-alist-p))
    (b* (((unless (consp a)) nil)
	 ((cons (cons index tterm) tl) a)
	 (- (cw "( expr -> ~x0~%" (tterm->expr tterm)))
	 (- (cw "  index -> ~x0~%" index))
	 (- (cw "  path-cond -> ~x0~%" (tterm->path-cond tterm)))
	 (- (cw "  judgements -> ~x0 )~%" (tterm->judgements tterm))))
      (show-j-alist-help tl)))

  (define show-j-alist((j-alist nat-tterm-alist-p))
    (show-j-alist-help (set::mergesort j-alist)))))

(defsection path-cond
  :short "Propagate the path-cond down an expression tree."
  :long  "Most functions just propagate their path-cond to their arguments.
(if cond then else) strengthens the path-cond of its then and else
with cond and (not cond) respectively."

  ; negate: simple version.
  ;   BOZO: rather than constructing a new pseudo-term (list 'not x), I should
  ;   at least check and simplify (not (not ...)).
  (define negate ((x pseudo-termp))
    :returns (not-x pseudo-termp)
    (b* ((x (pseudo-term-fix x))
	 (nx (list 'not x))
	 ((unless (consp x)) nx)
	 ((if (equal (car x) 'not)) (cadr x))
	 ((unless (equal (car x) 'if)) nx)
	 ((if (and (equal (caddr x) ''t) (equal (caddr x) ''nil)))
	  (negate (cadr x)))
	 ((if (and (equal (caddr x) ''nil) (equal (caddr x) ''t)))
	  (cadr x)))
      nx)
    ///
    (more-returns
      (not-x :name correctness-of-negate
	(iff (ev-smtcp not-x a)
	     (not (ev-smtcp (pseudo-term-fix x) a)))
	:hints(("Goal" :in-theory (enable negate))))))
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

  (define tterm-list-update-path-cond ((lst tterm-list-p) (parent tterm-p))
    :returns (new-lst tterm-list-p)
    (if (consp lst)
      (cons (tterm-add-path-cond-tterm (car lst) parent)
	    (tterm-list-update-path-cond (cdr lst) parent))
      nil)
    ///
    (defcong tterm-list-equiv tterm-list-equiv
	     (tterm-list-update-path-cond lst parent) 1
      :hints(("Goal" :induct (pairlis$ lst lst-equiv))))
    (defcong tterm->path-cond-equiv tterm-list-equiv
	     (tterm-list-update-path-cond lst parent) 2
      :hints(("Goal" :induct (len lst))))
    (more-returns
      (new-lst :name tterm-list->expr-list-equiv-of-tterm-list-update-path-cond
	(tterm-list->expr-list-equiv new-lst lst))

      (new-lst :name tterm-list-correct-p-of-tterm-list-update-path-cond
	(implies (tterm-list-correct-p lst a)
		 (tterm-list-correct-p new-lst a)))

      (new-lst :name args->path-cond-ev-of-tterm-list-update-path-cond
	(implies (and (tterm->path-cond-ev parent a)
		      (args->path-cond-ev lst a))
		 (args->path-cond-ev new-lst a)))))

  (define tterm-update-path-cond-children ((tterm tterm-p))
    :returns (new-tt tterm-p)
    (case (tterm->kind tterm)
      (:var (tterm-fix tterm))
      (:quote (tterm-fix tterm))
      (:if
	(b* ((condx (tterm->condx tterm))
	     (thenx (tterm->thenx tterm))
	     (elsex (tterm->elsex tterm))
	     (cond-expr  (tterm->expr condx)))
	  (change-tterm
	    tterm
	    :guts
	    (change-tterm-guts-if
	      (tterm->guts tterm)
	      :condx (tterm-add-path-cond-tterm condx tterm)
	      :thenx (tterm-add-path-cond-set
		       (tterm-add-path-cond-tterm thenx tterm)
		       (parse-conjunct cond-expr))
	      :elsex (tterm-add-path-cond-set
		       (tterm-add-path-cond-tterm elsex tterm)
		       (parse-conjunct (negate cond-expr)))))))
      (:fncall
	(b* ((new-args (tterm-list-update-path-cond (tterm->args tterm) tterm))
	     (new-guts (make-tterm-guts-fncall
			 :f (tterm->f tterm)
			 :args new-args)))
	  (make-tterm :path-cond (tterm->path-cond tterm)
		      :judgements (tterm->judgements tterm)
		      :smt-judgements (tterm->smt-judgements tterm)
		      :guts new-guts))))
    ///
    (defcong tterm-equiv tterm-equiv (tterm-update-path-cond-children tterm) 1)
    (more-returns
      (new-tt :name tterm->path-cond-of-tterm-update-path-cond-children
	(tterm->path-cond-equiv new-tt tterm))

      (new-tt :name tterm->judgements-of-tterm-update-path-cond-children
	      (tterm->judgements-equiv new-tt tterm))

      (new-tt :name tterm->smt-judgements-of-tterm-update-path-cond-children
	      (tterm->smt-judgements-equiv new-tt tterm))

      (new-tt :name tterm->kind-of-tterm-update-path-cond-children
	(tterm->kind-equiv new-tt tterm))))

  (local (defrule tterm-equiv-of-var-or-quote
    (implies
      (or (equal (tterm->kind tterm) :var)
	  (equal (tterm->kind tterm) :quote))
      (tterm-equiv (tterm-update-path-cond-children tterm)
		   tterm))
    :in-theory (enable tterm-update-path-cond-children)))

  (local (defrule lemma-if-details
    (let* ((condx (tterm->condx tterm))
	   (thenx (tterm->thenx tterm))
	   (elsex (tterm->elsex tterm))
	   (cond-expr  (tterm->expr condx))
	   (new-tt (tterm-update-path-cond-children tterm))
	   (new-condx (tterm-add-path-cond-tterm condx tterm))
	   (new-thenx (tterm-add-path-cond-set
			(tterm-add-path-cond-tterm thenx tterm)
			(parse-conjunct cond-expr)))
	   (new-elsex (tterm-add-path-cond-set
			(tterm-add-path-cond-tterm elsex tterm)
			(parse-conjunct (negate cond-expr)))))
      (implies (equal (tterm->kind tterm) :if)
	       (and (tterm-equiv (tterm->condx new-tt) new-condx)
		    (tterm-equiv (tterm->thenx new-tt) new-thenx)
		    (tterm-equiv (tterm->elsex new-tt) new-elsex))))
    :in-theory (enable tterm-update-path-cond-children)))

  (local (defrule lemma-fncall-details
    (implies (equal (tterm->kind tterm) :fncall)
      (let* ((new-tt (tterm-update-path-cond-children tterm))
	     (args (tterm->args tterm))
	     (new-args (tterm->args new-tt)))
	(tterm-list-equiv new-args (tterm-list-update-path-cond args tterm))))
    :in-theory (enable tterm-update-path-cond-children)))

  (local (defrule tterm->judgements-and-expr-of-tterm-update-path-cond-children
    (let ((new-tt (tterm-update-path-cond-children tterm)))
      (and (tterm->judgements-and-expr-equiv new-tt tterm)
	   (tterm->smt-judgements-and-expr-equiv new-tt tterm)))
    :in-theory (enable tterm->judgements-and-expr-equiv
		       tterm->smt-judgements-and-expr-equiv)
    :prep-lemmas (
      (defrule lemma-fncall-f
	(let ((new-tt (tterm-update-path-cond-children tterm)))
	  (implies (equal (tterm->kind tterm) :fncall)
		   (tterm->f-equiv new-tt tterm)))
	:in-theory (enable tterm-update-path-cond-children
			   tterm->f tterm->f-equiv))
      (defrule lemma-equal
	(let ((new-tt (tterm-update-path-cond-children tt)))
	  (equal (tterm->expr new-tt) (tterm->expr tt)))
	:use((:instance
	       tterm->expr (tt (tterm-update-path-cond-children tt)))
	     (:instance tterm->expr))))))

  (defrule tterm->expr-of-tterm-update-path-cond-children
    (let ((new-tt (tterm-update-path-cond-children tterm)))
      (tterm->expr-equiv new-tt tterm)))

  (defrule tterm-correct-p-of-tterm-update-path-cond-children
    (let ((new-tt (tterm-update-path-cond-children tterm)))
      (implies (tterm-correct-p tterm a)
	       (tterm-correct-p new-tt a)))
    :expand ((tterm-correct-p (tterm-update-path-cond-children tterm) a)))

  (define tterm-upcc-ignore-options-and-state
      ((tterm tterm-p) (opts acl2::any-p) (state state-p))
    :ignore-ok t
    (tterm-update-path-cond-children tterm))

  (in-theory (enable tterm-upcc-ignore-options-and-state))
  (tterm-propagate path-cond :pre tterm-upcc-ignore-options-and-state)
  (in-theory (disable tterm-upcc-ignore-options-and-state)))

(defsection proto-judgements
  :short "add judgements to each subterm of a tterm"
  :long  "Add judgements to a tterm of the form
    (ti-equal (hide (cdr (cons expr-index (type-p x)))) (type-p x))
for each type-recognizer, type-p, known to smtlink.  We'll use rewrite$ to simplify
the tterm-correct-expr generated from these judgements.  This allows us to connect
the hidden (type-p x) with the unhidden, and thus rewritten (type-p x).  rewrite$
can change the structure of the term.  We use expr-index to match to the correct
instance of a sub-expression."
; Implementation note 1: This seems like a nice task for the tterm-propagate macro
;   from the tterm-change3 book.  But, it doesn't provide a way to thread the counter
;   through the tree walk.  I could modify the macro (or write a new one) that return
;   (mv new-counter new-tterm-node), but that will add clutter of either having two
;   version of the macro, or forcing the smtlink developer to provide updating functions
;   that return an mv, even when they don't need it.  I could store counter in a table
;   in state.  That should work because we are planning on calling rewrite$ from a
;   computed-hint.  However, if we wanted similar functionality in a clause processor,
;   we can't modify state.  So, I'm writing a tree-walker just for this use.

;   Implementation note 2: Checking every subterm against every type recognizer may
;   introduce scaling issues if smtlink is used on big clauses with a large set of
;   possible types.  We could probably check the returns theorems for the top-level
;   function of each subterm to get a set of possible types.  I'm not sure how we
;   find these rules for highly-overloaded functions such as car and cdr.
;
;   Implementaion note 3: Because the judgements we add are trivial tautologies,
;   adding these judgements should preserve tterm-correct-p.  I haven't included
;   a proof because we have to verify the result of rewrite$ at run-time anyway.

  (define ti-equal ((x acl2::any-p) (y acl2::any-p))
    :returns (ok booleanp)
    (equal x y))

  (define proto-judge-help ((recognizers symbol-listp) (expr-index natp))
    :returns (judges judge-set-p
		     :hints(("Goal" :in-theory (enable judge-p))))
    :measure (len recognizers)
    (b* (((if (endp recognizers)) nil)
	 ((cons rec tl) (symbol-list-fix recognizers)))
       (set::insert
	 `(ti-equal (hide (cdr (cons ,(kwote expr-index) (,rec x))))
		    (bool-fix$inline (,rec x)))
	  (proto-judge-help tl expr-index))))

  (defines proto-judgements
    :verify-guards nil
    (define proto-judgements-term ((tterm tterm-p) (acc proto-judge-acc-p))
      :returns (mv (new-tt tterm-p) (new-acc proto-judge-acc-p))
      :measure (tterm-count (tterm-fix tterm))
      :flag term
      (b* (((mv guts-x acc-x)
	    (proto-judgements-guts (tterm->guts tterm) acc))
	   ((proto-judge-acc acc-x) acc-x)
	   (new-tt
	    (change-tterm tterm
	      :guts guts-x
	      :judgements
		(proto-judge-help acc-x.recognizers acc-x.next-index)))
	   (new-acc
	     (change-proto-judge-acc acc-x
	       :next-index (1+ acc-x.next-index)
	       :j-alist (hons-acons acc-x.next-index new-tt acc-x.j-alist))))
	(mv new-tt new-acc)))

    (define proto-judgements-guts
	((guts tterm-guts-p)  (acc proto-judge-acc-p))
      :returns (mv (new-guts tterm-guts-p) (new-acc proto-judge-acc-p))
      :measure (tterm-guts-count (tterm-guts-fix guts))
      :flag guts
      (b* ((guts (tterm-guts-fix guts))
	   (acc0 (proto-judge-acc-fix acc)))
	(tterm-guts-case guts
	   :var (mv guts acc0)
	   :quote (mv guts acc0)
	   :if
	     (b* (((mv new-condx acc1)
		   (proto-judgements-term guts.condx acc0))
		  ((mv new-thenx acc2)
		   (proto-judgements-term guts.thenx acc1))
		  ((mv new-elsex acc3)
		   (proto-judgements-term guts.elsex acc2)))
	      (mv (change-tterm-guts-if guts
		    :condx new-condx :thenx new-thenx :elsex new-elsex)
		  acc3))
	   :fncall
	     (b* (((mv new-args acc1)
		   (proto-judgements-list guts.args acc0)))
	       (mv (change-tterm-guts-fncall guts :args new-args)
		   acc1)))))

    (define proto-judgements-list
	((ttlst tterm-list-p) (acc proto-judge-acc-p))
      :returns (mv (new-ttlst tterm-list-p) (new-acc proto-judge-acc-p))
      :measure (tterm-list-count (tterm-list-fix ttlst))
      :flag list
      (b* ((ttlst (tterm-list-fix ttlst))
	   ((proto-judge-acc acc0) (proto-judge-acc-fix acc))
	   ((unless (consp ttlst)) (mv nil acc0))
	   ((cons hd tl) ttlst)
	   ((mv new-hd acc1) (proto-judgements-term hd acc0))
	   ((mv new-tl acc2) (proto-judgements-list tl acc1)))
	(mv (cons new-hd new-tl) acc2)))
    ///
    (verify-guards proto-judgements-term))

  ; The case-match in parse-ti-equal below nicely (imho) expresses the pattern
  ;   we want to handle for (ti-equal ...) expressions returned by rewrite$.
  ;   It also causes prolific case splitting.  To manage this, we quarantine
  ;   the case-match in parse-ti-equal and process the results of the
  ;   case-match in parese-ti-equal-help.
  (define parse-ti-equal-help ((js nat-tterm-alist-p) (i natp) (j judge-p))
    :returns (new-js nat-tterm-alist-p)
    :verify-guards nil
    (b* ((js (nat-tterm-alist-fix js))
	 (i (nfix i))
	 (j (judge-fix j))
	 (a (hons-get i js))
	 ((unless a)
	  (er acl2::hard? 'parse-ti-equal
	      "Smtlink internal error: bad expr-index, ~x0~%" i))
	 ((tterm tt0) (cdr a))
	 (tt1 (if (and (not (set::emptyp tt0.judgements))
		       (consp (set::head tt0.judgements))
		       (equal (car (set::head tt0.judgements)) 'ti-equal))
		(change-tterm tt0 :judgements nil)
		tt0)))
      (hons-acons i (tterm-add-judge-set tt1 (list j)) js))
    ///
    (local (defrule guard-lemma
      (implies (judge-p j) (judge-set-p (list j)))
      :enable judge-set-p))
    (verify-guards parse-ti-equal-help))

  (define parse-ti-equal ((js nat-tterm-alist-p) (x pseudo-termp))
    :returns (new-js nat-tterm-alist-p)
    :verify-guards nil
    (let ((js (nat-tterm-alist-fix js)))
      (case-match x
	(('ti-equal ('hide ('cdr ('cons ('quote expr-index) (type-recognizer &)))) ''t)
	 (if (and (natp expr-index) (symbolp type-recognizer))
	   (parse-ti-equal-help js expr-index `(,type-recognizer x))
	   js))
	(& js)))
    ///
    (local (defrule guard-lemma
      (implies (symbolp type-recognizer) (judge-p `(,type-recognizer x)))
      :enable judge-p))
    (verify-guards parse-ti-equal))


  (define delete-empty-judgements ((js nat-tterm-alist-p) (keys nat-listp))
    :measure (len (acl2::nat-list-fix keys))
    :returns (new-js nat-tterm-alist-p)
    (b* ((js (nat-tterm-alist-fix js))
	 (keys (acl2::nat-list-fix keys))
	 ((unless keys) js)
	 ((cons hd tl) keys)
	 (a (hons-get hd js))
	 ((unless (consp a)) js) ; shouldn't happen
	 ((tterm tt) (cdr a))
	 (js2 (if (and (consp tt.judgements)
		       (consp (car tt.judgements))
		       (equal (caar tt.judgements) 'ti-equal))
		(hons-acons hd (change-tterm tt :judgements nil) js)
		js)))
      (delete-empty-judgements js2 tl)))

  (define parse-judgements-help ((js nat-tterm-alist-p) (x pseudo-termp))
    :returns (new-js nat-tterm-alist-p)
    :verify-guards nil
    (b* ((js (nat-tterm-alist-fix js))
	 (x (pseudo-term-fix x))
	 ((unless (equal (acl2::pseudo-term-kind x) :fncall)) js)
	 ((if (equal (acl2::pseudo-term-fncall->fn x) 'ti-equal))
	  (parse-ti-equal js x))
	 ((unless (equal (acl2::pseudo-term-fncall->fn x) 'if)) js)
	 (args (acl2::pseudo-term-fncall->args x))
	 ((unless (and (consp args)
		       (consp (cdr args))
		       (consp (cddr args))
		       (null (cdddr args))))
	  js)
	 ((list condx thenx elsex) args))
      (parse-judgements-help
	(parse-judgements-help
	  (parse-judgements-help js condx) thenx) elsex))
    ///
    (verify-guards parse-judgements-help))

  (define j-alist-keys ((js nat-tterm-alist-p))
    :returns (keys nat-listp)
    :measure (len (nat-tterm-alist-fix js))
    :short "Like strip-cars without the guard of alistp."
    :long "Alistp implies true-listp, but fast-alists don't satisfy alistp!"
    (b* ((js (nat-tterm-alist-fix js))
	 ((unless (consp js)) nil)
	 ((cons hd tl) js))
      (cons (car hd) (j-alist-keys tl))))

  (define parse-judgements ((js nat-tterm-alist-p) (x pseudo-termp))
    :returns (new-js nat-tterm-alist-p)
    (b* ((js1 (parse-judgements-help js x))
	 (keys (j-alist-keys js1)))
    (fast-alist-clean
      (delete-empty-judgements (parse-judgements-help js1 x) keys)))))

(defsection merge-judgements
  :short "Annotate a term with the type-judgements determined by rewrite$."
  :long  "Emperically, applying rewrite$ to the  tterm-correct-expr of a term
returns an if-then-else tree where the conditions are the path-conditions of
the term.  If an if-condition, then-expression, or else-expression is an
application of ti-equal, we check to see if the unhidden version of the
type-recognizer call rewrote to 't.  If so, we add that type-judgement
to the term."

  (define merge-judgements-fetch ((tt-proto tterm-p) (j-alist nat-tterm-alist-p))
    :returns (new-tt tterm-p)
    (b* (((tterm tt-proto) (tterm-fix tt-proto))
	 (j-alist (nat-tterm-alist-fix j-alist))
	 (j1
	   (if (set::emptyp tt-proto.judgements)
	     'missing-judgements
	     (set::head tt-proto.judgements)))
	 (tt3 (case-match j1
		(('ti-equal ('hide ('cdr ('cons ('quote expr-index) &))) &)
		 (b* (((unless (natp expr-index))
		       (er hard? 'merge-judgements-fetch
			   "Smtlink, internal error: expr-index is not a natp -- ~x0"
			   expr-index))
		      (a (hons-get expr-index j-alist))
		      ((unless a)
		       (er hard? 'merge-judgements-fetch
			   "Smtlink, internal error: expr-index not found in j-alist -- expr-index = ~x0"
			   expr-index))
		      ((tterm tt1) (cdr a)))
		   tt1))
		('missing-judgements
		 (er hard? 'merge-judgements-fetch
		     "Smtlink, internal error: tt-proto has no judgements"))
		(& (er hard? 'merge-judgements-fetch
		       "tt-proto judgements aren't ti-equal tests"))))
	 )
	(if tt3 tt3 tt-proto)))


  (defines merge-judgements
    :verify-guards nil
    (define merge-judgements-term ((tt-proto tterm-p)
				  (j-alist nat-tterm-alist-p))
      :measure (tterm-count (tterm-fix tt-proto))
      :returns (new-tt tterm-p)
      (change-tterm (merge-judgements-fetch tt-proto j-alist)
	:guts (merge-judgements-guts (tterm->guts tt-proto) j-alist)))

    (define merge-judgements-guts ((guts tterm-guts-p)
				   (j-alist nat-tterm-alist-p))
      :measure (tterm-guts-count (tterm-guts-fix guts))
      :returns (new-guts tterm-guts-p)
      (b* ((guts (tterm-guts-fix guts))
	   (j-alist (nat-tterm-alist-fix j-alist)))
	(tterm-guts-case guts
	  :var guts
	  :quote guts
	  :if
	    (change-tterm-guts-if guts
	      :condx (merge-judgements-term guts.condx j-alist)
	      :thenx (merge-judgements-term guts.thenx j-alist)
	      :elsex (merge-judgements-term guts.elsex j-alist))
	  :fncall
	    (change-tterm-guts-fncall guts
	      :args (merge-judgements-args guts.args j-alist))))
    )

    (define merge-judgements-args ((args-proto tterm-list-p)
				   (j-alist nat-tterm-alist-p))
      :measure (tterm-list-count (tterm-list-fix args-proto))
      :returns (new-ttlst tterm-list-p)
      (b* ((args-proto (tterm-list-fix args-proto))
	   ((unless args-proto) nil)
	   ((cons hd tl) args-proto))
	(cons (merge-judgements-term hd j-alist)
	      (merge-judgements-args tl j-alist))))
    ///
    (verify-guards merge-judgements-term)))

(define type-inference-rw ((expr pseudo-termp)
                           (hyps pseudo-term-listp)
			   (recognizers symbol-listp)
			   (state state-p))
  :mode :program
  (b* ((expr (pseudo-term-fix expr))
       (hyps (pseudo-term-list-fix hyps))
       (recognizers (symbol-list-fix recognizers))
       ((proto-judge-acc acc) (make-proto-judge-acc :recognizers recognizers))
       (tt1 (tterm-propagate-path-cond-term
	      (make-tterm-trivial expr) nil state)))
    (with-fast-alist acc.j-alist
      (b* (((mv tt2 acc2)
	    (proto-judgements-term tt1 acc))
	   ((unless (termp (tterm-correct-expr tt2) (w state)))
	    (er soft 'type-inference-rw "(termp (tterm-correct-expr xpre) (w state)) -> nil~%"))
	   (cx2 (acl2::beta-reduce-pseudo-termp (tterm-correct-expr tt2)))
	   ((mv erp cx2-rw state)
	    (rewrite$-helper cx2 hyps nil state))
	   ((if erp)
	    (prog2$
	      (cw "rewrite$-helper failed: erp=~x0, cx2-rw=~x1~%" erp cx2-rw)
	      (mv erp cx2-rw state)))
	   (j (fast-alist-clean (parse-judgements (proto-judge-acc->j-alist acc2) cx2-rw)))
	   (tt3 (merge-judgements-term tt2 j)))
	(value tt3)))))

(define smt-recognizers ((datatypes smt-datatype-list-p))
  :returns (recognizers symbol-listp)
  :measure (len (smt-datatype-list-fix datatypes))
  (b* ((datatypes (smt-datatype-list-fix datatypes))
       ((unless datatypes) nil)
       ((cons hd tl) datatypes))
    (cons (smt-function->name (smt-datatype->recognizer hd))
	  (smt-recognizers tl))))

(std::defprojection negate-list ((x pseudo-term-listp))
  :returns (not-x pseudo-term-listp)
  (negate x))

(define type-inference-rw-clause ((clause pseudo-term-listp)
                                  (whole-clause pseudo-term-listp)
                                  (recognizers symbol-listp)
                                  (state state-p))
  :mode :program
  (b* ((clause (pseudo-term-list-fix clause))
       (whole-clause (pseudo-term-list-fix whole-clause))
       (recognizers (symbol-list-fix recognizers)))
    (if (consp clause)
        (b* ((term-to-infer (car clause))
             (hypotheses (negate-list (remove term-to-infer whole-clause)))
             ((mv err tterm state) (type-inference-rw term-to-infer
                                                      hypotheses
                                                      recognizers
                                                      state))
             ((if err) (mv err tterm state))
             ((mv err tterms state) (type-inference-rw-clause (cdr clause)
                                                              whole-clause
                                                              recognizers
                                                              state))
             ((if err) (mv err tterms state)))
          (value (cons tterm tterms)))
      (value nil))))

(define smt-type-judge-bottom-up-hint (cl kwd-alist state)
  :guard-debug t
  :parents (smt-computed-hints)
  :short "@('smt::smt-type-judge-bottom-up-hint') WRITE SOMETHING."
  :mode :program
  (b* (((unless (and (pseudo-term-listp cl)
                     (consp kwd-alist)
                     (consp (cdr kwd-alist))
                     (consp (cadr kwd-alist))
                     (= (len (cadr kwd-alist))
                        4)
                     (state-p state)))
        (prog2$ (cw "smt-type-judge-bottom-up-hint: preconditions not met: ~x0~%"
		    (if (pseudo-term-listp cl)
                        (if (consp kwd-alist)
                            (if (consp (cdr kwd-alist))
			        (if (consp (cadr kwd-alist))
			            (if (= (len (cadr kwd-alist)) 4)
				        (if (state-p state)
				            "all preconditions satisfied?!"
				          "(not (state-p state))")
				      "(not (= (len (cadr kwd-alist)) 4))")
			          "(not (consp (cadr kwd-alist)))")
			      "(not (consp (cdr kwd-alist)))")
			  "(not (consp kwd-alist))")
		      "(not (psuedo-term-listp cl))"))
                (value nil)))
       ((list* cp-kwd (list next-cp & q-smt-hint &) kwd-alist-tail) kwd-alist)
       ((unless (equal cp-kwd :clause-processor))
        (prog2$ (cw "smt-type-judge-bottom-up-hint: missing clause processor in kwd-alist: ~x0~%"
                    kwd-alist)
                (value nil)))
       ((unless (and (quotep q-smt-hint)
                     (smtlink-hint-p (unquote q-smt-hint))))
        (prog2$ (cw "not quoted smtlink-hint-p: ~x0~%" q-smt-hint)
                (value nil)))
       (smt-hint (unquote q-smt-hint))
       (recognizers (smt-recognizers (smtlink-hint->datatypes smt-hint)))
       ((mv fail tterms state) (type-inference-rw-clause cl cl recognizers state))
       ((if fail) (value nil)))
    (value `(:computed-hint-replacement ((smt-computed-hint clause))
             :clause-processor (,next-cp clause ',(cons smt-hint tterms) state)
             ,@kwd-alist-tail))))

(define type-judge-bottom-up-cp ((cl pseudo-term-listp) (hint t) state)
    (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
         ((unless (consp hint)) (mv t nil state))
         ((cons smt-hint tterms) hint)
         ((unless (smtlink-hint-p smt-hint)) (mv t nil state))
         ((unless (tterm-list-p tterms)) (mv t nil state))
         (expr-list (tterm-list->expr-list tterms))
	 ((unless (equal cl expr-list))
	  (prog2$
	    (cw "type-judge-bottom-up-cp: tterms don't correspond to clause.~%
                 clause: ~x0~%  expr-list: ~x1~%"
                cl
                expr-list)
	    (mv t nil state)))
	 (next-cp (cdr (assoc-equal 'type-judge-bottom-up *SMT-architecture*)))
	 ((if (null next-cp)) (mv t nil state))
	 (new-cl (tterms->tterm-clauses tterms))
	 (the-hint `(:clause-processor (,next-cp clause ',smt-hint state)))
	 (hinted-goal `((hint-please ',the-hint) ,@new-cl))
	 ;; Side condition
         (side-condition (tterm-list-correct-expr tterms))
	 ; might add a theory hint based on the rules used by rewrite$, or
	 ;   allow hints from the (advanced?) user.
	 )
      (value (list (cons side-condition cl) hinted-goal))))

(defrule correctness-of-type-judge-bottom-up-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (ev-smtcp
                    (conjoin-clauses
                      (acl2::clauses-result
                        (type-judge-bottom-up-cp cl hint state)))
                    a))
             (ev-smtcp (disjoin cl) a))
    :do-not-induct t
    :expand (type-judge-bottom-up-cp cl hint state)
    :in-theory (disable ev-smtcp-of-disjoin)
    :rule-classes :clause-processor)


(local (defsection examples
  (fty::defalist nat-sym-alist
    :key-type natp
    :val-type symbolp
    :true-listp t)

  (define xpr ()
    :returns (x pseudo-termp)
    '(if (natp x)
       (if (integerp y)
	 (natp (binary-+ x (binary-* y y)))
       't)
     't))

  (define xpr2 ()
    :returns (x pseudo-termp)
    '(if (natp x)
       (if (not (integerp y))
	  (natp (binary-+ x (binary-* y y)))
       't)
     't))

  (define expr-pre ((expr pseudo-termp) (state state-p))
    (b* (((proto-judge-acc acc)
	  (make-proto-judge-acc
	    :recognizers '(booleanp integerp natp nat-sym-alist-p)))
	 (tt1 (tterm-propagate-path-cond-term
		(make-tterm-trivial expr) nil state)))
      (with-fast-alist acc.j-alist
	(proto-judgements-term tt1 acc))))

  (define rec()
    :returns (recognizers symbol-listp)
    '(booleanp integerp natp nat-sym-alist-p))

  (define rw-test-fn ((expr pseudo-termp))
    `(b* ((recognizers '(booleanp integerp natp nat-sym-alist-p))
	  ((mv erp tterm state) (type-inference-rw ,expr nil recognizers state))
	  ((if erp)
	   (prog2$ (cw "type-inference-rw failed~%")
		   (mv erp tterm state)))
	  ((unless (tterm-p tterm))
	   (er soft 'rw-test
	       "type-inference-rw should return (mv nil x state) where (tterm-p x))~%  but x is not a tterm-p~%  x = ~x0~%"
	       tterm))
	  (- (cw "tterm = ~%"))
	  (- (show-ttermx tterm "  ")))
       (mv nil 'ok state))
    ///
    (defmacro rw-test (expr)
      (rw-test-fn expr)))

  ; for an example, try
  ; (rw-test (xpr))

(define smt-type-judge-bottom-up-demo (state)
  :mode :program
  (b* (((mv fail x state)
	(smt-type-judge-bottom-up-hint
	  (list (xpr))
	  (list :clause-processor
		(list 'type-judge-top-down
		      'ignore-me
		      (kwote
			(make-smtlink-hint
			  :datatypes
			  (list (make-smt-datatype-basic :recognizer (make-smt-function :name 'booleanp))
				(make-smt-datatype-basic :recognizer (make-smt-function :name 'integerp))
				(make-smt-datatype-basic :recognizer (make-smt-function :name 'natp))
				(make-smt-datatype-basic :recognizer (make-smt-function :name 'nat-sym-alist-p)))))
		      'ignore-me))
	  state))
       ((if fail)
	(mv fail (cw "smt-type-judge-bottom-up-hint failed~%") state))
       (- (cw "x  = `(~x0 ~x1 ~x2~%      (~x3 ~x4 ',(cons smt-hint tterm) ~x5)~%      ...)~%"
	      (car x) (cadr x) (caddr x) (car (cadddr x)) (cadr (cadddr x)) (cadddr (cadddr x))))
       (- (cw "smt-hint = ~x0~%" (car (unquote (caddr (cadddr x))))))
       (- (cw "tterm =~%"))
       (- (show-ttermx (cdr (unquote (caddr (cadddr x)))) "  ")))
    (value :invisible)))))
