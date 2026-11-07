;; Copyright (C) 2021, University of British Columbia
;; Written by Mark Greenstreet (December 15th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

; tterm-change.lisp
;   Functions that preserve tterm-correct-p when updating one or more
;   fields of a tterm-p term.

(include-book "tterm")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

; Disabling the 30 top "useless" made no significant change in the time for
; certification.  I won't clutter this book with a paean to my impatience.


(define tterm-changes-returns-thms ((fn symbolp)
                                    (rv symbolp)
                                    (tterm symbolp)
                                    (changed-fields symbol-listp)
                                    (fields symbol-listp))
  :mode :program
  (b* (((unless (consp fields)) nil)
       ((cons field tail) fields)
       (thm (symcat 'tterm-> field '-of- fn))
       (equiv-fn (symcat 'tterm-> field '-equiv))
       (tail-rv (tterm-changes-returns-thms fn rv tterm changed-fields tail)))
    (if (position field changed-fields)
        tail-rv
      (cons `(,rv :name ,thm
                  (,equiv-fn ,rv ,tterm))
            tail-rv))))


(define tterm-only-changes-fn ((name symbolp)
                               (formals pseudo-term-listp)
                               (body pseudo-termp)
                               (changed-fields symbol-listp)
                               (tterm symbolp)
                               (rv symbolp)
                               (returns-theorems acl2::pseudo-event-form-listp)
                               (more-events acl2::pseudo-event-form-listp)
                               state)
  :mode :program
  (let ((fields (fty-prod-fields 'tterm state)))
    (mv nil
        `(define ,name ,formals
           :returns (,rv tterm-p)
           ,body
           ///
           (fty::deffixequiv ,name)
           (more-returns
            ,@(tterm-changes-returns-thms name rv tterm changed-fields fields)
            ,@returns-theorems)
           ,@more-events)
        state)))


(defmacro tterm-only-changes
          (name
            &key
            (formals '((tterm tterm-p)))
            (body '(tterm-fix tterm))
            (changed-fields 'nil)
            (tterm 'tterm)
            (rv 'new-tt)
            (returns-theorems 'nil)
            (more-events 'nil))
  `(make-event
     (tterm-only-changes-fn ',name
                            ',formals
                            ',body
                            ',changed-fields
                            ',tterm
                            ',rv
                            ',returns-theorems
                            ',more-events
                            state)))


(tterm-only-changes
  tterm-add-judge-set
  :formals ((tterm tterm-p) (new-judges judge-set-p))
  :body (change-tterm (tterm-fix tterm)
		      :judgements (set::union (judge-set-fix new-judges)
					      (tterm->judgements tterm)))
  :changed-fields (judgements)
  :returns-theorems ((new-tt :name tterm->judgements-of-tterm-add-judge-set
                             (equal (tterm->judgements new-tt)
	                            (set::union (judge-set-fix new-judges)
			                        (tterm->judgements tterm)))))
  :more-events ((local (in-theory (disable tterm-add-judge-set)))

                (defrule tterm->judgements-ev-of-tterm-add-judge-set
                  (equal (tterm->judgements-ev (tterm-add-judge-set tterm new-judges) a)
	                 (and (all<judge-ev> (judge-set-fix new-judges) (tterm->expr tterm) a)
		              (tterm->judgements-ev tterm a)))
                  :in-theory (enable tterm->judgements-ev))

                (defrule tterm->smt-judgements-and-expr-equiv-of-tterm-add-judge-set
                  (tterm->smt-judgements-and-expr-equiv
	            (tterm-add-judge-set tterm new-judges)
	            tterm)
                  :in-theory (enable tterm->smt-judgements-and-expr-equiv))

                (defrule tterm-correct-p-of-tterm-add-judge-set
                  (implies (and (tterm-correct-p tterm a)
		                (implies (tterm->path-cond-ev tterm a)
			                 (all<judge-ev> (judge-set-fix new-judges)
					                (tterm->expr tterm)
					                a)))
	                   (tterm-correct-p (tterm-add-judge-set tterm new-judges) a))
                  :expand ((tterm-correct-p (tterm-add-judge-set tterm new-judges) a)))))


;; (tterm-only-changes
;;   tterm-add-judge
;;   :formals ((tterm tterm-p) (new-judge judge-p))
;;   :body   (tterm-add-judge-set tterm (set::insert (judge-fix new-judge) nil))
;;   :changed-fields (judgements)
;;   :returns-theorems ((new-tt :name tterm->judgements-of-tterm-add-judge
;;                              (equal (tterm->judgements new-tt)
;; 	                            (set::insert (judge-fix new-judge)
;; 			                         (tterm->judgements tterm))))

;;                      (new-tt :name tterm->judgements-ev-of-tterm-add-judge
;;                              (equal (tterm->judgements-ev new-tt a)
;; 	                            (and (judge-ev (judge-fix new-judge) (tterm->expr tterm) a)
;; 		                         (tterm->judgements-ev tterm a))))

;;                      (new-tt :name tterm-correct-p-of-tterm-add-judge
;;                              (implies (and (tterm-correct-p tterm a)
;; 		                           (implies (tterm->path-cond-ev tterm a)
;; 			                            (judge-ev (judge-fix new-judge)
;; 				                              (tterm->expr tterm)
;; 				                              a)))
;; 	                              (tterm-correct-p new-tt a)))))


(tterm-only-changes
  tterm-add-smt-judge-set
  :formals ((tterm tterm-p) (new-judges judge-set-p))
  :body (change-tterm (tterm-fix tterm)
		      :smt-judgements (set::union (judge-set-fix new-judges)
					          (tterm->smt-judgements tterm)))
  :changed-fields (smt-judgements)
  :returns-theorems ((new-tt :name tterm->smt-judgements-of-tterm-add-smt-judge-set
                             (equal (tterm->smt-judgements new-tt)
	                            (set::union (judge-set-fix new-judges)
			                        (tterm->smt-judgements
                                                  tterm)))))
  :more-events ((local (in-theory (disable tterm-add-smt-judge-set)))

                (defrule tterm->smt-judgements-ev-of-tterm-add-smt-judge-set
                  (equal (tterm->smt-judgements-ev (tterm-add-smt-judge-set tterm new-judges) a)
	                 (and (all<judge-ev> (judge-set-fix new-judges) (tterm->expr tterm) a)
		              (tterm->smt-judgements-ev tterm a)))
                  :in-theory (enable tterm->smt-judgements-ev))

                (defrule tterm->judgements-and-expr-equiv-of-tterm-add-smt-judge-set
                  (tterm->judgements-and-expr-equiv
	            (tterm-add-smt-judge-set tterm new-judges)
	            tterm)
                  :in-theory (enable tterm->judgements-and-expr-equiv))

                (defrule tterm-correct-p-of-tterm-add-smt-judge-set
                  (implies (and (tterm-correct-p tterm a)
		                (implies (tterm->path-cond-ev tterm a)
			                 (all<judge-ev> (judge-set-fix new-judges)
					                (tterm->expr tterm)
					                a)))
	                   (tterm-correct-p (tterm-add-smt-judge-set tterm new-judges) a))
                  :expand ((tterm-correct-p (tterm-add-smt-judge-set tterm new-judges) a)))

                (defrule tterm-add-smt-judge-set-subset-preserves-tterm-correct-p
	          (implies (and (tterm-correct-p tterm a)
		                (set::subset smt-judges (tterm->judgements tterm)))
		           (tterm-correct-p (tterm-add-smt-judge-set tterm smt-judges)
		                            a))
	          :cases ((judge-set-p smt-judges))
	          :expand ((tterm-correct-p tterm a)
		           (tterm->judgements-ev tterm a)))))


(tterm-only-changes
  tterm-add-path-cond-set
  :formals ((tterm tterm-p) (new-pcs pseudo-term-set-p))
  :body (change-tterm (tterm-fix tterm)
		      :path-cond (set::union (pseudo-term-set-fix new-pcs)
				             (tterm->path-cond tterm)))
  :changed-fields (path-cond)
  :returns-theorems ((new-tt :name tterm->path-cond-of-tterm-add-path-cond-set
                             (equal (tterm->path-cond new-tt)
	                            (set::union (pseudo-term-set-fix new-pcs)
			                        (tterm->path-cond tterm)))))
  :more-events ((defcong tterm-equiv tterm-equiv (tterm-add-path-cond-set tterm new-pcs) 1)
                (defcong pseudo-term-set-equiv tterm-equiv (tterm-add-path-cond-set tterm new-pcs) 2)

                (local (in-theory (disable tterm-add-path-cond-set)))

                (defrule tterm->judgements-and-expr-equiv-of-tterm-add-path-cond-set
                  (tterm->judgements-and-expr-equiv
	            (tterm-add-path-cond-set tterm new-pcs)
	            tterm)
                  :in-theory (enable tterm->judgements-and-expr-equiv))

                (defrule tterm->smt-judgements-and-expr-equiv-of-tterm-add-path-cond-set
                  (tterm->smt-judgements-and-expr-equiv
	            (tterm-add-path-cond-set tterm new-pcs)
	            tterm)
                  :in-theory (enable tterm->smt-judgements-and-expr-equiv))

                (defrule tterm->path-cond-ev-of-tterm-add-path-cond-set
                  (equal (tterm->path-cond-ev (tterm-add-path-cond-set tterm new-pcs) a)
	                 (and (tterm->path-cond-ev tterm a)
		              (all<pseudo-term-ev> (pseudo-term-set-fix new-pcs) a)))
                  :in-theory (enable tterm->path-cond-ev))

                (defrule tterm-correct-p-of-tterm-add-path-cond-set
                  (implies (tterm-correct-p tterm a)
	                   (tterm-correct-p (tterm-add-path-cond-set tterm new-pcs) a))
                  :expand ((tterm-correct-p (tterm-add-path-cond-set tterm new-pcs) a)))))


(tterm-only-changes
  tterm-add-path-cond-tterm
  :formals ((tterm tterm-p) (parent tterm-p))
  :body (tterm-add-path-cond-set tterm (tterm->path-cond parent))
  :changed-fields (path-cond)
  :returns-theorems ((new-tt :name tterm-correct-p-of-tterm-add-path-cond-tterm
                             (implies (tterm-correct-p tterm a)
	                              (tterm-correct-p new-tt a)))

                     (new-tt :name tterm->path-cond-ev-of-tterm-add-path-cond-tterm
                             (equal (tterm->path-cond-ev new-tt a)
	                            (and (tterm->path-cond-ev tterm a)
		                         (tterm->path-cond-ev parent a)))
                             :hints(("Goal" :expand (tterm->path-cond-ev parent a)))))
  :more-events ((defcong tterm-equiv tterm-equiv (tterm-add-path-cond-tterm tterm parent) 1)
                (defcong tterm->path-cond-equiv tterm-equiv (tterm-add-path-cond-tterm tterm parent) 2)))


(tterm-only-changes
  tterm-add-path-cond
  :formals ((tterm tterm-p) (new-pc pseudo-termp))
  :body (tterm-add-path-cond-set tterm (set::insert (pseudo-term-fix new-pc)
                                                    nil))
  :changed-fields (path-cond)
  :returns-theorems ((new-tt :name tterm-correct-p-of-tterm-add-path-cond
                             (implies (tterm-correct-p tterm a)
	                              (tterm-correct-p new-tt a)))

                     (new-tt :name tterm->path-cond-ev-of-tterm-add-path-cond
                             (equal (tterm->path-cond-ev new-tt a)
	                            (and (ev-smtcp (pseudo-term-fix new-pc) a)
		                         (tterm->path-cond-ev tterm a)))
                             :hints(("Goal" :in-theory (enable pseudo-term-ev)))))
  :more-events ((defcong tterm-equiv tterm-equiv (tterm-add-path-cond tterm new-pcs) 1)
                (defcong pseudo-term-equiv tterm-equiv (tterm-add-path-cond tterm new-pcs)
                  2)))


(tterm-only-changes
  tterm-change-guts
  :formals ((tterm tterm-p) (new-guts tterm-guts-p))
  :body (change-tterm (tterm-fix tterm)
                      :guts (tterm-guts-fix new-guts))
  :changed-fields (guts)
  :returns-theorems ((new-tt :name tterm->guts-of-tterm-change-guts
                             (equal (tterm->guts new-tt)
                                    (tterm-guts-fix new-guts))))
  :more-events ((defcong tterm-equiv tterm-equiv (tterm-change-guts tterm new-guts) 1)
                (defcong tterm-guts-equiv tterm-equiv (tterm-change-guts tterm new-guts)
                  2)))


; the functions above allow us to update the path-cond or judgements or a
; single tterm-p object.  tterm-p objects for trees corresponding to the syntax
; of the expression that they are annotating.  The
;     (tterm-propagate name :pre fn-pre :post fn-post)
; macro below introduces
;     tterm-propagate-<$name$>-term
; (and several other functions) that performs a depth-first traversal the tree
; updating each node with fn-pre (default: tterm-fix) before traversing the
; descendants and ; updating with fn-post (default: tterm-fix) after traversing
; the descendants.  Functions fn-pre and fn-post must ensure:
;   (tterm-p (fn-pxx tterm))
;   (tterm->path-cond-equiv (fn-pxx tterm) tterm)
;   (tterm->expr-equiv (fn-pxx tterm) tterm)
;   (implies (tterm-correct-p tterm a) (tterm-correct-p (fn-pxx tterm) a))
; The function tterm-propagate-<$name$>-term then makes the same guarantees.

(define tterm-update-term-default ((tterm tterm-p) (opts acl2::any-p) state)
  (declare (ignore opts state))
  :returns (new-tt tterm-p)
  (tterm-fix tterm)
  ///
  (more-returns
    (new-tt :name tterm->path-cond-of-tterm-update-term-default
      (tterm->path-cond-equiv new-tt tterm))

    (new-tt :name tterm->expr-of-tterm-update-term-default
      (tterm->expr-equiv new-tt tterm))

    (new-tt :name tterm-correct-p-of-tterm-update-term-default
      (implies (tterm-correct-p tterm a)
	       (tterm-correct-p new-tt a)))))

(encapsulate
  (((tterm-update-term-pre * * state) => *)
   ((tterm-update-term-post * * state) => *))

  (local (defun tterm-update-term-pre (tterm opts state)
	   (tterm-update-term-default tterm opts state)))

  (defthm tterm-p-of-tterm-update-term-pre
    (tterm-p (tterm-update-term-pre tterm opts state)))

  (defthm tterm->path-cond-of-tterm-update-term-pre
    (tterm->path-cond-equiv (tterm-update-term-pre tterm opts state) tterm))

  (defthm tterm->expr-of-tterm-update-term-pre
    (tterm->expr-equiv (tterm-update-term-pre tterm opts state) tterm))

  (defthm tterm-correct-p-of-tterm-update-term-pre
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp a) ; BOZO
		  (tterm-correct-p tterm a))
	     (tterm-correct-p (tterm-update-term-pre tterm opts state) a)))

  ; Yuck -- a cut-and-paste to create the -post version.  If this gets
  ; used in yet another way, I should probably write a macro.
  (local (defun tterm-update-term-post (tterm opts state)
	   (tterm-update-term-default tterm opts state)))

  (defthm tterm-p-of-tterm-update-term-post
    (tterm-p (tterm-update-term-post tterm opts state)))

  (defthm tterm->path-cond-of-tterm-update-term-post
    (tterm->path-cond-equiv (tterm-update-term-post tterm opts state) tterm))

  (defthm tterm->expr-of-tterm-update-term-post
    (tterm->expr-equiv (tterm-update-term-post tterm opts state) tterm))

  (defthm tterm-correct-p-of-tterm-update-term-post
    (implies (and (ev-smtcp-meta-extract-global-facts)
		  (alistp a) ; BOZO
		  (tterm-correct-p tterm a))
	     (tterm-correct-p (tterm-update-term-post tterm opts state) a))))

(defrule tterm-update-term-pre-preserves-tterm->expr-count
  (equal (tterm->expr-count (tterm-update-term-pre tterm opts state))
	 (tterm->expr-count tterm)))

(defrule tterm-update-term-post-preserves-tterm->expr-count
  (equal (tterm->expr-count (tterm-update-term-post tterm opts state))
	 (tterm->expr-count tterm)))

(defun tterm-propagate-defines-fn (name fn-pre fn-post opt-guard more-events)
  (b* ((defines-name (symcat 'tterm-propagate- name))
       (fn-term (symcat defines-name '-term))
       (fn-guts (symcat defines-name '-guts))
       (fn-term-if (symcat defines-name '-if))
       (fn-term-fncall (symcat defines-name '-fncall))
       (fn-args (symcat defines-name '-args))
       (more-formals `((opts ,opt-guard) (state state-p)))
       (more-actuals '(opts state)))
    `(defines ,defines-name
       :verify-guards nil
       :well-founded-relation l<
       (define ,fn-term ((tterm tterm-p) ,@more-formals)
	 :flag term
	 :returns (new-tt tterm-p)
	 :measure (list (tterm->expr-count tterm) 3)
	 (,fn-post (,fn-guts (,fn-pre tterm ,@more-actuals)
				,@more-actuals)
		 ,@more-actuals))

       (define ,fn-guts ((tterm tterm-p) ,@more-formals)
	 :flag guts
	 :returns (new-tt tterm-p)
	 :measure (list (tterm->expr-count tterm) 2)
	 (case (tterm->kind tterm)
	   (:var (tterm-fix tterm))
	   (:quote (tterm-fix tterm))
	   (:if (,fn-term-if tterm ,@more-actuals))
	   (:fncall (,fn-term-fncall tterm ,@more-actuals))))

       (define ,fn-term-if ((tterm tterm-p) ,@more-formals)
	 :flag if
	 :returns (new-tt tterm-p)
	 :measure (list (tterm->expr-count tterm) 1)
	 (if (equal (tterm->kind tterm) :if)
	   (tterm
	     (tterm->path-cond tterm)
	     (tterm->judgements tterm)
             (tterm->smt-judgements tterm)
	     (tterm-guts-if
	       (,fn-term (tterm->condx tterm) ,@more-actuals)
	       (,fn-term (tterm->thenx tterm) ,@more-actuals)
	       (,fn-term (tterm->elsex tterm) ,@more-actuals)))
	   (tterm-fix tterm)))

       (define ,fn-term-fncall ((tterm tterm-p) ,@more-formals)
	 :flag fncall
	 :returns (new-tt tterm-p)
	 :measure (list (tterm->expr-count tterm) 1)
	 (if (equal (tterm->kind tterm) :fncall)
	   (tterm
	     (tterm->path-cond tterm)
	     (tterm->judgements tterm)
             (tterm->smt-judgements tterm)
	     (tterm-guts-fncall
	       (tterm->f tterm)
	       (,fn-args (tterm->args tterm) ,@more-actuals)))
	   (tterm-fix tterm)))

       (define ,fn-args ((args tterm-list-p) ,@more-formals)
	 :flag args
	 :returns (new-args tterm-list-p)
	 :measure (list (tterm-list->expr-list-count args) 0)
	 (if (consp args)
	   (cons (,fn-term (car args) ,@more-actuals)
		 (,fn-args (cdr args) ,@more-actuals))
	   nil))
       ///
       (verify-guards ,fn-term)
       ,@more-events)))

; an example:
; (tterm-propagate-defines-fn 'foo 'foo-pre 'foo-post 'rationalp nil)

(defmacro tterm-propagate-defines
  (name
   &key (pre 'tterm-update-term-default)
        (post 'tterm-update-term-default)
	(opt-guard 'acl2::any-p)
        (more-events 'nil))
  (tterm-propagate-defines-fn name pre post opt-guard more-events))

(tterm-propagate-defines generic
			 :pre tterm-update-term-pre
			 :post tterm-update-term-post
			 :more-events (
  (local (defrule tterm-propagate-generic-args-when-consp
    (implies (consp args)
	     (equal (tterm-propagate-generic-args args opts state)
		    (cons (tterm-propagate-generic-term (car args) opts state)
			  (tterm-propagate-generic-args (cdr args) opts state))))))

  (local (defrule tterm-propagate-generic-args-of-atom
    (implies (not (consp args))
	     (not (tterm-propagate-generic-args args opts state)))
    :expand ((tterm-propagate-generic-args args opts state))))

  (local (defrule lemma-fncall-judgements
    (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
      (implies (and (equal (tterm->kind tterm) :fncall)
		    (acl2::any-p opts)
                    (acl2::any-p state))
	(tterm->judgements-equiv new-tt tterm)))
    :expand (tterm-propagate-generic-fncall tterm opts state)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-fncall-smt-judgements
    (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
      (implies (and (equal (tterm->kind tterm) :fncall)
		    (acl2::any-p opts)
                    (acl2::any-p state))
	(tterm->smt-judgements-equiv new-tt tterm)))
    :expand (tterm-propagate-generic-fncall tterm opts state)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-fncall-expr
    (let ((new-tt (tterm-propagate-generic-fncall tterm opts state))
	  (new-args (tterm-propagate-generic-args (tterm->args tterm) opts state)))
      (implies
	(tterm-list->expr-list-equiv new-args (tterm->args tterm))
	(tterm->expr-equiv new-tt tterm)))
    :in-theory (enable tterm->expr tterm->f)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-fncall-trivial
    (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
      (implies (not (equal (tterm->kind tterm) :fncall))
	       (equal new-tt (tterm-fix tterm))))))

  (local (defrule lemma-if-judgements
    (let ((new-tt (tterm-propagate-generic-if tterm opts state)))
      (implies (and (equal (tterm->kind tterm) :if)
		    (acl2::any-p opts)
                    (acl2::any-p state))
	(tterm->judgements-equiv new-tt tterm)))
    :expand (tterm-propagate-generic-if tterm opts state)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-if-smt-judgements
    (let ((new-tt (tterm-propagate-generic-if tterm opts state)))
      (implies (and (equal (tterm->kind tterm) :if)
		    (acl2::any-p opts)
                    (acl2::any-p state))
	(tterm->smt-judgements-equiv new-tt tterm)))
    :expand (tterm-propagate-generic-if tterm opts state)
    :rule-classes (:forward-chaining)))

  (local (defrule lemma-if-expr-judgements
    (let ((new-tt (tterm-propagate-generic-if tterm opts state))
          (new-condx (tterm-propagate-generic-term (tterm->condx tterm) opts state))
	  (new-thenx (tterm-propagate-generic-term (tterm->thenx tterm) opts state))
	  (new-elsex (tterm-propagate-generic-term (tterm->elsex tterm) opts state)))
      (implies
	(and (equal (tterm->kind tterm) :if)
	     (tterm->expr-equiv new-condx (tterm->condx tterm))
	     (tterm->expr-equiv new-thenx (tterm->thenx tterm))
	     (tterm->expr-equiv new-elsex (tterm->elsex tterm)))
	(tterm->judgements-and-expr-equiv new-tt tterm)))
    :in-theory (enable tterm->expr)))

  (local (defrule lemma-if-expr-smt-judgements
    (let ((new-tt (tterm-propagate-generic-if tterm opts state))
          (new-condx (tterm-propagate-generic-term (tterm->condx tterm) opts state))
	  (new-thenx (tterm-propagate-generic-term (tterm->thenx tterm) opts state))
	  (new-elsex (tterm-propagate-generic-term (tterm->elsex tterm) opts state)))
      (implies
	(and (equal (tterm->kind tterm) :if)
	     (tterm->expr-equiv new-condx (tterm->condx tterm))
	     (tterm->expr-equiv new-thenx (tterm->thenx tterm))
	     (tterm->expr-equiv new-elsex (tterm->elsex tterm)))
	(tterm->smt-judgements-and-expr-equiv new-tt tterm)))
    :in-theory (enable tterm->expr)))

  (local (defrule lemma-if-trivial
    (let ((new-tt (tterm-propagate-generic-if tterm opts st)))
      (implies (not (equal (tterm->kind tterm) :if))
	       (equal new-tt (tterm-fix tterm))))))

  (defthm-tterm-propagate-generic-flag
    (defthm tterm->expr-of-tterm-propagate-generic-term
      (let ((new-tt (tterm-propagate-generic-term tterm opts state)))
	(tterm->expr-equiv new-tt tterm))
      :flag term)

    (defthm tterm->expr-of-tterm-propagate-generic-guts
      (let ((new-tt (tterm-propagate-generic-guts tterm opts state)))
	(tterm->expr-equiv new-tt tterm))
      :flag guts)

    (defthm tterm->expr-of-tterm-propagate-generic-if
      (let ((new-tt (tterm-propagate-generic-if tterm opts state)))
	(tterm->expr-equiv new-tt tterm))
      :flag if)

    (defthm tterm->expr-of-tterm-propagate-generic-fncall
      (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
	(tterm->expr-equiv new-tt tterm))
      :flag fncall)

    (defthm tterm-list->expr-list-of-tterm-propagate-generic-args
      (let ((new-args (tterm-propagate-generic-args args opts state)))
	(tterm-list->expr-list-equiv new-args args))
      :flag args)

    :hints(("Goal"
      :in-theory (enable tterm-propagate-generic-term
			 tterm-propagate-generic-guts))))

  (local (defrule tterm->path-cond-of-tterm-propagate-generic-fncall
    (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
      (tterm->path-cond-equiv new-tt tterm))
    :expand (tterm-propagate-generic-fncall tterm opts state)))

  (local (defrule tterm->path-cond-of-tterm-propagate-generic-if
    (let ((new-tt (tterm-propagate-generic-if tterm opts state)))
      (tterm->path-cond-equiv new-tt tterm))
    :expand (tterm-propagate-generic-if tterm opts state)))

  (local (defrule tterm->path-cond-of-tterm-propagate-generic-guts
    (let ((new-tt (tterm-propagate-generic-guts tterm opts state)))
      (tterm->path-cond-equiv new-tt tterm))
    :expand (tterm-propagate-generic-guts tterm opts state)))

  (defrule tterm->path-cond-of-tterm-propagate-generic-term
    (let ((new-tt (tterm-propagate-generic-term tterm opts state)))
      (tterm->path-cond-equiv new-tt tterm))
    :expand (tterm-propagate-generic-term tterm opts state))

  (defrule tterm-list->path-cond-of-tterm-propagate-generic-args
    (let ((new-args (tterm-propagate-generic-args args opts state)))
      (tterm-list->path-cond-equiv new-args args))
    :in-theory (enable tterm-list->path-cond-equiv)
    :induct (len args))

  (local (defrule lemma-fncall-correct
    (let ((new-tt (tterm-propagate-generic-fncall tterm opts state))
	  (new-args (tterm-propagate-generic-args (tterm->args tterm) opts state)))
      (implies (and (equal (tterm->kind tterm) :fncall)
		    (tterm-correct-p tterm a)
		    (tterm-list-correct-p new-args a))
	       (tterm-correct-p new-tt a)))
    :in-theory (disable tterm-propagate-generic-fncall)
    :expand ((tterm-correct-p (tterm-propagate-generic-fncall tterm opts state) a))
    :prep-lemmas (
      (defrule lemma-1
	(let ((new-tt (tterm-propagate-generic-fncall tterm opts state))
	      (new-args (tterm-propagate-generic-args (tterm->args tterm) opts state)))
	  (implies (equal (tterm->kind tterm) :fncall)
		   (and (tterm-list-equiv (tterm->args new-tt) new-args)
			(equal (tterm->kind new-tt) :fncall))))
	:expand ((tterm-propagate-generic-fncall tterm opts state)))
      (defrule lemma-2
        (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
          (and
            (tterm->judgements-equiv new-tt tterm)
            (tterm->smt-judgements-equiv new-tt tterm)))
        :expand ((tterm-propagate-generic-fncall tterm opts state)))
      (defrule lemma-3
	(let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
          (implies
            (and (acl2::any-p opts)
                                     (acl2::any-p state))
	    (tterm->judgements-and-expr-equiv new-tt tterm)))
	:in-theory (enable tterm->judgements-and-expr-equiv)
;	:expand ((tterm->judgements-and-expr-equiv
;		   (tterm-propagate-generic-fncall tterm opts state) tterm))
	:cases ((equal (tterm->kind tterm) :fncall)))
      (defrule lemma-4
        (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
          (tterm->smt-judgements-and-expr-equiv new-tt tterm))
        :in-theory (enable tterm->smt-judgements-and-expr-equiv)
        :cases ((equal (tterm->kind tterm) :fncall))))))

  (local (defrule lemma-if-correct
    (let ((new-tt (tterm-propagate-generic-if tterm opts state)))
      (implies (and (equal (tterm->kind tterm) :if)
		    (tterm-correct-p tterm a)
		    (tterm-correct-p (tterm-propagate-generic-term (tterm->condx tterm) opts state) a)
		    (tterm-correct-p (tterm-propagate-generic-term (tterm->thenx tterm) opts state) a)
		    (tterm-correct-p (tterm-propagate-generic-term (tterm->elsex tterm) opts state) a))
	       (tterm-correct-p new-tt a)))
    :in-theory (disable tterm-propagate-generic-if)
    :expand ((tterm-correct-p (tterm-propagate-generic-if tterm opts state) a))
    :prep-lemmas (
      (defrule lemma-1
	(let ((new-tt (tterm-propagate-generic-if tterm opts state)))
	  (implies (equal (tterm->kind tterm) :if)
		   (and (equal (tterm->kind new-tt) :if)
			(tterm-equiv (tterm->condx new-tt)
				     (tterm-propagate-generic-term (tterm->condx tterm) opts state))
			(tterm-equiv (tterm->thenx new-tt)
				     (tterm-propagate-generic-term (tterm->thenx tterm) opts state))
			(tterm-equiv (tterm->elsex new-tt)
				     (tterm-propagate-generic-term (tterm->elsex tterm) opts state)))))
	:expand ((tterm-propagate-generic-if tterm opts state))))))

  (defthm-tterm-propagate-generic-flag
    (defthm tterm-correct-p-of-tterm-propagate-generic-term
      (let ((new-tt (tterm-propagate-generic-term tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (tterm-correct-p tterm a))
		 (tterm-correct-p new-tt a)))
      :flag term)

    (defthm tterm-correct-p-of-tterm-propagate-generic-guts
      (let ((new-tt (tterm-propagate-generic-guts tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (tterm-correct-p tterm a))
	  (tterm-correct-p new-tt a)))
      :flag guts)

    (defthm tterm-correct-p-of-tterm-propagate-generic-if
      (let ((new-tt (tterm-propagate-generic-if tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (tterm-correct-p tterm a))
	  (tterm-correct-p new-tt a)))
      :flag if)

    (defthm tterm-correct-p-of-tterm-propagate-generic-fncall
      (let ((new-tt (tterm-propagate-generic-fncall tterm opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (tterm-correct-p tterm a))
	  (tterm-correct-p new-tt a)))
      :flag fncall)

    (defthm tterm-list-correct-p-of-tterm-propagate-generic-args
      (let ((new-args (tterm-propagate-generic-args args opts state)))
	(implies (and (ev-smtcp-meta-extract-global-facts)
		      (alistp a) ; BOZO
		      (tterm-list-correct-p args a))
		 (tterm-list-correct-p new-args a)))
      :flag args)
    :hints(("Goal"
      :in-theory (disable tterm-propagate-generic-fncall tterm-propagate-generic-if))))))

(defun tterm-propagate-fn (name fn-pre fn-post opt-guard)
  (tterm-propagate-defines-fn name fn-pre fn-post opt-guard
    (b* ((defines-name (symcat 'tterm-propagate- name))
	 (fn-term (symcat defines-name '-term))
	 (fn-guts (symcat defines-name '-guts))
	 (fn-term-if (symcat defines-name '-if))
	 (fn-term-fncall (symcat defines-name '-fncall))
	 (fn-args (symcat defines-name '-args))
	 (lemma-pre-type (symcat defines-name '-lemma-pre-type))
	 (lemma-pre-expr (symcat defines-name '-lemma-pre-expr))
	 (lemma-pre-path (symcat defines-name '-lemma-path-pre-cond))
	 (lemma-pre-correct (symcat defines-name '-lemma-pre-correct))
	 (lemma-post-type (symcat defines-name '-lemma-post-type))
	 (lemma-post-expr (symcat defines-name '-lemma-post-expr))
	 (lemma-post-path (symcat defines-name '-lemma-post-path-cond))
	 (lemma-post-correct (symcat defines-name '-lemma-post-correct))
	 (thm-expr (symcat 'tterm->expr-of- fn-term))
	 (thm-path-cond (symcat 'tterm->path-cond-of- fn-term))
	 (thm-correct (symcat 'tterm-correct-p-of- fn-term))
	 (more-actuals '(opts state))
	 (fi-bindings `((tterm-update-term-pre ,fn-pre)
			(tterm-update-term-post ,fn-post)
			(tterm-propagate-generic-term ,fn-term)
			(tterm-propagate-generic-guts ,fn-guts)
			(tterm-propagate-generic-if ,fn-term-if)
			(tterm-propagate-generic-fncall ,fn-term-fncall)
			(tterm-propagate-generic-args ,fn-args))))
      `((local (defrule ,lemma-pre-type
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (tterm-p new-tt))))
        (local (defrule ,lemma-pre-expr
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (tterm->expr-equiv new-tt tterm))))
        (local (defrule ,lemma-pre-path
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (tterm->path-cond-equiv new-tt tterm))))
        (local (defrule ,lemma-pre-correct
	  (let ((new-tt (,fn-pre tterm ,@more-actuals)))
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (alistp a) ; BOZO
			  (tterm-correct-p tterm a))
		     (tterm-correct-p new-tt a)))))
        (local (defrule ,lemma-post-type
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (tterm-p new-tt))))
        (local (defrule ,lemma-post-expr
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (tterm->expr-equiv new-tt tterm))))
        (local (defrule ,lemma-post-path
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (tterm->path-cond-equiv new-tt tterm))))
        (local (defrule ,lemma-post-correct
	  (let ((new-tt (,fn-post tterm ,@more-actuals)))
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (alistp a) ; BOZO
			  (tterm-correct-p tterm a))
		     (tterm-correct-p new-tt a)))))
	(defrule ,thm-expr
	  (let ((new-tt (,fn-term tterm ,@more-actuals)))
	    (tterm->expr-equiv new-tt tterm))
	  :use((:functional-instance tterm->expr-of-tterm-propagate-generic-term
		  ,@fi-bindings))
	  :in-theory '(
	    (:congruence tterm-equiv-implies-equal-tterm-correct-p-1)
	    (:definition ,fn-term)
	    (:definition ,fn-guts)
	    (:definition ,fn-term-if)
	    (:definition ,fn-term-fncall)
	    (:definition ,fn-args)
	    (:equivalence tterm->expr-equiv-is-an-equivalence)
	    (:equivalence tterm->path-cond-equiv-is-an-equivalence)
	    (:forward-chaining tterm->kind-possibilities)
	    (:rewrite ,lemma-pre-type)
	    (:rewrite ,lemma-pre-expr)
	    (:rewrite ,lemma-pre-path)
	    (:rewrite ,lemma-pre-correct)
	    (:rewrite ,lemma-post-type)
	    (:rewrite ,lemma-post-expr)
	    (:rewrite ,lemma-post-path)
	    (:rewrite ,lemma-post-correct)
	    (:rewrite tterm-p-of-tterm-update-path-cond-children)
	    (:type-prescription tterm-correct-p)))

	(defrule ,thm-path-cond
	  (let ((new-tt (,fn-term tterm ,@more-actuals)))
	    (tterm->path-cond-equiv new-tt tterm))
	  :use((:functional-instance tterm->path-cond-of-tterm-propagate-generic-term
		  ,@fi-bindings)))

	(defrule ,thm-correct
	  (let ((new-tt (,fn-term tterm ,@more-actuals)))
	    (implies (and (ev-smtcp-meta-extract-global-facts)
			  (alistp a) ; BOZO
		          (tterm-correct-p tterm a))
		     (tterm-correct-p new-tt a)))
	  :use((:functional-instance tterm-correct-p-of-tterm-propagate-generic-term
		  ,@fi-bindings)))))))

(defmacro tterm-propagate (name &key (pre 'tterm-update-term-default)
				     (post 'tterm-update-term-default)
				     (opt-guard 'acl2::any-p))
  (tterm-propagate-fn name pre post opt-guard))
