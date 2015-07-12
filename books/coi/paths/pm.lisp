; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

#|

Things to do:

[x] look for divergence of "head" <- subsumed by current technqiues
[x] look for inequlity of "tail" <- just added
[x] diverges-from-all-cons, pure cons form using diverges (possible inefficiencies)
[x] I think all-diverge is handled in path.lisp analogous to bag::unique
[ ] add map-cons/map-append to syn::eval
[ ] extend meta-fns to deal with map-cons/map-append
[ ] diverges-from-all-append, w/append
[ ] Extend syntax-remove rules to deal with quoted terms(?)
[ ] Unique members

- case-split idioms(?)
- all-disjoint-or-null predicate


|#


(in-package "CPATH")
;jcd - removed this (include-book "graph")
(include-book "meta")

(local (in-theory (enable (:rewrite wf-syntax-prefix-implies-true-listp)
			  (:definition wf-syntax-prefix))))

;(defcong list::equiv list::equiv
;  (cons a x) 2)

(DEFTHM SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-WORKS-RIGHT
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST
     BAG::X
     BAG::Y BAG::BAG BAG::N BAG::TYPE-ALIST
     BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST
		     BAG::X
		     BAG::Y BAG::BAG BAG::N BAG::TYPE-ALIST
		     BAG::WHOLE-TYPE-ALIST BAG::FLG)
		    BAG::A))
   (BAG::UNIQUE-SUBBAGPS (PD-EVAL BAG::X BAG::A) (PD-EVAL BAG::Y BAG::A) (PD-EVAL BAG::BAG BAG::A)))
  :HINTS
  (("Goal" :use (:functional-instance (:instance bag::SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-WORKS-RIGHT
						 (bag::v (PD-EVAL BAG::X BAG::A))
						 (w (PD-EVAL BAG::Y BAG::A)))
				      (bag::syntax-ev pd-eval)
				      (bag::syntax-ev-list pd-eval-list))
    :in-theory (enable pd-eval-constraint-0)))
  :RULE-CLASSES (:REWRITE :FORWARD-CHAINING))

(DEFTHM SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST-WORKS-RIGHT
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST
     BAG::V
     BAG::X BAG::BAG BAG::N BAG::TYPE-ALIST
     W BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST
		     BAG::V
		     BAG::X BAG::BAG BAG::N BAG::TYPE-ALIST
		     W BAG::WHOLE-TYPE-ALIST BAG::FLG)
		    BAG::A)
    )
   (BAG::UNIQUE-MEMBERP-AND-SUBBAGP
    (PD-EVAL BAG::V BAG::A)
    (PD-EVAL BAG::X BAG::A)
    (PD-EVAL BAG::BAG BAG::A)))
  :HINTS (("goal" :use (:functional-instance bag::SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST-WORKS-RIGHT
					     (bag::syntax-ev pd-eval)
					     (bag::syntax-ev-list pd-eval-list))))
  :rule-classes (:rewrite :forward-chaining))

(DEFTHM SHOW-MEMBERP-FROM-TYPE-ALIST-WORKS-RIGHT
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST
     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
     BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST
		     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
		     BAG::WHOLE-TYPE-ALIST BAG::FLG)
		    BAG::A))
   (MEMBERP (PD-EVAL BAG::X BAG::A)
	    (PD-EVAL BAG::Y BAG::A)))
  :HINTS (("goal" :use (:functional-instance bag::SHOW-MEMBERP-FROM-TYPE-ALIST-WORKS-RIGHT
					     (bag::syntax-ev pd-eval)
					     (bag::syntax-ev-list pd-eval-list))))
  :rule-classes (:rewrite :forward-chaining))


(defthm show-subbagp-from-type-alist-works-right
  (IMPLIES
   (AND
    (BAG::HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST
     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
     BAG::WHOLE-TYPE-ALIST BAG::FLG)
    (PD-EVAL (BAG::HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST
		     BAG::X BAG::Y BAG::N BAG::TYPE-ALIST
		     BAG::WHOLE-TYPE-ALIST BAG::FLG)
		    BAG::A))
   (BAG::SUBBAGP (PD-EVAL BAG::X BAG::A)
		 (PD-EVAL BAG::Y BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance bag::show-subbagp-from-type-alist-works-right
					     (bag::syntax-ev pd-eval)
					     (bag::syntax-ev-list pd-eval-list)))))

(defthm SYNTAX-SUBBAGP-IMPLEMENTS-SUBBAGP
  (implies
   (BAG::SYNTAX-SUBBAGP-FN BAG::A BAG::TERM1 BAG::TERM2)
   (BAG::SUBBAGP (pd-eval BAG::TERM1 BAG::A)
		 (pd-eval BAG::TERM2 BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance bag::SYNTAX-SUBBAGP-IMPLEMENTS-SUBBAGP
					     (bag::syntax-ev pd-eval)
					     (bag::syntax-ev-list pd-eval-list)))))

(defthm sp-of-nil
  (equal (sp nil val r) val)
  :hints (("goal" :in-theory '(cpath::sp-of-non-consp))))

(defun shared-prefix (p1 p2)
  (declare (type t p1 p2))
  (if (consp p1)
      (if (consp p2)
	  (let ((v (car p1)))
	    (if (equal v (car p2))
		(met ((pre p1 p2) (shared-prefix (cdr p1) (cdr p2)))
		     (mv (cons v pre) p1 p2))
	      (mv nil p1 p2)))
	(mv nil p1 p2))
    (mv nil p1 p2)))

;; #|
;; (defthm not-consp-implies-identity
;;   (implies
;;    (not (consp (v0 (shared-prefix p1 p2))))
;;    (and (equal (v1 (shared-prefix p1 p2)) p1)
;; 	(equal (v2 (shared-prefix p1 p2)) p2))))

;; (defun shared-prefix-1 (p1 p2)
;;   (if (and (consp p1)
;; 	   (consp p2)
;; 	   (equal (car p1) (car p2)))
;;       (shared-prefix-1 (cdr p1) (cdr p2))
;;     p1))

;; (defcong list::equiv list::equiv
;;   (shared-prefix-1 p1 p2) 1)

;; (defcong list::equiv equal
;;   (shared-prefix-1 p1 p2) 2)

;; (defun shared-prefix-0 (p1 p2)
;;   (if (and (consp p1)
;; 	   (consp p2)
;; 	   (equal (car p1) (car p2)))
;;       (cons (car p1) (prefix (cdr p1) (cdr p2)))
;;     nil))

;; (defcong list::equiv equal
;;   (shared-prefix-0 p1 p2) 1)

;; (defcong list::equiv equal
;;   (shared-prefix-0 p1 p2) 2)

;; (defthm shared-prefix-0-commutes
;;   (list::equiv (shared-prefix-0 p1 p2)
;; 		   (shared-prefix-0 p2 p1))
;;   :rule-classes ((:rewrite :loop-stopper (p2 p1))))
;; |#

(defun syntax-quote-shared-prefix (p1 p2)
  (declare (type t p1 p2))
  (if (consp p1)
      (cond
       ((syn::consp p2)
	(let ((v (syn::car p2)))
	  (if (syn::quotep v)
	      (let ((v (syn::dequote v)))
		(if (equal v (car p1))
		    (met ((pre p1 p2) (syntax-quote-shared-prefix (cdr p1) (syn::cdr p2)))
			 (mv (cons v pre) p1 p2))
		  (mv nil p1 p2)))
	    (mv nil p1 p2))))
       ((syn::quotep p2)
	(met ((pre p1 p2) (shared-prefix p1 (syn::dequote p2)))
	     (mv pre p1 (syn::enquote p2))))
       (t (mv nil p1 p2)))
    (mv nil p1 p2)))

(defun syntax-shared-prefix (p1 p2)
  (declare (type t p1 p2))
  (cond
   ((syn::quotep p1)
    (met ((pre p1 p2) (syntax-quote-shared-prefix (syn::dequote p1) p2))
	 (mv (syn::enquote pre) (syn::enquote p1) p2)))
   ((syn::quotep p2)
    (met ((pre p2 p1) (syntax-quote-shared-prefix (syn::dequote p2) p1))
	 (mv (syn::enquote pre) p1 (syn::enquote p2))))
   ((syn::consp p1)
    (if (syn::consp p2)
	(let ((v1 (syn::car p1))
	      (v2 (syn::car p2)))
	  (if (equal v1 v2)
	      (met ((pre p1 p2) (syntax-shared-prefix (syn::cdr p1) (syn::cdr p2)))
		   (mv (syn::cons v1 pre) p1 p2))
	    (mv (syn::nil) p1 p2)))
      (mv (syn::nil) p1 p2)))
   ((syn::appendp p1)
    (let ((v1 (syn::arg 1 p1)))
      (cond
       ((syn::appendp p2)
	(let ((v2 (syn::arg 1 p2)))
	  (if (equal v1 v2)
	      (met ((pre p1 p2) (syntax-shared-prefix (syn::arg 2 p1) (syn::arg 2 p2)))
		   (mv (syn::append v1 pre) p1 p2))
	    (mv (syn::nil) p1 p2))))
       ((equal v1 p2)
	(mv v1 v1 (syn::nil)))
       (t
	(mv (syn::nil) p1 p2)))))
   ((equal p1 p2)
    (mv p1 (syn::nil) (syn::nil)))
   (t
    (mv (syn::nil) p1 p2))))

(defun bind-shared-prefix-fn (p1 p2 r0 r1 r2)
  (declare (type t p1 p2 r0 r1 r2))
  (met ((v0 v1 v2) (syntax-shared-prefix p1 p2))
       `((,r0 . ,v0)
	 (,r1 . ,v1)
	 (,r2 . ,v2))))

(defmacro bind-shared-prefix (p1 p2 r0 r1 r2)
  `(bind-shared-prefix-fn ,p1 ,p2 ',r0 ',r1 ',r2))

(defthmd gp-sp-append
  (equal (gp p1 (sp p2 v (gp r0 st)))
	 (gp (append r0 p1) (sp (append r0 p2) v st)))
  :hints (("goal" :in-theory (e/d (append
				   ;cpath::open-gp  ;looped
                                   gp
                                   sp)
				  (cpath::g-to-gp)))))

;; Trigger theorem .. we use bind-shared-prefix instead
;; of triggering a meta-evaluation of shared-prefix
;; since the meta-evaluation will only ever be an
;; approximation (I don't know how we would prove the
;; theory in that case??)
;;
;; That being the case, how will we extend this to
;; lists of paths??  By triggering on gp?
;;
(defthm gp-of-sp-bind-shared-prefix
  (implies
   (and
    (bind-free (bind-shared-prefix p1 p2 r0 r1 r2) (r0 r1 r2))
    (consp r0)
    (equal p1 (append r0 r1))
    (equal p2 (append r0 r2)))
   (equal (gp p1 (sp p2 v st))
	  (gp r1 (sp r2 v (gp r0 st)))))
  :hints (("goal" :in-theory `(gp-sp-append))))

(in-theory
 (enable
  pseudo-termp
  ))

;; You could strengthen this if x and y were "boolean"
;; This would require that meta functions return (syn::bool)
;; values.  That would allow you to

(defthm booleanp-conjoin
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a)))
   (booleanp (pd-eval (syn::conjoin x y) a)))
   :hints (("goal" :in-theory (enable syn::conjoin))))


(defthm pd-eval-conjoin-equal
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a))
    (and x y))
   (equal (pd-eval (syn::conjoin x y) a)
	  (and (pd-eval x a)
	       (pd-eval y a))))
  :hints (("goal" :in-theory (enable syn::conjoin))))

(defthm pd-eval-conjoin-iff
  (implies
   (and x y)
   (iff (pd-eval (syn::conjoin x y) a)
	(and (pd-eval x a)
	     (pd-eval y a))))
  :hints (("goal" :in-theory (enable syn::conjoin))))

(defthm booleanp-make-conjunction
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a)))
   (booleanp (pd-eval (bag::make-conjunction x y) a)))
 :hints (("goal" :in-theory (enable bag::make-conjunction))))

(defthm pd-eval-make-conjunction-equal
  (implies
   (and
    (booleanp (pd-eval x a))
    (booleanp (pd-eval y a)))
   (equal (pd-eval (bag::make-conjunction x y) a)
	  (and (pd-eval x a)
	       (pd-eval y a))))
  :hints (("goal" :in-theory (enable bag::make-conjunction))))

(defthm pd-eval-make-conjunction-iff
  (iff (pd-eval (bag::make-conjunction x y) a)
       (and (pd-eval x a)
	    (pd-eval y a)))
  :hints (("goal" :in-theory (enable bag::make-conjunction))))

;; ===================
;;
;; diverges-from-all
;;
;; ===================

;;
;; begin show-diverges-from-all-from-type-alist
;;

;;
;; We should probably go here eventually ..
;;

#+joe
(defignored show-list-equiv-from-type-alist bag::a (a b type-alist whole-alist)
  (declare (type t a b type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
			      (acl2::type-alistp whole-alist)
                              (pseudo-termp a)
                              (pseudo-termp b)
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-list)
      nil
    (let* ((entry (car type-alist))
	   (fact  (car entry)))
      (or (and (syn::funcall 'equal 2 fact)
	       (bag::ts-non-nil (cadr entry))
	       )
	  (and (syn::funcall 'list::equiv 2 fact)
	       (bag::ts-non-nil (cadr entry))
	       )
	  (show-list-equiv-from-type-alist a b (cdr type-alist) whole-alist)))))

(defignore show-diverges-from-all-from-type-alist bag::a (x list type-alist whole-alist)
  (declare (type t x list type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
			      (acl2::type-alistp whole-alist)
                              (pseudo-termp x)
                              (pseudo-termp list)
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
	   (fact  (car entry)))
      (let ((n (bag::usb16-fix (len whole-alist))))
	(or (and (syn::funcall 'all-diverge 1 fact)
		 (bag::ts-non-nil (cadr entry))
		 (bag::show-unique-memberp-and-subbagp-from-type-alist x list
								       (syn::arg 1 fact)
								       n whole-alist n whole-alist 1))
	    (and (syn::funcall 'all-diverge-from-all 2 fact)
		 (bag::ts-non-nil (cadr entry))
		 (bag::show-memberp-from-type-alist x (syn::arg 1 fact)
						    n whole-alist whole-alist 1)
		 (bag::show-subbagp-from-type-alist list (syn::arg 2 fact) n whole-alist whole-alist 1))
	    (and (syn::funcall 'diverges-from-all 2 fact)
		 (bag::ts-non-nil (cadr entry))
		 (equal x (syn::arg 1 fact))   ;; Probably should be made weaker
		 (bag::show-subbagp-from-type-alist list (syn::arg 2 fact) n whole-alist whole-alist 1))
	    (show-diverges-from-all-from-type-alist x list (cdr type-alist) whole-alist))))))

(defirrelevant show-diverges-from-all-from-type-alist 1 bag::a (x list type-alist whole-alist)
  :hints (("goal" :in-theory (enable
			      BAG::HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-IRRELEVANT
			      bag::hyp-for-show-unique-memberp-and-subbagp-from-type-alist-irrelevant
			      bag::hyp-for-show-memberp-from-type-alist-irrelevant
			      ))))

(defignore hyp-for-show-diverges-from-all-from-type-alist bag::a (x list type-alist whole-alist)
  (declare (type t x list type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
			      (acl2::type-alistp whole-alist)
                              (pseudo-termp x)
                              (pseudo-termp list)
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
	   (fact  (car entry))
	   (n (bag::usb16-fix (len whole-alist))))
      (or (and (syn::funcall 'all-diverge 1 fact)
	       (bag::ts-non-nil (cadr entry))
	       (syn::and (bag::hyp-for-show-unique-memberp-and-subbagp-from-type-alist x list
										       (syn::arg 1 fact)
										       n whole-alist n whole-alist 1)
			 fact))
	  (and (syn::funcall 'all-diverge-from-all 2 fact)
	       (bag::ts-non-nil (cadr entry))
	       (syn::and (bag::hyp-for-show-memberp-from-type-alist x (syn::arg 1 fact)
								    n whole-alist whole-alist 1)
			 (bag::hyp-for-show-subbagp-from-type-alist list (syn::arg 2 fact) n whole-alist whole-alist 1)
			 fact))
	  (and (syn::funcall 'diverges-from-all 2 fact)
	       (bag::ts-non-nil (cadr entry))
	       (equal x (syn::arg 1 fact))   ;; Probably should be made weaker
	       (syn::and (bag::hyp-for-show-subbagp-from-type-alist list (syn::arg 2 fact) (bag::usb16-fix (len whole-alist))
								    whole-alist whole-alist 1)
			 fact))
	  (hyp-for-show-diverges-from-all-from-type-alist x list (cdr type-alist) whole-alist)))))

(defirrelevant hyp-for-show-diverges-from-all-from-type-alist 1 bag::a (x list type-alist whole-alist)
  :hints (("goal" :in-theory (enable
			      BAG::HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-IRRELEVANT
			      bag::hyp-for-show-unique-memberp-and-subbagp-from-type-alist-irrelevant
			      bag::hyp-for-show-memberp-from-type-alist-irrelevant
			      ))))

(defthm type-alistp-pseudo-termp
  (implies
   (ACL2::TYPE-ALISTP TYPE-ALIST)
   (pseudo-termp (caar type-alist)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable ACL2::TYPE-ALISTP))))

(defthm pseudo-termp-hyp-for-show-diverges-from-all-from-type-alist
  (implies
   (and
    (acl2::type-alistp type-alist)
    (acl2::type-alistp whole-alist)
    (pseudo-termp x)
    (pseudo-termp list))
   (pseudo-termp (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist)))
  :hints (("goal" :in-theory (enable syn::conjoin syn::open-nth))))

(defthm show-diverges-from-all-from-type-alist-to-hyp-for
  (iff (show-diverges-from-all-from-type-alist x list type-alist whole-alist)
       (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist)))


(defthm diverges-from-all-from-unique-memberp-and-subbagp-all-diverge
  (implies
   (and
    (all-diverge bag)
    (bag::unique-memberp-and-subbagp x list bag))
   (diverges-from-all x list))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable diverges-from-all))))

(defthmd diverges-from-all-from-memberp-subbagp-all-diverge-from-all-1
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::memberp a x)
    (bag::subbagp list y))
   (diverges-from-all a list)))

(defthmd diverges-from-all-from-memberp-subbagp-all-diverge-from-all-2
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::memberp a y)
    (bag::subbagp list x))
   (diverges-from-all a list)))

(defthm pd-eval-hyp-for-show-diverges-from-all-from-type-alist-implies-diverges-from-all
  (implies
   (and
    (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist)
    (pd-eval (hyp-for-show-diverges-from-all-from-type-alist x list type-alist whole-alist) bag::a))
   (diverges-from-all (pd-eval x bag::a) (pd-eval list bag::a)))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :in-theory (e/d (diverges-from-all-from-memberp-subbagp-all-diverge-from-all-2
			    diverges-from-all-from-memberp-subbagp-all-diverge-from-all-1
			    syn::open-nth syn::conjoin) (DIVERGES-FROM-ALL-BY-MEMBERSHIP))))
  :rule-classes (:rewrite :forward-chaining))

;;
;; end show-diverges-from-all-from-type-alist
;;

(defignore show-diverges-from-all-from-quote-list bag::a (x list type-alist)
  (declare (type (satisfies pseudo-termp) x)
	   (type (satisfies acl2::type-alistp) type-alist))
  (if (consp list)
      (and (show-prefix-diverge-from-alist x (syn::enquote (car list)) type-alist)
	   (show-diverges-from-all-from-quote-list x (cdr list) type-alist))
    t))

(defirrelevant show-diverges-from-all-from-quote-list 1 bag::a (x list type-alist)
  :hints (("goal" :in-theory (enable
			      hyp-for-show-prefix-diverge-from-alist-irrelevant
			      ))))

(defignore hyp-for-show-diverges-from-all-from-quote-list bag::a (x list type-alist)
  (declare (type (satisfies pseudo-termp) x)
	   (type (satisfies acl2::type-alistp) type-alist))
  (if (consp list)
      (syn::and (hyp-for-show-prefix-diverge-from-alist x (syn::enquote (car list)) type-alist)
		(hyp-for-show-diverges-from-all-from-quote-list x (cdr list) type-alist))
    (syn::true)))

(defthm pseudo-termp-hyp-for-show-diverges-from-all-from-quote-list
  (implies
   (and
    (acl2::type-alistp type-alist)
    (pseudo-termp x))
   (pseudo-termp (hyp-for-show-diverges-from-all-from-quote-list x list type-alist))))

(defirrelevant hyp-for-show-diverges-from-all-from-quote-list 1 bag::a (x list type-alist)
  :hints (("goal" :in-theory (enable
			      hyp-for-show-prefix-diverge-from-alist-irrelevant
			      ))))

(defthm show-diverges-from-all-from-quote-list-to-hyp-for
  (iff (show-diverges-from-all-from-quote-list x list type-alist)
       (hyp-for-show-diverges-from-all-from-quote-list x list type-alist)))

(defthm pd-eval-diverge-from-hyp-for-show-prefix-diverge-from-alist-stronger
  (implies
   (and
    (hyp-for-show-prefix-diverge-from-alist x y type-alist)
    (pd-eval (hyp-for-show-prefix-diverge-from-alist x y type-alist) bag::a)
    (equal yv (pd-eval y bag::a)))
   (diverge yv (pd-eval x bag::a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm show-diverges-from-all-from-quote-list-implies-diverges-from-all
  (implies
   (and
    (hyp-for-show-diverges-from-all-from-quote-list x list type-alist)
    (pd-eval (hyp-for-show-diverges-from-all-from-quote-list x list type-alist) bag::a))
   (diverges-from-all (pd-eval x bag::a) list))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (e/d (syn::open-nth syn::conjoin diverges-from-all)
                                  (DIVERGES-FROM-ALL-OF-CDR ;efficiency
                                   NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
                                   )))))

(defignore simplify-diverges-from-all-from-cons-list bag::a (x list type-alist)
  (declare (type (satisfies pseudo-termp) x list)
	   (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp list)
    (let ((y (syn::car list)))
      (met ((simp term) (simplify-diverges-from-all-from-cons-list x (syn::cdr list) type-alist))
	(if (show-prefix-diverge-from-alist x y type-alist)
	    (mv t term)
	  (mv simp (syn::and term `(diverge ,x ,y)))))))
   ((syn::appendp list)
    (met ((s1 t1) (simplify-diverges-from-all-from-cons-list x (syn::arg 1 list) type-alist))
      (met ((s2 t2) (simplify-diverges-from-all-from-cons-list x (syn::arg 2 list) type-alist))
	(mv (or s1 s2) (syn::and t1 t2)))))
   ((syn::quotep list)
    ;; We could use a simplify-diverges-from-all-from-quote-list
    (if (show-diverges-from-all-from-quote-list x (syn::dequote list) type-alist)
	(mv t (syn::true))
      (mv nil `(diverges-from-all ,x ,list))))
   (t
    (if (show-diverges-from-all-from-type-alist x list type-alist type-alist)
	(mv t (syn::true))
      (mv nil `(diverges-from-all ,x ,list))))))

(defirrelevant simplify-diverges-from-all-from-cons-list 1 bag::a (x list type-alist)
  :hints (("goal" :in-theory (enable
			      hyp-for-show-diverges-from-all-from-type-alist-irrelevant
			      hyp-for-show-prefix-diverge-from-alist-irrelevant
			      hyp-for-show-diverges-from-all-from-quote-list-irrelevant
			      ))))

(defignore hyp-for-simplify-diverges-from-all-from-cons-list bag::a (x list type-alist)
  (declare (type (satisfies pseudo-termp) x list)
	   (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp list)
    (syn::and (or (hyp-for-show-prefix-diverge-from-alist x (syn::car list) type-alist)
		  (syn::true))
	      (hyp-for-simplify-diverges-from-all-from-cons-list x (syn::cdr list) type-alist)))
   ((syn::appendp list)
    (syn::and
     (hyp-for-simplify-diverges-from-all-from-cons-list x (syn::arg 1 list) type-alist)
     (hyp-for-simplify-diverges-from-all-from-cons-list x (syn::arg 2 list) type-alist)))
   ((syn::quotep list)
    (or (hyp-for-show-diverges-from-all-from-quote-list x (syn::dequote list) type-alist)
	(syn::true)))
   (t
    (or (hyp-for-show-diverges-from-all-from-type-alist x list type-alist type-alist)
	(syn::true)))))

(defthm iff-hyp-for-simplify-diverges-from-all-from-cons-list
  (iff (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist) t))

(defthm iff-v1-simplify-diverges-from-all-from-cons-list
  (iff (v1 (simplify-diverges-from-all-from-cons-list x list type-alist)) t))

(defirrelevant hyp-for-simplify-diverges-from-all-from-cons-list 1 bag::a (x list type-alist)
  :hints (("goal" :in-theory (enable
			      hyp-for-show-diverges-from-all-from-type-alist-irrelevant
			      hyp-for-show-prefix-diverge-from-alist-irrelevant
			      hyp-for-show-diverges-from-all-from-quote-list-irrelevant
			      ))))

(defthm pseudo-termp-hyp-for-simplify-diverges-from-all-from-cons-list
  (implies
   (and
    (acl2::type-alistp type-alist)
    (pseudo-termp x)
    (pseudo-termp list))
   (pseudo-termp (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist))))

#+joe
(defthm simplify-diverges-from-all-from-cons-list-to-hyp-for
  (iff (simplify-diverges-from-all-from-cons-list x list type-alist)
       (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist)))

(defthm simplify-diverges-from-all-from-cons-list-implies-diverges-from-all
  (implies
   (pd-eval (hyp-for-simplify-diverges-from-all-from-cons-list x list type-alist) bag::a)
   (equal (pd-eval (v1 (simplify-diverges-from-all-from-cons-list x list type-alist)) bag::a)
	  (diverges-from-all (pd-eval x bag::a) (pd-eval list bag::a))))
  ;; :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :induct (simplify-diverges-from-all-from-cons-list x list type-alist)
	   :in-theory (enable syn::open-nth diverges-from-all))
	  (and acl2::stable-under-simplificationp
	       `(:in-theory (enable syn::conjoin)))))

;; begin all-diverge-from-all

(defignore show-all-diverge-from-all-type-alist bag::a (x list n type-alist whole-alist)
  (declare (type t x list type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
			      (acl2::type-alistp whole-alist)
                              (pseudo-termp x)
                              (pseudo-termp list)
			      (acl2::unsigned-byte-p 16 n)
			      )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :measure (len type-alist)
		  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
	   (fact  (car entry)))
      (or (and (syn::funcall 'all-diverge-from-all 2 fact)
	       (bag::ts-non-nil (cadr entry))
	       (or (and (bag::show-subbagp-from-type-alist x    (syn::arg 1 fact) n whole-alist whole-alist 1)
			(bag::show-subbagp-from-type-alist list (syn::arg 2 fact) n whole-alist whole-alist 1))
		   (and (bag::show-subbagp-from-type-alist x    (syn::arg 2 fact) n whole-alist whole-alist 1)
			(bag::show-subbagp-from-type-alist list (syn::arg 1 fact) n whole-alist whole-alist 1))))
	  (and (syn::funcall 'all-diverge 1 fact)
	       (bag::ts-non-nil (cadr entry))
	       (bag::show-unique-subbagps-from-type-alist x list
							  (syn::arg 1 fact)
							  n whole-alist whole-alist 1))
	  (show-all-diverge-from-all-type-alist x list n (cdr type-alist) whole-alist)))))

(defignore hyp-for-show-all-diverge-from-all-type-alist bag::a (x list n type-alist whole-alist)
  (declare (type t x list type-alist)
           (xargs :guard (and (acl2::type-alistp type-alist)
			      (acl2::type-alistp whole-alist)
                              (pseudo-termp x)
                              (pseudo-termp list)
			      (acl2::unsigned-byte-p 16 n)
                              )
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :measure (len type-alist)
		  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
	   (fact  (car entry)))
      (or (and (syn::funcall 'all-diverge-from-all 2 fact)
	       (bag::ts-non-nil (cadr entry))
	       (or (syn::and (bag::hyp-for-show-subbagp-from-type-alist x    (syn::arg 1 fact) n whole-alist whole-alist 1)
			     (bag::hyp-for-show-subbagp-from-type-alist list (syn::arg 2 fact) n whole-alist whole-alist 1)
			     fact)
		   (syn::and (bag::hyp-for-show-subbagp-from-type-alist x    (syn::arg 2 fact) n whole-alist whole-alist 1)
			     (bag::hyp-for-show-subbagp-from-type-alist list (syn::arg 1 fact) n whole-alist whole-alist 1)
			     fact)))
	  (and (syn::funcall 'all-diverge 1 fact)
	       (bag::ts-non-nil (cadr entry))
	       (syn::and
		(bag::hyp-for-show-unique-subbagps-from-type-alist x list
								   (syn::arg 1 fact)
								   n whole-alist whole-alist 1)
		fact))
	  (hyp-for-show-all-diverge-from-all-type-alist x list n (cdr type-alist) whole-alist)))))

(defirrelevant show-all-diverge-from-all-type-alist 1 bag::a (x list n type-alist full-alist)
  :hints (("goal" :in-theory (enable
			      bag::hyp-for-show-subbagp-from-type-alist-irrelevant
			      bag::hyp-for-show-unique-subbagps-from-type-alist-irrelevant
			      ))))

(defirrelevant hyp-for-show-all-diverge-from-all-type-alist 1 bag::a (x list n type-alist full-alist)
  :hints (("goal" :in-theory (enable
			      bag::hyp-for-show-subbagp-from-type-alist-irrelevant
			      bag::hyp-for-show-unique-subbagps-from-type-alist-irrelevant
			      ))))

(defthm pseudo-termp-hyp-for-show-all-diverge-from-all-type-alist
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp list)
    (acl2::type-alistp type-alist)
    (acl2::type-alistp full-alist)
    )
   (pseudo-termp (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist))))

(defthm iff-show-all-diverge-from-all-type-alist-hyps
  (iff (show-all-diverge-from-all-type-alist x list n type-alist full-alist)
       (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist)))

(defthmd all-diverge-from-all-diverge-subbagp-1
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::subbagp a x)
    (bag::subbagp b y))
   (all-diverge-from-all a b)))

(defthmd all-diverge-from-all-diverge-subbagp-2
  (implies
   (and
    (all-diverge-from-all x y)
    (bag::subbagp a y)
    (bag::subbagp b x))
   (all-diverge-from-all a b)))

(defthmd all-diverge-from-all-from-unique-subbagps-all-diverge
  (implies
   (and
    (all-diverge list)
    (bag::unique-subbagps x y list))
   (and (all-diverge-from-all x y)
	(all-diverge-from-all y x)))
  :rule-classes (:rewrite :forward-chaining))


(defthm show-all-diverge-from-all-type-alist-works
  (implies
   (and
    (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist)
    (pd-eval (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist) bag::a))
   (all-diverge-from-all (pd-eval x bag::a) (pd-eval list bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :do-not '(generalize eliminate-destructors)
	   :in-theory (e/d (syn::open-nth
			    SYN::CONJOIN
			    all-diverge-from-all-from-unique-subbagps-all-diverge
			    all-diverge-from-all-diverge-subbagp-1
			    all-diverge-from-all-diverge-subbagp-2
			    )
			   (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP)))))

(defthm show-all-diverge-from-all-type-alist-works-2
  (implies
   (and
    (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist)
    (pd-eval (hyp-for-show-all-diverge-from-all-type-alist x list n type-alist full-alist) bag::a))
   (all-diverge-from-all (pd-eval list bag::a) (pd-eval x bag::a)))
  :hints (("goal" :in-theory (disable show-all-diverge-from-all-type-alist-works)
	   :use show-all-diverge-from-all-type-alist-works))
  :rule-classes (:rewrite :forward-chaining))


(defignore simplify-all-diverge-from-all-cons-list bag::a (swap x list type-alist)
  (declare (type (satisfies pseudo-termp) x list)
	   (type (satisfies acl2::type-alistp) type-alist)
	   (xargs :hints (("goal" :in-theory (enable syn::open-nth)))
		  :measure (+ (if swap 1 0) (acl2-count x) (acl2-count list))))
  (cond
   ((syn::consp x)
    (let ((y (syn::car x)))
      (met ((s1 t1) (simplify-diverges-from-all-from-cons-list y list type-alist))
	(met ((s2 t2) (simplify-all-diverge-from-all-cons-list swap (syn::cdr x) list type-alist))
	  (mv (or s1 s2) (syn::and t1 t2))))))
   ((syn::appendp x)
    (met ((s1 t1) (simplify-all-diverge-from-all-cons-list swap (syn::arg 1 x) list type-alist))
      (met ((s2 t2) (simplify-all-diverge-from-all-cons-list swap (syn::arg 2 x) list type-alist))
	(mv (or s1 s2) (syn::and t1 t2)))))
   (swap
    (simplify-all-diverge-from-all-cons-list nil list x type-alist))
   (t
    (if (show-all-diverge-from-all-type-alist x list (bag::usb16-fix (len type-alist)) type-alist type-alist)
	(mv t (syn::true))
      (mv nil `(all-diverge-from-all ,x ,list))))))

(defirrelevant simplify-all-diverge-from-all-cons-list 1 bag::a (swap x list type-alist)
  :hints (("goal" :in-theory (enable
			      simplify-diverges-from-all-from-cons-list-irrelevant
			      hyp-for-simplify-diverges-from-all-from-cons-list-irrelevant
			      hyp-for-show-all-diverge-from-all-type-alist-irrelevant
			      ))))

(defignore hyp-for-simplify-all-diverge-from-all-cons-list bag::a (swap x list type-alist)
  (declare (type (satisfies pseudo-termp) x list)
	   (type (satisfies acl2::type-alistp) type-alist)
	   (xargs :hints (("goal" :in-theory (enable syn::open-nth)))
		  :measure (+ (if swap 1 0) (acl2-count x) (acl2-count list))))
  (cond
   ((syn::consp x)
    (let ((y (syn::car x)))
      (syn::and (hyp-for-simplify-diverges-from-all-from-cons-list y list type-alist)
		(hyp-for-simplify-all-diverge-from-all-cons-list swap (syn::cdr x) list type-alist))))
   ((syn::appendp x)
    (syn::and (hyp-for-simplify-all-diverge-from-all-cons-list swap (syn::arg 1 x) list type-alist)
	      (hyp-for-simplify-all-diverge-from-all-cons-list swap (syn::arg 2 x) list type-alist)))
   (swap
    (hyp-for-simplify-all-diverge-from-all-cons-list nil list x type-alist))
   (t
    (or (hyp-for-show-all-diverge-from-all-type-alist x list (bag::usb16-fix (len type-alist)) type-alist type-alist)
	(syn::true)))))

(defirrelevant hyp-for-simplify-all-diverge-from-all-cons-list 1 bag::a (swap x list type-alist)
  :hints (("goal" :in-theory (enable
			      hyp-for-simplify-diverges-from-all-from-cons-list-irrelevant
			      hyp-for-show-all-diverge-from-all-type-alist-irrelevant
			      ))))

(defthm pseudo-termp-hyp-for-simplify-all-diverge-from-all-cons-list
  (implies
   (and
    (pseudo-termp x)
    (pseudo-termp list)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-simplify-all-diverge-from-all-cons-list swap x list type-alist))))

(defthm iff-simplify-all-diverge-from-all-cons-list-to-hyp-for
  (and (iff (v1 (simplify-all-diverge-from-all-cons-list swap x list type-alist)) t)
       (iff (hyp-for-simplify-all-diverge-from-all-cons-list swap x list type-alist) t)))

;; DAG -- move me!! -- this rules belong in "path"

(defthmd all-diverge-from-all-append-1
  (equal (all-diverge-from-all (append x y) z)
	 (and (all-diverge-from-all x z)
	      (all-diverge-from-all y z)))
  :hints (("goal" :in-theory (enable append all-diverge-from-all))))

(defthmd all-diverge-from-all-append-2
  (equal (all-diverge-from-all z (append x y))
	 (and (all-diverge-from-all z x)
	      (all-diverge-from-all z y)))
  :hints (("goal" :in-theory (enable append all-diverge-from-all))))


(defthm all-diverge-from-all-commute
  (implies
   (all-diverge-from-all x y)
   (all-diverge-from-all y x))
  :rule-classes (:forward-chaining))

(defthm simplify-all-diverge-from-all-cons-list-works
  (implies
   (pd-eval (hyp-for-simplify-all-diverge-from-all-cons-list swap x list type-alist) bag::a)
   (equal (pd-eval (v1 (simplify-all-diverge-from-all-cons-list swap x list type-alist)) bag::a)
	  (all-diverge-from-all (pd-eval x bag::a) (pd-eval list bag::a))))
  ;;:rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :induct (simplify-all-diverge-from-all-cons-list swap x list type-alist)
	   :in-theory (e/d (syn::open-nth
			    all-diverge-from-all-append-1
			    all-diverge-from-all-append-2)
			   (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP)))
	  (and acl2::stable-under-simplificationp
	       `(:in-theory (enable syn::conjoin)))))

;; end all-diverge-from-all

(DEFTHM SHOW-ALL-DIVERGE-FROM-TYPE-ALIST-WORKS-RIGHT-pd-eval
  (IMPLIES
   (AND (HYP-FOR-SHOW-ALL-DIVERGE-FROM-TYPE-ALIST
	 X N TYPE-ALIST WHOLE-TYPE-ALIST)
	(PD-EVAL (HYP-FOR-SHOW-ALL-DIVERGE-FROM-TYPE-ALIST
			 X N TYPE-ALIST WHOLE-TYPE-ALIST)
			BAG::A)
	)
   (ALL-DIVERGE (PD-EVAL X BAG::A)))
  :RULE-CLASSES (:REWRITE :FORWARD-CHAINING)
  :HINTS (("Goal" :use (:functional-instance SHOW-ALL-DIVERGE-FROM-TYPE-ALIST-WORKS-RIGHT
					     (path-syntax-ev  pd-eval)
					     (path-syntax-ev-list pd-eval-list))
           :in-theory (enable pd-eval-constraint-0))))


(defthm pd-eval-show-all-diverge-from-all-from-type-alist-works-right
  (IMPLIES
   (AND (PD-EVAL (HYP-FOR-SHOW-ALL-DIVERGE-FROM-ALL-FROM-TYPE-ALIST
			 X Y N TYPE-ALIST WHOLE-TYPE-ALIST)
			BAG::A)
	(HYP-FOR-SHOW-ALL-DIVERGE-FROM-ALL-FROM-TYPE-ALIST
	 X Y N TYPE-ALIST WHOLE-TYPE-ALIST))
   (ALL-DIVERGE-FROM-ALL (PD-EVAL X BAG::A)
			 (PD-EVAL Y BAG::A)))
  :rule-classes (:rewrite :forward-chaining)
  :HINTS (("Goal" :use (:functional-instance show-all-diverge-from-all-from-type-alist-works-right
					     (path-syntax-ev  pd-eval)
					     (path-syntax-ev-list pd-eval-list)))))


(defignore simplify-all-diverge-from-cons-list bag::a (list type-alist)
  (declare (type (satisfies pseudo-termp) list)
	   (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp list)
    (met ((simp term) (simplify-all-diverge-from-cons-list (syn::cdr list) type-alist))
      (met ((s2 t2) (simplify-diverges-from-all-from-cons-list (syn::car list) (syn::cdr list) type-alist))
	(mv (or simp s2) (syn::and term t2)))))
   ((syn::appendp list)
    (met ((s1 t1) (simplify-all-diverge-from-cons-list (syn::arg 1 list) type-alist))
      (met ((s2 t2) (simplify-all-diverge-from-cons-list  (syn::arg 2 list) type-alist))
	(met ((s3 t3) (simplify-all-diverge-from-all-cons-list t (syn::arg 1 list) (syn::arg 2 list) type-alist))
	  (mv (or s1 s2 s3) (syn::and t1 t2 t3))))))
   ((syn::quotep list)
    (let ((list (syn::dequote list)))
      (mv t (syn::enquote (all-diverge list)))))
   (t
    (if (show-all-diverge-from-type-alist list (bag::usb16-fix (len type-alist)) type-alist type-alist)
	(mv t (syn::true))
      (mv nil `(all-diverge ,list))))))

(defignore hyp-for-simplify-all-diverge-from-cons-list bag::a (list type-alist)
  (declare (type (satisfies pseudo-termp) list)
	   (type (satisfies acl2::type-alistp) type-alist))
  (cond
   ((syn::consp list)
    (syn::and (or (hyp-for-simplify-diverges-from-all-from-cons-list (syn::car list) (syn::cdr list) type-alist)
		  (syn::true))
	      (hyp-for-simplify-all-diverge-from-cons-list (syn::cdr list) type-alist)))
   ((syn::appendp list)
    (syn::and (hyp-for-simplify-all-diverge-from-cons-list (syn::arg 1 list) type-alist)
	      (hyp-for-simplify-all-diverge-from-cons-list  (syn::arg 2 list) type-alist)
	      (hyp-for-simplify-all-diverge-from-all-cons-list t (syn::arg 1 list) (syn::arg 2 list) type-alist)))
   ((syn::quotep list)
    (syn::true))
   (t
    (or (hyp-for-show-all-diverge-from-type-alist list (bag::usb16-fix (len type-alist)) type-alist type-alist)
	(syn::true)))))

(defthm iff-hyp-for-simplify-all-diverge-from-cons-list
  (iff (hyp-for-simplify-all-diverge-from-cons-list list type-alist) t))

(defthm iff-v1-simplify-all-diverge-from-cons-list
  (iff (v1 (simplify-all-diverge-from-cons-list list type-alist)) t))

(defirrelevant simplify-all-diverge-from-cons-list 2 bag::a (list type-alist)
  :hints (("goal" :in-theory (enable
			      simplify-diverges-from-all-from-cons-list-irrelevant
			      simplify-all-diverge-from-all-cons-list-irrelevant
			      hyp-for-show-all-diverge-from-type-alist-irrelevant
			      ))))

(defirrelevant hyp-for-simplify-all-diverge-from-cons-list 1 bag::a (list type-alist)
  :hints (("goal" :in-theory (enable
			      hyp-for-simplify-diverges-from-all-from-cons-list-irrelevant
			      hyp-for-simplify-all-diverge-from-all-cons-list-irrelevant
			      hyp-for-show-all-diverge-from-type-alist-irrelevant
			      ))))

(defthm pseudo-termp-hyp-for-simplify-all-diverge-from-cons-list
  (implies
   (and
    (pseudo-termp list)
    (acl2::type-alistp type-alist))
   (pseudo-termp (hyp-for-simplify-all-diverge-from-cons-list list type-alist))))

(defthmd all-diverge-cons
  (equal (all-diverge (cons a x))
	 (and (diverges-from-all a x)
	      (all-diverge x)))
  :hints (("goal" :in-theory (enable append all-diverge all-diverge-from-all))))

(defthmd all-diverge-append
  (equal (all-diverge (append x y))
	 (and (all-diverge x)
	      (all-diverge y)
	      (all-diverge-from-all x y)))
  :hints (("goal" :in-theory (enable append all-diverge all-diverge-from-all))))

(defthm hyp-for-simplify-all-diverge-from-cons-list-works
  (implies
   (pd-eval (hyp-for-simplify-all-diverge-from-cons-list list type-alist) bag::a)
   (equal (pd-eval (v1 (simplify-all-diverge-from-cons-list list type-alist)) bag::a)
	  (all-diverge (pd-eval list bag::a))))
  ;; :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :induct (SIMPLIFY-ALL-DIVERGE-FROM-CONS-LIST-FN BAG::A LIST TYPE-ALIST)
	   :in-theory (e/d (syn::open-nth)
			   (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
			    ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
			    ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP
			    ALL-DIVERGE-BY-MEMBERSHIP)))
	  (and acl2::stable-under-simplificationp
	       '(:in-theory (e/d (all-diverge-cons
				  all-diverge-append
				  syn::open-nth
				  syn::conjoin)
				 (ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
				  ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP-DRIVER
				  ALL-DIVERGE-FROM-ALL-BY-MEMBERSHIP
				  ALL-DIVERGE-BY-MEMBERSHIP))))))

(set-state-ok t)

(defun appears-negated (term clause)
  (declare (type t term clause))
  (if (consp clause)
      (let ((fact (car clause)))
	(or (equal term fact) ;; oh, for eq!
	    (appears-negated term (cdr clause))))
    nil))

(defun simplify-all-diverge-from-mfc (term mfc state)
  (declare (ignore state)
	   (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge 1 term)
      (let ((type-alist (acl2::mfc-type-alist mfc))
	    (clause     (acl2::mfc-clause mfc)))
	(if (or (acl2::mfc-ancestors mfc)
		(appears-negated term clause))
	    (let ((bag (syn::arg 1 term)))
	      (met ((simp tx) (simplify-all-diverge-from-cons-list-fn nil bag type-alist))
		(if simp tx term)))
	  term))
    term))

(defun hyp-for-simplify-all-diverge-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge 1 term)
      (let ((bag  (syn::arg 1 term)))
	(let ((type-alist (acl2::mfc-type-alist mfc)))
	  (let ((hyp (hyp-for-simplify-all-diverge-from-cons-list-fn nil bag type-alist)))
	    (bag::bind-extra-vars-in-hyp hyp term))))
    (syn::nil)))

(defthm meta-rule-to-simplify-all-diverge
  (implies (pd-eval (hyp-for-simplify-all-diverge-from-mfc term mfc state) bag::a)
           (equal (pd-eval term bag::a)
		  (pd-eval (simplify-all-diverge-from-mfc term mfc state) bag::a)))
  :rule-classes ((:meta :trigger-fns (all-diverge)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable
			      syn::open-nth
			      hyp-for-simplify-all-diverge-from-cons-list-irrelevant
			      simplify-all-diverge-from-cons-list-irrelevant
			      ))))

(defun show-all-diverge-from-all-from-mfc-2 (term mfc state)
  (declare (ignore state)
	   (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc))
	    (clause     (acl2::mfc-clause mfc)))
	(let ((x (syn::arg 1 term))
	      (y (syn::arg 2 term))
	      (n (bag::usb16-fix (len type-alist))))
	  (if (or (acl2::mfc-ancestors mfc)
		  (appears-negated term clause))
	      (if (show-all-diverge-from-all-from-type-alist-fn nil x y n type-alist type-alist)
		  (syn::true)
		(met ((s1 t1) (simplify-all-diverge-from-all-cons-list-fn nil :swap x y type-alist))
		  (if s1 t1 term)))
	    term)))
    term))

;; DAG -- who is using this name ??
(defun hyp-for-show-all-diverge-from-all-from-mfc-2 (term mfc state)
  (declare (ignore state)
	   (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'all-diverge-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc)))
	(let ((x (syn::arg 1 term))
	      (y (syn::arg 2 term))
	      (n (bag::usb16-fix (len type-alist))))
	  (let ((hyp (hyp-for-show-all-diverge-from-all-from-type-alist-fn nil x y n type-alist type-alist)))
	    (let ((hyp (or hyp
			   (hyp-for-simplify-all-diverge-from-all-cons-list-fn nil :swap x y type-alist))))
	      (bag::bind-extra-vars-in-hyp hyp term)))))
    term))

(defthm *meta*-all-diverge-from-all
  (implies
   (pd-eval (hyp-for-show-all-diverge-from-all-from-mfc-2 term mfc state) bag::a)
   (equal (pd-eval term bag::a)
	  (pd-eval (show-all-diverge-from-all-from-mfc-2 term mfc state) bag::a)))
  :hints (("goal" :in-theory (e/d
			      (
			       syn::open-nth
			       show-all-diverge-from-all-from-type-alist-irrelevant
			       SIMPLIFY-ALL-DIVERGE-FROM-ALL-CONS-LIST-irrelevant
			       hyp-for-show-all-diverge-from-all-from-type-alist-irrelevant
			       hyp-for-simplify-all-diverge-from-all-cons-list-irrelevant
			       )
			      nil
			      )))
  :rule-classes ((:meta :trigger-fns (all-diverge-from-all)
                        :backchain-limit-lst 0
                        )))

(defun show-diverges-from-all-from-mfc (term mfc state)
  (declare (ignore state)
	   (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'diverges-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc))
	    (clause     (acl2::mfc-clause mfc)))
	(let ((x    (syn::arg 1 term))
	      (list (syn::arg 2 term)))
	  (if (or (acl2::mfc-ancestors mfc)
		  (appears-negated term clause))
	      (if (show-diverges-from-all-from-type-alist-fn nil x list type-alist type-alist)
		  (syn::true)
		(met ((s1 t1) (simplify-diverges-from-all-from-cons-list-fn nil x list type-alist))
		  (if s1 t1 term)))
	    term)))
    term))

(defun hyp-for-show-diverges-from-all-from-mfc (term mfc state)
  (declare (ignore state)
	   (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (syn::funcall 'diverges-from-all 2 term)
      (let ((type-alist (acl2::mfc-type-alist mfc)))
	(let ((x    (syn::arg 1 term))
	      (list (syn::arg 2 term)))
	  (let ((hyp (hyp-for-show-diverges-from-all-from-type-alist-fn nil x list type-alist type-alist)))
	    (let ((hyp (or hyp
			   (hyp-for-simplify-diverges-from-all-from-cons-list-fn nil x list type-alist))))
	      (bag::bind-extra-vars-in-hyp hyp term)))))
    term))

(defthm *meta*-diverges-from-all
  (implies
   (pd-eval (hyp-for-show-diverges-from-all-from-mfc term mfc state) bag::a)
   (equal (pd-eval term bag::a)
	  (pd-eval (show-diverges-from-all-from-mfc term mfc state) bag::a)))
  :hints (("goal" :in-theory (e/d
			      (
			       syn::open-nth
			       hyp-for-show-diverges-from-all-from-type-alist-irrelevant
			       simplify-diverges-from-all-from-cons-list-irrelevant
			       hyp-for-simplify-diverges-from-all-from-cons-list-irrelevant
			       )
			      (DIVERGES-FROM-ALL-BY-MEMBERSHIP
			       ))))
  :rule-classes ((:meta :trigger-fns (diverges-from-all)
                        :backchain-limit-lst 0
                        )))


;; All diverge from all .. assuming we are dealing in atomic functions.

;; (show-all-diverge-from-all-from-mfc term mfc state)

;; (show-diverges-from-all term mfc state)
;; (bag::subbagp x y)
;;  => (show-diverges-..)
;;
;; (show-diverge-from-mfc term mfc state)
;; (bag::memberp x list)
;; => (show-diverges-from-all a x mfc state)

;; ================================================
;;
;; Some possible all-diverge-from-all directions ..
;;
;; ================================================

(defthm dominates-transitive-three
  (implies
   (and
    (dominates b x)
    (dominates s b))
   (dominates s x)))

(defun fix-prefix (prefix)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
	(case (car entry)
	      (:cons
	       (cons entry (fix-prefix (cdr prefix))))
	      (:append
	       (cons entry (fix-prefix (cdr prefix))))
	      (:quote
	       (let ((entry (cons :quote (list::fix (cdr entry)))))
		 (cons entry nil)))
	      (t nil)))
    nil))

(defun prefix-equiv (x y)
  (declare (type (satisfies wf-syntax-prefix) x y))
  (equal (fix-prefix x)
	 (fix-prefix y)))

(defequiv prefix-equiv)

(defun prefix-len (prefix)
  (declare (type (satisfies wf-syntax-prefix) prefix))
  (if (consp prefix)
      (let ((entry (car prefix)))
	(case (car entry)
	      (:cons
	       (1+ (prefix-len (cdr prefix))))
	      (:append
	       (1+ (prefix-len (cdr prefix))))
	      (:quote
	       (len (list::fix (cdr entry))))
	      (t 0)))
    0))

(defthm prefix-len-prop
  (<= 0 (prefix-len prefix))
  :rule-classes (:linear))

(defthm zp-prefix-len-reduction
  (iff (equal (prefix-len prefix) 0)
       (if (consp prefix)
	   (let ((entry (car prefix)))
	     (case (car entry)
		   (:cons
		    nil)
		   (:append
		    nil)
		   (:quote
		    (equal (len (list::fix (cdr entry))) 0))
		   (t t)))
	 t)))

(defcong prefix-equiv equal
  (prefix-len prefix) 1
  :hints (("goal" :induct (list::len-len-induction prefix prefix-equiv))))

(defun firstn-prefix (n prefix)
  (declare (type (satisfies wf-syntax-prefix) prefix)
	   (type (integer 0 *) n))
  (if (consp prefix)
      (let ((entry (car prefix)))
	(case (car entry)
	      (:cons
	       (if (zp n) nil
		 (cons entry (firstn-prefix (1- n) (cdr prefix)))))
	      (:append
	       (if (zp n) nil
		 (cons entry (firstn-prefix (1- n) (cdr prefix)))))
	      (:quote
	       (let ((entry (cons :quote (acl2::firstn n (list::fix (cdr entry))))))
		 (cons entry nil)))
	      (t nil)))
    nil))

(defthm wf-sytnax-prefix-firstn-prefix
  (implies
   (wf-syntax-prefix prefix)
   (wf-syntax-prefix (firstn-prefix n prefix)))
  :rule-classes (:rewrite :type-prescription))

;(defcong list::equiv equal
;  (acl2::firstn n list) 2)

(defcong prefix-equiv equal
  (firstn-prefix n prefix) 2)

(defthm list-cong-first-n
  (implies
   (<= (len list) (nfix n))
   (list::equiv (acl2::firstn n list)
		    list)))

(defthm prefix-equiv-firstn-prefix
  (implies
   (and
    (wf-syntax-prefix prefix)
    (<= (prefix-len prefix) (nfix n)))
   (prefix-equiv (firstn-prefix n prefix)
		 prefix)))


(defun prune-prefix (n prefix list2)
  (declare (type integer n))
  (if (and (consp prefix)
	   (consp list2)
	   (equal (car prefix) (car list2)))
      (prune-prefix (1+ n) (cdr prefix) (cdr list2))
    n))

(defthm integerp-prune-prefix
  (implies
   (integerp n)
   (integerp (prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm prune-prefix-len
  (implies
   (integerp n)
   (and (<= (prune-prefix n prefix list2)
	    (+ n (len prefix)))
	(<= n (prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm consp-open-firstn
  (implies
   (consp list)
   (equal (acl2::firstn n list)
	  (if (zp n) nil
	    (cons (car list) (acl2::firstn (1- n) (cdr list)))))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (prune-prefix n prefix x) n)))
   (dominates (acl2::firstn m prefix) x)))

(defun syntax-quote-prune-prefix (n prefix list2)
  (declare (type (satisfies wf-syntax-prefix) prefix)
	   (type integer n))
  (if (consp prefix)
      (let ((entry (car prefix)))
	(case (car entry)
	      (:cons
	       (if (and (consp list2)
			(syn::quotep (cdr entry))
			(equal (syn::dequote (cdr entry)) (car list2)))
		   (syntax-quote-prune-prefix (1+ n) (cdr prefix) (cdr list2))
		 n))
	      (:quote
	       (prune-prefix n (cdr entry) list2))
	      (t n)))
    n))

(defthm integerp-syntax-quote-prune-prefix
  (implies
   (integerp n)
   (integerp (syntax-quote-prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm syntax-quote-prune-prefix-prefix-len
  (implies
   (integerp n)
   (and (<= (syntax-quote-prune-prefix n prefix list2)
	    (+ n (prefix-len prefix)))
	(<= n (syntax-quote-prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm syntax-quote-prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (syntax-quote-prune-prefix n prefix x) n)))
   (dominates (s2l (firstn-prefix m prefix) a) x)))

(defun syntax-alist-prune-prefix (n prefix list2)
  (declare (type t prefix list2)
	   (type integer n))
  (if (consp prefix)
      (cond
       ((syn::consp list2)
	(let ((v (syn::car list2)))
	  (cond
	   ((syn::quotep v)
	    (if (equal (car prefix) (syn::dequote v))
		(syntax-alist-prune-prefix (1+ n) (cdr prefix) (syn::cdr list2))
	      n))
	   ((syn::quotep list2)
	    (prune-prefix n prefix (syn::dequote list2)))
	   (t n))))
       (t n))
    n))

(defthm integerp-syntax-alist-prune-prefix
  (implies
   (integerp n)
   (integerp (syntax-alist-prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm syntax-alist-prune-prefix-len
  (implies
   (integerp n)
   (and (<= (syntax-alist-prune-prefix n prefix list2)
	    (+ n (len prefix)))
	(<= n (syntax-alist-prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm syntax-alist-prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (syntax-alist-prune-prefix n prefix x) n)))
   (dominates (acl2::firstn m prefix) (syn::eval x a))))


(defun syntax-prune-prefix (n prefix list2)
  (declare (type (satisfies wf-syntax-prefix) prefix)
	   (type integer n))
  (if (consp prefix)
      (let ((entry (car prefix)))
	(case (car entry)
	      (:cons
	       (cond
		((syn::consp list2)
		 (if (equal (cdr entry) (syn::car list2))
		     (syntax-prune-prefix (1+ n) (cdr prefix) (syn::cdr list2))
		   n))
		((syn::quotep list2)
		 (syntax-quote-prune-prefix n prefix (syn::dequote list2)))
		(t n)))
	      (:append
	       (if (and (syn::appendp list2)
			(equal (cdr entry) (syn::arg 1 list2)))
		   (syntax-prune-prefix (1+ n) (cdr prefix) (syn::arg 2 list2))
		 n))
	      (:quote
	       (syntax-alist-prune-prefix n (cdr entry) list2))
	      (t n)))
    n))

(defthm integerp-syntax-prune-prefix
  (implies
   (integerp n)
   (integerp (syntax-prune-prefix n prefix list2)))
  :rule-classes (:rewrite :type-prescription))

(defthm syntax-prune-prefix-prefix-len
  (implies
   (integerp n)
   (and (<= (syntax-prune-prefix n prefix list2)
	    (+ n (prefix-len prefix)))
	(<= n (syntax-prune-prefix n prefix list2))))
  :rule-classes (:linear))

(defthm syntax-prune-prefix-dominates
  (implies
   (and
    (integerp n)
    (equal m (- (syntax-prune-prefix n prefix x) n)))
   (dominates (s2l (firstn-prefix m prefix) a) (syn::eval x a)))
  :hints (("Goal" :in-theory (enable syn::open-nth))))

(defun syntax-term-to-prefix (term)
  (declare (type t term))
  (cond
   ((syn::consp term)
    (met ((hit n prefix) (syntax-term-to-prefix (syn::cdr term)))
	 (mv hit (1+ n) (cons (cons :cons (syn::car term)) prefix))))
   ((syn::appendp term)
    (met ((hit n prefix) (syntax-term-to-prefix (syn::arg 2 term)))
	 (mv hit (1+ n) (cons (cons :append (syn::arg 1 term)) prefix))))
   ((syn::quotep term)
    (let ((term (syn::dequote term)))
      (if (true-listp term)
	  (mv t (len term) (cons (cons :quote term) nil))
	(mv nil 0 nil))))
   (t (mv nil 0 nil))))

(defthm integerp-v1-syntax-term-to-prefix
  (integerp (v1 (syntax-term-to-prefix term))))

(defthm wf-syntax-prefix-v2-syntax-term-to-prefix
  (wf-syntax-prefix (v2 (syntax-term-to-prefix term))))

(defthm v0-implies-v1-is-prefix-len-v2
  (implies
   (v0 (syntax-term-to-prefix term))
   (equal (v1 (syntax-term-to-prefix term))
	  (prefix-len (v2 (syntax-term-to-prefix term))))))

(defthm v0-implies-invertability
  (implies
   (v0 (syntax-term-to-prefix term))
   (equal (s2l (v2 (syntax-term-to-prefix term)) a)
	  (syn::eval term a)))
  :hints (("Goal" :in-theory (enable syn::open-nth))))

(defthm prefix-len-firstn-prefix
  (implies
   (and
    (integerp m)
    (<= 0 m)
    (<= m (prefix-len prefix)))
   (equal (prefix-len (firstn-prefix m prefix))
	  m)))

(defun syntax-quote-reduce-prefix (n prefix list)
  (declare (xargs :guard (and (integerp n)
			      (wf-syntax-prefix prefix)
			      (equal n (prefix-len prefix)))))
  (if (consp list)
      (let ((m (syntax-quote-prune-prefix 0 prefix (car list))))
	(if (zp m) nil
	  (let ((prefix (if (< m n) (firstn-prefix m prefix) prefix))
		(n      (if (< m n) m n)))
	    (syntax-quote-reduce-prefix n prefix (cdr list)))))
    prefix))

(defthm firstn-dominates-prefix
  (dominates (acl2::firstn n list) list)
  :hints(("Goal" :in-theory (enable acl2::firstn))))

(defthm s2l-firstn-prefix-dominates-prefix
  (dominates (s2l (firstn-prefix n prefix) a) (s2l prefix a)))

(defthm dominates-self-syntax-quote-reduce-prefix
  (dominates (s2l (syntax-quote-reduce-prefix n prefix list) a)
	     (s2l prefix a)))

(defthm prefix-dominates-backchain
  (implies
   (and
    (integerp n)
    (dominates (s2l prefix a) x))
   (dominates (s2l (syntax-quote-reduce-prefix n prefix list) a) x)))

(defun dominates-all (x list)
  (declare (type t x list))
  (if (consp list)
      (and (dominates x (car list))
	   (dominates-all x (cdr list)))
    t))

(defthm prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (prune-prefix n prefix x)
	  (if (< 0 n)
	      (+ 1 (prune-prefix (1- n) prefix x))
	    (- 1 (prune-prefix (1+ n) prefix x))))))

(defthm prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (prune-prefix n prefix x)
	  (+ n (prune-prefix 0 prefix x)))))

(defthm syntax-quote-prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (syntax-quote-prune-prefix n prefix x)
	  (if (< 0 n)
	      (+ 1 (syntax-quote-prune-prefix (1- n) prefix x))
	    (- 1 (syntax-quote-prune-prefix (1+ n) prefix x))))))

(defthm syntax-quote-prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (syntax-quote-prune-prefix n prefix x)
	  (+ n (syntax-quote-prune-prefix 0 prefix x)))))

(defthm syntax-alist-prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (syntax-alist-prune-prefix n prefix x)
	  (if (< 0 n)
	      (+ 1 (syntax-alist-prune-prefix (1- n) prefix x))
	    (- 1 (syntax-alist-prune-prefix (1+ n) prefix x))))))

(defthm syntax-alist-prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (syntax-alist-prune-prefix n prefix x)
	  (+ n (syntax-alist-prune-prefix 0 prefix x)))))

(defthm syntax-prune-prefix-step-reduction
  (implies
   (and
    (integerp n)
    (not (zp n)))
   (equal (syntax-prune-prefix n prefix x)
	  (if (< 0 n)
	      (+ 1 (syntax-prune-prefix (1- n) prefix x))
	    (- 1 (syntax-prune-prefix (1+ n) prefix x))))))

(defthm syntax-prune-prefix-n-reduction
  (implies
   (and
    (syntaxp (not (quotep n)))
    (integerp n))
   (equal (syntax-prune-prefix n prefix x)
	  (+ n (syntax-prune-prefix 0 prefix x)))))

(defthm equal-prune-len-implies-domination
  (implies
   (and
    (equal (prune-prefix n prefix x) m)
    (equal m (+ n (len prefix))))
   (dominates prefix x)))

(defthm equal-syntax-quote-prune-len-implies-domination
  (implies
   (and
    (equal (syntax-quote-prune-prefix n prefix x) m)
    (equal m (+ n (prefix-len prefix))))
   (dominates (s2l prefix a) x)))

(defthm equal-syntax-alist-prune-len-implies-domination
  (implies
   (and
    (equal (syntax-alist-prune-prefix n prefix x) m)
    (equal m (+ n (len prefix))))
   (dominates prefix (syn::eval x a))))

(defthm equal-syntax-prune-len-implies-domination
  (implies
   (and
    (equal (syntax-prune-prefix n prefix x) m)
    (equal m (+ n (prefix-len prefix))))
   (dominates (s2l prefix a) (syn::eval x a)))
  :hints (("goal" :in-theory (enable syn::open-nth))))

(defthm nil-dominates-all
  (dominates-all nil list))

(defthm dominates-all-syntax-quote-reduce-prefix
  (implies
   (equal n (prefix-len prefix))
   (dominates-all (s2l (syntax-quote-reduce-prefix n prefix list) a) list))
  :hints (("goal" :induct (syntax-quote-reduce-prefix n prefix list))))

(defun syntax-reduce-prefix (n prefix list)
  (declare (xargs :guard (and (integerp n)
			      (wf-syntax-prefix prefix)
			      (equal n (prefix-len prefix)))))
  (cond
   ((syn::consp list)
    (let ((m (syntax-prune-prefix 0 prefix (syn::car list))))
      (if (zp m) nil
	(let ((prefix (if (< m n) (firstn-prefix m prefix) prefix))
	      (n      (if (< m n) m n)))
	  (syntax-reduce-prefix n prefix (syn::cdr list))))))
   ((syn::quotep list)
    (syntax-quote-reduce-prefix n prefix (syn::dequote list)))
   (t nil)))

(defthm dominates-self-syntax-reduce-prefix
  (dominates (s2l (syntax-reduce-prefix n prefix list) a)
	     (s2l prefix a)))

(defthm syntax-reduce-prefix-dominates-backchain
  (implies
   (and
    (integerp n)
    (dominates (s2l prefix a) x))
   (dominates (s2l (syntax-reduce-prefix n prefix list) a) x)))

(defthm dominates-all-syntax-reduce-prefix
  (implies
   (equal n (prefix-len prefix))
   (dominates-all (s2l (syntax-reduce-prefix n prefix list) a) (syn::eval list a)))
  :hints (("goal" :induct (syntax-reduce-prefix n prefix list))))


(defun syntax-prefix (list)
  (declare (type t list))
  (if (syn::consp list)
      (let ((term (syn::car list)))
	(met ((hit n prefix) (syntax-term-to-prefix term))
	     (and hit (syntax-reduce-prefix n prefix (syn::cdr list)))))
    nil))

(defthm dominates-all-syntax-prefix
  (dominates-all (s2l (syntax-prefix list) a) (syn::eval list a)))

;; ===================
;;
;; Meta key extraction
;;
;; ===================


(defun keyx (list)
  (declare (type t list))
  (if (consp list)
      (if (consp (car list))
	  (cons (caar list)
		(keyx (cdr list)))
	(cons nil (keyx (cdr list))))
    nil))

(defthm keyx-reduction
  (equal (keyx list)
	 (keys list)))

;; jcd - had to change a few "keys" to "strip-cars" here since keys is just a
;; macro alias now and isn't a real function.

(defund syntax-keys (hit list)
  (declare (type t list))
  (cond
   ((syn::consp list)
    (let ((x (syn::car list)))
      (let ((v (if (syn::consp x) (syn::car x) `(car ,x))))
	(syn::cons v (syntax-keys t (syn::cdr list))))))
   ((syn::quotep list)
    (let ((list (syn::dequote list)))
      (syn::enquote (keyx list))))
   ((syn::appendp list)
    (syn::append (syntax-keys t (syn::arg 1 list))
		 (syntax-keys t (syn::arg 2 list))))
   (t
    (and hit `(strip-cars ,list)))))

(defthm syntax-keys-true
  (implies
   hit
   (syntax-keys hit list))
  :hints (("goal" :in-theory (enable
			      syntax-keys
			      ))))

(syn::extend-eval
 key-eval
 (
  (strip-cars list)
  (car x)
  ))

(defthm key-eval-syntax-keys
  (implies
   (syntax-keys hit term)
   (equal (key-eval (syntax-keys hit term) a)
	  (keys (key-eval term a))))
  :hints (("goal" :in-theory (e/d (syn::open-nth
				   keys syntax-keys)
				  (keys-of-cdr)))))

(defun syntax-keys-wrapper (term)
  (declare (type t term))
  (if (syn::funcall 'strip-cars 1 term)
      (let ((list (syn::arg 1 term)))
	(let ((list (syntax-keys nil list)))
	  (or list
	      term)))
    term))

(defthm *meta*-key-eval-keys
  (equal (key-eval term a)
	 (key-eval (syntax-keys-wrapper term) a))
  :hints (("goal" :in-theory (enable syn::open-nth)))
  :rule-classes ((:meta :trigger-fns (strip-cars))))
;  :rule-classes ((:meta :trigger-fns (keys))))



;; jcd - this is redundant, removing
;; (in-theory
;;  (disable
;;   keys
;;   ))

;; #|

;; '(
;;   (C d)
;;   (c x)
;;   (p q)
;;   )

;; `(
;;   (a b c d)
;;   (a b c x)
;;   (a b p q)
;;   )

;; (defun common-prefixes (prefixes a list2)
;;   (if (consp list2)
;;       (let ((prefixes (common-prefix prefixes (car list2) a)))
;; 	(common-prefixes prefixes a (cdr list2)))
;;     prefixes))

;; (defun common-prefixes-list (prefixes list1 list2)
;;   (if (consp list1)
;;       (let ((prefixes (common-prefixes (car list1) list2)))
;; 	(common-prefixes-list prefixes (cdr list1) list2))
;;     prefixes))


;; (defignore syntax-remove-1-prefixed-tail-dominator bag::a (list pre n x)
;;   (declare (type (satisfies alistp) pre)
;; 	   (type (integer 0 *) n))
;;   (cond
;;    ((syn::consp list)
;;     (let ((z (syn::car list)))
;;       (let ((m (sudo-len z)))
;; 	(if (and (< n m) (syntax-prefixed-tail-dominator-p z pre x))
;; 	    (mv t (syn::cdr list))
;; 	  (met ((hit rest) (syntax-remove-1-prefixed-tail-dominator (syn::cdr list) pre n x))
;; 	       (if hit (mv hit (syn::cons (syn::car list) rest))
;; 		 (mv nil nil)))))))
;;    ((syn::appendp list)
;;     (let ((arg1 (syn::arg 1 list)))
;;       (met ((hit rest) (syntax-remove-1-prefixed-tail-dominator arg1 pre n x))
;; 	   (if hit (mv hit (syn::append rest (syn::arg 2 list)))
;; 	     (let ((arg2 (syn::arg 2 list)))
;; 	       (met ((hit rest) (syntax-remove-1-prefixed-tail-dominator arg2 pre n x))
;; 		    (if hit (mv hit (syn::append arg1 rest))
;; 		      (mv nil nil))))))))
;;    ((syn::quotep list)
;;     (if (and (syn::quotep x)
;; 	     (consp pre)
;; 	     (equal (caar pre) :quote)
;; 	     (true-listp (cdar pre)))
;; 	(let ((prefix (cdar pre)))
;; 	  (met ((hit rest) (remove-1-prefixed-tail-dominator (syn::dequote list) prefix (syn::dequote x)))
;; 	       (mv hit (syn::enquote rest))))
;;       (mv nil nil)))
;;    (t (mv nil nil))))

;; (defignored (prefix n list1 list2)


;; (defignored syntax-remove-list-prefixed-tail-dominator bag::a (prefix n list1 list2)
;;   (declare (type t list1 list2))
;;   (cond
;;    ((syn::consp list1)
;;     (met ((hit1 rest) (syntax-remove-1-prefixed-tail-dominator list2 prex n (syn::car list1)))
;; 	 (met ((hit2 rest) (syntax-remove-list-prefixed-tail-dominator prefix n (syn::cdr list1) rest))
;; 	      (mv (or hit1 hit2) rest))))
;;    ((syn::appendp list1)
;;     (met ((hit1 rest) (syntax-remove-list-prefixed-tail-dominator prefix n (syn::arg 1 list1) list2))
;; 	 (met ((hit2 rest) (syntax-remove-list-prefixed-tail-dominator prefix n (syn::arg 2 list1) rest))
;; 	      (mv (or hit1 hit2) rest))))
;;    ((syn::null list1)
;;     (mv nil list1))
;;    ((syn::quotep list1)
;;     (syntax-remove-quote-list-prefixed-tail-dominator prefix n list1 list2))
;;    (t
;;     (mv nil nil))))


;; (defirrelevant syntax-common-prefix-p 1 bag::a (prefix n list1 list2)
;;   :hints (("goal" :in-theory (enable
;; 			      syntax-common-prefix-p
;; 			      syntax-contains-prefixed-tail-dominator-irrelevant
;; 			      ))))

;; (defignored syntax-found-common-prefix-p bag::a (v rest list1 list2)
;;   (declare (type t v rest list1 list2))
;;   (if (syn::consp rest)
;;       (met ((hit prefix) (syntax-tail-dominates (syn::car rest) v))
;; 	   (or (and hit (syntax-common-prefix-p prefix (len prefix) list1 list2))
;; 	       (syntax-found-common-prefix-p v (syn::cdr rest) list1 list2)))
;;     nil))

;; (defirrelevant syntax-found-common-prefix-p 1 bag::a (v rest list1 list2)
;;   :hints (("goal" :in-theory (enable
;; 			      syntax-found-common-prefix-p
;; 			      syntax-common-prefix-p-irrelevant
;; 			      ))))

;; (defignored



;; |#

(in-theory (disable sp-to-clrp))

(defthm clrp-sp-domination
  (implies
   (dominates a r)
   (equal (clrp r (sp a v st))
	  (sp a (clrp (nthcdr (len a) r) v) st)))
  :hints (("goal" :in-theory (enable dominates
				     clrp
				     sp
				     gp
				     nthcdr))))

(defun dominated (a list)
  (declare (type t list))
  (if (consp list)
      (if (dominates a (car list))
	  (cons (car list) (dominated a (cdr list)))
	(dominated a (cdr list)))
    nil))

(defthm dominated-when-no-domination
  (implies
   (not (dominates-some a list))
   (equal (dominated a list) nil)))

(defthm nthcdr-not-consp
  (implies
   (not (consp list))
   (equal (nthcdr n list) (if (zp n) list nil))))

(defun nthcdrx (n list)
  (declare (type (integer 0 *) n))
  (if (zp n) list
    (if (consp list)
	(nthcdrx (1- n) (cdr list))
      nil)))

(defthm nthcdrx-to-nthcdr
  (equal (nthcdrx n list)
	 (nthcdr n list))
  :hints (("goal" :in-theory (enable nthcdr))))

(defun map-nthcdr (n list)
  (declare (type (integer 0 *) n))
  (if (consp list)
      (cons (nthcdrx n (car list))
	    (map-nthcdr n (cdr list)))
    nil))

(defthm sp-of-clrp
  (implies
   (dominates a x)
   (equal (sp a v (clrp x r))
	  (sp a v r)))
  :hints (("goal" :in-theory (enable dominates sp clrp))))

(defthm clrp-of-sp-identity
  (equal (clrp a (sp a v r))
	 (clrp a r))
  :hints (("goal"  :induct (sp a v r)
	   :in-theory (enable sp clrp))))

(defthmd clrp-commute-2
  (equal (clrp a (clrp b r))
	 (clrp b (clrp a r)))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))

(theory-invariant
 (incompatible
  (:rewrite clrp-commute-2)
  (:rewrite clrp-of-clrp)))

(defthm clrp-clrp-list-sp-reduction
  (equal (clrp a (clrp-list list (sp a v r)))
	 (clrp a (clrp-list list r)))
  :hints (("goal" :in-theory (e/d
			      (
			       clrp-list
			       clrp-commute-2
			       )
			      (
			       clrp-of-clrp
			       meta-rule-to-show-prefix-domination
			       )))))

(defthm nthcdr-of-dominator
  (implies
   (dominates x a)
   (list::equiv (nthcdr (len a) x)
		    nil))
  :hints (("goal" :in-theory (enable dominates nthcdr))))

(defcong list::equiv equal
  (clrp x r) 1
  :hints (("goal" :in-theory (enable clrp))))


(defthm diverges-from-all-from-non-domination
  (implies
   (and
    (not (dominates-some a list))
    (not (dominated-by-some a list)))
   (diverges-from-all a list))
  :hints (("goal" :in-theory (enable diverges-from-all
				     dominates-some
				     dominated-by-some)))
  :rule-classes (:forward-chaining))

(defthm clrp-list-sp-domination
  (implies
   (not (dominated-by-some a list))
   (equal (clrp-list list (sp a v st))
	  (sp a (clrp-list (map-nthcdr (len a) (dominated a list)) v)
	      (clrp-list list st))))
  :hints (("goal" :induct (clrp-list list st)
	   :in-theory (e/d
		       (
			clrp-commute-2
			diverge
			;jcd - removing graph.lisp - equal-sp-reduction
			dominates-some
			dominated-by-some
			clrp-list
			CLRP-LIST-OF-SP-WHEN-DIVERGES-FROM-ALL)
		       (
			clrp-of-clrp
;jcd			NTHCDR-WHEN-DOMINATES
			)))))

(defthm gp-clrp
  (implies
   (dominates a x)
   (equal (gp a (clrp x st))
	  (clrp (nthcdr (len a) x) (gp a st))))
  :hints (("goal" :in-theory (enable
			      diverge
			      clrp
			      GP-OF-SP
			      ))))

(defthm gp-clrp-list
  (implies
   (not (dominated-by-some a list))
   (equal (gp a (clrp-list list st))
	  (clrp-list (map-nthcdr (len a) (dominated a list)) (gp a st))))
  :hints (("goal" :induct (clrp-list list st)
	   :in-theory (e/d
		       (
			;; jcd - not necessary clrp-commute-2
			;; jcd - not necessary diverge
			;; jcd - removing graph.lisp - equal-sp-reduction
			;; jcd - not necessary dominates-some
			;; jcd - not necessary dominated-by-some
			clrp-list
                        ;; jcd not necessary CLRP-LIST-OF-SP-WHEN-DIVERGES-FROM-ALL
                        )
		       (
			;; jcd - not necessary clrp-of-clrp
			;; jcd - not necessary NTHCDR-WHEN-DOMINATES
			)))))

#|


(defthm syntax-quote-dominates-implies-dominates-pd-eval
  (implies
   (syntax-quote-dominates-p x y)
   (dominates x (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance syntax-quote-dominates-implies-dominates
					     (syn::eval pd-eval)
					     (syn::eval-list pd-eval-list)))))

(defthm syntax-domination-implies-domination-helper-pd-eval
  (implies
   (hyp-for-show-syntax-dominates-p flg x y type-alist)
   (dominates (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :use (:functional-instance syntax-domination-implies-domination-helper
					     (syn::eval pd-eval)
					     (syn::eval-list pd-eval-list)))))

(defignore syntax-dominated-by-some-quote bag::a (x qlist)
  (if (consp qlist)
      (or (syntax-quote-dominates-p (car qlist) x)
	  (syntax-dominated-by-some-quote x (cdr qlist)))
    nil))

(defthm syntax-domianted-by-some-quote-implies-domianted-by-some
  (implies
   (syntax-dominated-by-some-quote x qlist)
   (dominated-by-some (pd-eval x bag::a) qlist))
  :hints (("goal" :in-theory (enable dominated-by-some)))
  :rule-classes (:forward-chaining :rewrite))


(defignore syntax-dominated-by-some bag::a (x list alist)
  (cond
   ((syn::consp list)
    (or (show-syntax-dominates-p t (syn::car list) x alist)
	(syntax-dominated-by-some x (syn::cdr list) alist)))
   ((syn::appendp list)
    (or (syntax-dominated-by-some x (syn::arg 1 list) alist)
	(syntax-dominated-by-some x (syn::arg 2 list) alist)))
   ((syn::quotep list)
    (if (syn::quotep x)
	(dominated-by-some (syn::dequote x) (syn::dequote list))
      (syntax-dominated-by-some-quote x (syn::dequote list))))
   (t
    nil)))

(defthm syntax-domianted-by-some-better-implies-domianted-by-some
  (implies
   (syntax-dominated-by-some x list alist)
   (dominated-by-some (pd-eval x bag::a) (pd-eval list bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth dominated-by-some)))
  :rule-classes (:forward-chaining :rewrite))

(defignore syntax-dominates-some bag::a (x list alist)
  (cond
   ((syn::consp list)
    (or (show-syntax-dominates-p t x (syn::car list) alist)
	(syntax-dominates-some x (syn::cdr list) alist)))
   ((syn::appendp list)
    (or (syntax-dominates-some x (syn::arg 1 list) alist)
	(syntax-dominates-some x (syn::arg 2 list) alist)))
   ((syn::quotep list)
    (and (syn::quotep x)
	 (dominates-some (syn::dequote x) (syn::dequote list))))
   (t
    nil)))

(defthm syntax-domiantes-some-implies-domiantes-some
  (implies
   (syntax-dominates-some x list alist)
   (dominates-some (pd-eval x bag::a) (pd-eval list bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth dominates-some)))
  :rule-classes (:forward-chaining :rewrite))

(defignore syntax-dominates-some-quote bag::a (a list)
  (cond
   ((syn::consp list)
    (let ((v (syn::car list)))
      (or (syntax-quote-dominates-p a v)
	  (syntax-dominates-some-quote a (syn::cdr list)))))
   ((syn::appendp list)
    (or (syntax-dominates-some-quote a (syn::arg 1 list))
	(syntax-dominates-some-quote a (syn::arg 2 list))))
   ((syn::quotep list)
    (dominates-some a (syn::dequote list)))
   (t
    nil)))

(defthm syntax-domiantes-some-quote-implies-domiantes-some
  (implies
   (syntax-dominates-some-quote x list)
   (dominates-some x (pd-eval list bag::a)))
  :hints (("goal" :in-theory (enable syn::open-nth dominates-some)))
  :rule-classes (:forward-chaining :rewrite))

;; Eventually we may want to look for things like
;; (map-cons x list)
;; (map-append x y)
;;
(defignore syntax-all-dominate-some bag::a (x y)
  (cond
   ((syn::appendp y)
    (or (syntax-all-dominate-some x (syn::arg 1 y))
	(syntax-all-dominate-some x (syn::arg 2 y))))
   ((syn::quotep y)
    (and (syn::quotep x)
	 (all-dominate-some (syn::dequote x) (syn::dequote y))))
   (t
    (equal x y))))

(defun all-dominate-some (x y)
  (if (consp x)
      (and (dominates-some (car x) y)
	   (all-dominate-some (cdr x) y))
    t))

(include-book "equiv")

(defthm all-dominate-some-subset
  (implies
   (path-subset x y)
   (all-dominate-some x y)))

(defthm all-dominate-some-id
  (all-dominate-some x x))

(defthm all-dominate-some-append-2
  (implies
   (all-dominate-some x y)
   (all-dominate-some x (append y z))))

(defthm all-dominate-some-append-3
  (implies
   (all-dominate-some x z)
   (all-dominate-some x (append y z))))

DAG

(defignore split-list-by-dominators-quote bag::a (list x rx ry)
  (if (consp list)
      (if (syntax-dominates-some-quote (car list) x)
	  (split-list-by-dominators-quote (cdr list) x (cons (car list) rx) ry)
	(split-list-by-dominators-quote (cdr list) x  rx (cons (car list) ry)))
    (mv rx ry)))

(defthm memberp-v0-split-list-by-dominators
  (equal (memberp a (v0 (split-list-by-dominators-quote list x rx ry)))
	 (or (memberp a rx)
	     (and (memberp a list)
		  (syntax-dominates-some-quote a x)))))

(defthm promote-rx
  (implies
   (consp rx)
   (bag::perm (v0 (split-list-by-dominators-quote list x rx ry))
	      (cons (car rx) (v0 (split-list-by-dominators-quote list x (cdr rx) ry)))))
  :hints (("goal" :in-theory (e/d (BAG::PERM-BY-DOUBLE-CONTAINMENT)
				  (BAG::PERM-OF-CONS-MEMBERP-CASE
				   BAG::PERM-OF-cons)))))

(defthm all-diverge-from-all-split-list-by-dominatros-quote
  (implies
   (and
    (all-diverge list)
    (all-diverge-from-all rx ry))
   (all-diverge-from-all (v0 (split-list-by-dominators-quote list x rx ry))
			 (v1 (split-list-by-dominators-quote list x rx ry))))
  :hints (("goal" :in-theory (enable all-diverge))))

(defun split-list-by-dominators (list x rx ry alist)
  (cond
   ((syn::consp list)
    (if (syntax-dominates-some (syn::car list) x alist)
	(split-list-by-dominators (syn::cdr list) x (syn::cons (syn::car list) rx) ry alist)
      (split-list-by-dominators (syn::cdr list) x rx (syn::cons (syn::car list) ry) alist)))
   ((syn::appendp list)
    (met ((rx ry) (split-list-by-dominators (syn::arg 1 list) x rx ry alist))
      (split-list-by-dominators (syn::arg 2 list) x rx ry alist)))
   ((syn::quotep list)
    (met ((vx vy) (split-list-by-dominators-quote (syn::dequote list) x nil nil))
      (mv (syn::append rx vx) (syn::append ry vy))))
   (t
    (if (syntax-all-dominate-some list x)
	(mv (syn::append list rx) ry)
      (mv rx (syn::append list ry))))))

(defignore syntax-unique-dominators (x y list)
  (met ((rx ry) (split-list-by-dominators list x (syn::nil) (syn::nil) alist))
    (and (syntax-all-dominated-by-some x rx)
	 (syntax-all-dominated-by-some y ry))))

(defthm syntax-all-dominate-some-implies-all-dominate-some
  (implies
   (syntax-all-dominate-some x y)
   (all-dominate-some (pd-eval x bag::a) (pd-eval y bag::a)))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("goal" :in-theory (enable syn::open-nth))))





(defun all-diverge-from-all-decompose-2 (x y alist)
  (cond
   ((syn::consp x)
    (and (show-diverges-from-all (syn::car x) y alist)
	 (all-diverge-from-all-decompose-2 (syn::cdr x) y alist)))
   ((syn::appendp x)
    (and (all-diverge-from-all-decompose-1 (syn::arg 1 x) y alist)
	 (all-diverge-from-all-decompose-1 (syn::arg 2 x) y alist)))
   ((syn::quotep x)
    (all-diverge-from-all-decompose-1-quote (syn::dequote x) y alist))
   (t
    (show-all-diverge-from-all-decompose-2 x y alist))))

(defun all-diverge-from-all-decompose-1 (x y alist)
  (cond
   ((syn::consp x)
    (and (show-diverges-from-all-decompose-2 (syn::car x) y alist)
	 (all-diverge-from-all-decompose-1 (syn::cdr x) y alist)))
   ((syn::appendp x)
    (and (all-diverge-from-all-decompose-1 (syn::arg 1 x) y alist)
	 (all-diverge-from-all-decompose-1 (syn::arg 2 x) y alist)))
   ((syn::quotep x)
    (all-diverge-from-all-decompose-1-quote (syn::dequote x) y alist))
   (t
    (show-all-diverge-from-all-decompose-2 x y alist))))


(defun all-diverge-from-all-decompose (x y alist)
  )

;; It might be best to break up the input (as well as intermediate
;; results) into atomic segments and then reason about those
;; segments one at a time.  This would unify many of the routines
;; and make them more general.

(defun list::constituant (list c a q)
  (cond
   ((syn::consp list)
    (let ((x (syn::car list)))
      (if (syn::quotep x)
	  (constituant (syn::cdr list) c a (cons (syn::dequote x) q))
	(constituant (syn::cdr list) (cons x c) a q))))
   ((syn::append list)
    (met ((c a q) (constituant (syn::arg 1 list) c a q))
      (constituant (syn::arg 2 list) c a q)))
   ((syn::quotep list)
    (mv c a (append (syn::dequote list) q)))
   (t
    (mv c (cons list a) q))))

(defun list::reconstitute-c (c)
  (if (consp c)
      (syn::cons (car c)
		 (list::reconstitute-c (cdr c)))
    (syn::nil)))

(defun list::reconstitute-a (a)
  (if (consp a)
      (syn::append (car a)
		   (list::reconstitute-a (cdr a)))
    (syn::nil)))

(defun list::reconstitute-q (q)
  (syn::quote q))

(defun list::reconstitute (c a q)
  (syn::append (list::reconstitute-a a)
	       (syn::append (list::reconstitute-c c)
			    (list::reconstitute-q q))))

(defthm reconstitution
  (met ((c a q) (list::constituant list))
    (bag::perm (pd-eval (list::reconstitute c a q) bag::a)
	       (pd-eval list bag::a))))

(defthm
  (implies
   (member fn *supported-functions*)
   (equal (pd-eval (simplify goals) bag::a)
	  (pd-eval (reconstruct goals) bag::a))))

(deconstruct term) => goals
(reconstruct goals) => term

(reconstruct (deconstruct term)) = term

(pd-eval (simplify goals) bag::a)
(pd-eval (reconstruct goals) bag::a)

(defun simplify (stack)
  (if (consp stack)
      (let ((op (car stack)))
	(let ((stack (reduce op stack)))
	  (simplify stack)))
    ..))


(:member (:atom term) (:quotep list))

(defun elaborate (fn x alist)
  )

(defun show (fn x y n alist whole)
  )

(defun simplify-term-list (fn term-list x)
  )

(defun simplify-quote-list (fn quote-list x)
  )

(defun simplify (fn x y n alist whole)
  (if (or (zp n) (endp type-alist))
      nil
    (let* ((entry (car type-alist))
	   (fact  (car entry)))
      (case fn
	(:all-diverge-from-all
	 (cond
	  ((syn::funcall 'all-diverge-from-all 2 fact)
	   (met ((sx a sy b) (match-subbags x y (syn::arg 1 fact) (syn::arg 2 fact) whole))
	     (or (and sx sy)
		 (and sx (met ((c2 a2 q2) (deconstruct a))
			   (and (simplify-list :diverges-from-all c2 y)
				(simplify-list :all-diverge-from-all a2 y)
				(simplify-quote-list :all-diverge-from-all q2 y))))
		 (and sy (met ((c2 a2 q2) (deconstruct b))
			   (and (simplify-list :diverges-from-all c2 x)
				(simplify-list :all-diverge-from-all a2 x)
				(simplify-quote-list :all-diverge-from-all q2 x))))
		 (simplify fn x y n (cdr alist) whole))))
	  (and (syn::funcall 'all-diverge 1 fact)
	       (bag::ts-non-nil (cadr entry))
	       (bag::show-unique-subbagps-from-type-alist x list
							  (syn::arg 1 fact)
							  (bag::usb16-fix (len whole-alist)) whole-alist whole-alist 1))))
	(:diverge
	 (cond
	  ((syn::funcall 'diverge)
	   (or (and (equal x (syn::arg 1 fact))
		    (equal y (syn::arg 2 fact)))
	       (and (equal x (syn::arg 2 fact))
		    (equal y (syn::arg 1 fact)))
	       (simplify fn x y n (cdr alist) whole)))
	  ((syn::funcall 'diverges-from-all)
	   (or (and (equal x (syn::arg 1 fact))
		    (show-membership y (syn::arg 2 fact)))
	       (and (equal y (syn::arg 2 fact))
		    (show-membership x (syn::arg 2 fact)))))
	  ((syn::funcall 'all-diverge-from-all)
	   (or (and (show-membership x (syn::arg 1 fact))
		    (show-membership y (syn::arg 2 fact)))
	       (and (show-membership x (syn::arg 2 fact))
		    (show-membership y (syn::arg 1 fact)))))
	  ((syn::funcall 'all-diverge)
	   (bag::show-unique-membership-from-type-alist x list
							(syn::arg 1 fact)
							(bag::usb16-fix (len whole-alist))))))
	(:diverges-from-all
	 )

	     (or (and sx sy)
		 (and sx (met ((c2 a2 q2) (deconstruct a))
			   (and (simplify-list :diverges-from-all c2 y)
				(simplify-list :all-diverge-from-all a2 y)
				(simplify-quote-list :all-diverge-from-all q2 y))))
		 (and sy (met ((c2 a2 q2) (deconstruct b))
			   (and (simplify-list :diverges-from-all c2 x)
				(simplify-list :all-diverge-from-all a2 x)
				(simplify-quote-list :all-diverge-from-all q2 x))))
		 (simplify fn x y n (cdr alist) whole))))
	  (and (syn::funcall 'all-diverge 1 fact)
	       (bag::ts-non-nil (cadr entry))
	       (bag::show-unique-subbagps-from-type-alist x list
							  (syn::arg 1 fact)
							  (bag::usb16-fix (len whole-alist)) whole-alist whole-alist 1)))
	  (t
	   (simplify fn x y n (cdr alist) whole))))

	  (:


    (:all-diverge
     (case fn
       (:diverge
	(unique-members
     )

  (case fn
    (:neq
     )
    (:diverge
     )
    (:perm
     )
    (:member
     )
    (:not-member
     )
    (:subbagp
     )
    (:allmembers
     )
    ))

(defthm diverge-from-syntax-dominating-divergence
  (implies
   (and
    (diverge a b)
    (syntax-quote-dominates-p a v)
    (syntax-quote-dominates-p b w))
   (diverge (pd-eval v bag::a) (pd-eval w bag::a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm diverge-from-syntax-dominated-by-some-diverges-from-all
  (implies
   (and
    (diverges-from-all a qlist)
    (syntax-quote-dominates-p a v)
    (syntax-dominated-by-some-quote w qlist))
   (diverge (pd-eval v bag::a) (pd-eval w bag::a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("goal" :in-theory (enable diverges-from-all)
	   :induct (syntax-dominated-by-some-quote w qlist))))

(defun syntax-not-dominates (x y)
  (cond
   ((syn::consp x)
    (or (not (syn::consp y))
	(let ((v (syn::car x))
	      (w (syn::car y)))
	  (or (not (syn::quotep v))
	      (not (syn::quotep w))
	      (not (equal (syn::dequote v) (syn::dequote w)))
	      (syntax-not-dominates (syn::cdr x) (syn::cdr y))))))
   ((syn::quotep x)
    (not (dominates (syn::dequote x) (syn::dequote y))))
   (t ;; For our purposes, this is a no-op
    t)))

(defthm not-dominates-when-syntax-not-equal
  (implies
   (and
    (consp a)
    (SYNTAX-QUOTE-DOMINATES-P A Y)
    (syntax-not-dominates y x))
   (not (SYNTAX-QUOTE-DOMINATES-P A X))))


(defun syntax-unique-portions (list x xr yr)
  (cond
   ((syn::consp list)
    (if (syntax-dominates-some (syn::car list) x)
	(syntax-unique-portions (syn::cdr list) x (cons xr) y yr)




;;
;; Cannot seem to independently say what we want
;;

(defthm diverge-from-syntax-dominated-by-some-all-diverge
  (implies
   (and
    (all-diverge qlist)
    (not (equal x y))
    (syntax-dominated-by-some-quote x qlist)
    (syntax-dominated-by-some-quote y qlist))
   (diverge (pd-eval x bag::a) (pd-eval y bag::a)))
  :hints (("goal" :in-theory (e/d (all-diverge)
				  (open-dominates)))))



|#
