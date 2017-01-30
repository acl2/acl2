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

;; equiv.lisp
;; Primitive alist fixing and equivalence relations.

(in-package "ALIST")
(include-book "../util/iff")
(include-book "../lists/basic")
(include-book "../lists/memberp")
(include-book "../lists/set")
(include-book "../util/good-rewrite-order")
(include-book "equiv")
(local (include-book "../util/iff"))

;; Interpreting Objects as Conses (consfix)
;;
;; We can think of a mapping between all ACL2 objects and conses, so that any
;; atom is mapped to (nil . nil) and any cons is mapped to itself.  The
;; function consfix applies this mapping for us, i.e., it interprets any ACL2
;; object as a cons.  Because this is how car and cdr interpret their
;; arguments, there are some very nice properties that we can prove about this
;; operation.

(defund consfix (x)
  (declare (type t x))
  (if (consp x)
      x
    (cons nil nil)))

(local
 (encapsulate
  ()
  ;; Here we check to make sure that our type prescription rule is as strong as
  ;; we think it is.  Don't remove this event even though it has no effect on
  ;; the logical world.
  (local (defthm test-type-prescription-of-consfix
           (consp (consfix x))
           :hints(("Goal"
                   :in-theory (union-theories '((:type-prescription consfix))
                                              (theory 'minimal-theory))))))))

(defthm consfix-when-non-consp
  (implies (not (consp x))
           (equal (consfix x)
                  (cons nil nil)))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-when-consp
  (implies (consp x)
           (equal (consfix x)
                  x))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-does-nothing
  (equal (equal x (consfix x))
         (consp x))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-of-cons
  (equal (consfix (cons a b))
         (cons a b)))



;; Note (jcd): Do not add the following rules.  They are trivial consequences
;; of the congruence rules under cons-equiv below, so adding them is not
;; necessary.
;;
;; (defthm consfix-of-car
;;   (equal (car (consfix a))
;;          (car a)))
;;
;; (defthm consfix-of-cdr
;;   (equal (cdr (consfix a))
;;          (cdr a)))





;; The Cons Equivalence Relation (cons-equiv)
;;
;; Given that (with consfix) we can now think of any object as a cons, the next
;; natural step is to define an equivalence relation wherein objects are
;; considered to be equivalent when their interpretations as conses are the
;; same.

(defun keys (alist)
  (declare (type t alist))
  (if (consp alist)
      (if (consp (car alist))
	  (cons (caar alist)
		(keys (cdr alist)))
	(cons nil (keys (cdr alist))))
    nil))

#|
(defthm memberp-cons-keys
  (implies
   (consp alist)
   (memberp (caar alist) (keys alist))))

(defthm clrv-len-reduction
  (implies
   (memberp a (keys alist))
   (< (len (clrv a alist)) (len alist)))
  :rule-classes (:linear))

(defun element (a y)
  (if (consp y)
      (if (equal (car a) (caar y))
	  (equal (cdr a) (cdar y))
	(element a (cdr y)))
    nil))

(defthm element-definition
  (equal (element a y)
	 (and (memberp (car a) (keys y))
	      (equal (cdr a) (cdr (getv (car a) y)))))
  :rule-classes (:definition))

(defcong cons-equiv equal (element a y) 1)

(defthm element-implication
  (implies
   (element a y)
   (and (memberp (car a) (keys y))
	(equal (cdr a) (cdr (getv (car a) y)))))
  :rule-classes (:forward-chaining))

(defthm element-elements-implication
  (implies
   (and (memberp (car a) (keys y))
	(equal (cdr a) (cdr (getv (car a) y))))
   (element a y))
  :rule-classes (:forward-chaining))

(defthm not-element-elements-implication-1
  (implies
   (not (memberp (car a) (keys y)))
   (not (element a y)))
  :rule-classes (:forward-chaining))

(defthm not-element-elements-implication-2
  (implies
   (not (equal (cdr a) (cdr (getv (car a) y))))
   (not (element a y)))
  :rule-classes (:forward-chaining))

(defthm element-base
  (implies
   (not (consp x))
   (not (element a x)))
  :hints (("Goal" :in-theory (enable element))))

(defthm element-cons
  (equal (element a (cons x y))
	 (if (equal (car a) (car x))
	     (equal (cdr a) (cdr x))
	   (element a y)))
  :hints (("Goal" :in-theory (enable element))))

(defthm element-append
  (equal (element a (append x y))
	 (if (memberp (car a) (keys x))
	     (element a x)
	   (element a y)))
  :hints (("Goal" :induct (append x y)
	   :in-theory (enable memberp append element))))

|#

(defthm assoc-append
  (equal (assoc a (append x y))
	 (if (memberp a (keys x))
	     (assoc a x)
	   (assoc a y))))

(defthm keys-append
  (equal (keys (append x y))
	 (append (keys x)
		 (keys y))))


;; pick-a-point

#|
(defthm consp-implies-memberp
  (implies
   (consp x)
   (memberp (caar x) (keys x))))
|#

(defun assoc-equiv (list x y)
  (declare (type t list x y))
  (if (consp list)
      (and (cons-equiv (assox (car list) x)
		       (assox (car list) y))
	   (assoc-equiv (cdr list) x y))
    t))

(defthm assoc-equiv-commute
  (implies
   (syntaxp (acl2::good-rewrite-order x y))
   (equal (assoc-equiv list y x)
	  (assoc-equiv list x y)))
  :rule-classes ((:rewrite :loop-stopper nil)))

;; I think perhaps this should be disabled.  Perhaps the only reason
;; for doing this is to avoid having so many chaining rules .. but I
;; think it would be better to solve the problem of chaining rules by
;; commuting their conclusion than by duplicating every equivalence
;; relation in the hypothesis.

(defthm assoc-equiv-commute-fwd
  (implies
   (assoc-equiv list x y)
   (assoc-equiv list y x))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable assoc-equiv-commute))))

(defthm assoc-equiv-memberp
  (implies
   (and
    (assoc-equiv list x y)
    (memberp a list)
    (syntaxp (acl2::good-rewrite-order x y)))
   (cons-equiv (assoc a x)
	       (assoc a y)))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-subsetp-1
  (implies
   (and
    (list::subsetp a b)
    (assoc-equiv b x y))
   (assoc-equiv a x y))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-subsetp-2
  (implies
   (and
    (assoc-equiv b x y)
    (list::subsetp a b))
   (assoc-equiv a x y))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-chaining-1
  (implies
   (and
    (assoc-equiv a w x)
    (assoc-equiv a x y))
   (assoc-equiv a w y))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-chaining-2
  (implies
   (and
    (assoc-equiv a x y)
    (assoc-equiv a w x))
   (assoc-equiv a w y))
  :rule-classes (:rewrite :forward-chaining))

(encapsulate
 ()

 (encapsulate
  (((assocequiv-hyps) => *)
   ((assocequiv-list) => *)
   ((assocequiv-lhs) => *)
   ((assocequiv-rhs) => *))

  (local (defun assocequiv-hyps () nil))
  (local (defun assocequiv-lhs  () nil))
  (local (defun assocequiv-rhs  () nil))
  (local (defun assocequiv-list () nil))

  (defthm subdomain-multiplicity-constraint
    (implies
     (and
      (assocequiv-hyps)
      (memberp arbitrary-element (assocequiv-list)))
     (cons-equiv (assoc arbitrary-element (assocequiv-lhs))
		 (assoc arbitrary-element (assocequiv-rhs))))
    :rule-classes nil)
  )

 (local (defun badguy (list x y)
          (cond ((atom list)
                 nil)
                ((not (cons-equiv (assoc (car list) x)
				  (assoc (car list) y)))
                 (car list))
                (t (badguy (cdr list) x y)))))

 (local (defthm badguy-witness
          (implies (not (assoc-equiv list x y))
                   (not (cons-equiv (assoc (badguy list x y) x)
				    (assoc (badguy list x y) y))))))

 (local (defthm badguy-witness-2
          (implies (not (memberp (badguy list x y) list))
                   (assoc-equiv list x y))))

 (defthm assocequiv-by-multiplicity-driver
   (implies (assocequiv-hyps)
            (assoc-equiv (assocequiv-list) (assocequiv-lhs) (assocequiv-rhs)))
   :rule-classes nil
   :hints(("Goal"
           :use ((:instance
                  subdomain-multiplicity-constraint
                  (arbitrary-element (badguy (assocequiv-list) (assocequiv-lhs) (assocequiv-rhs))))))))

 (ADVISER::defadvice assocequiv-by-multiplicity
   (implies (assocequiv-hyps)
            (assoc-equiv (assocequiv-list) (assocequiv-lhs) (assocequiv-rhs)))
   :rule-classes (:pick-a-point :driver assocequiv-by-multiplicity-driver))

 )


(in-theory (disable assoc-equiv))

(defcong list::setequiv equal (assoc-equiv list x y) 1)

(defun subdomain (x y)
  (and (assoc-equiv (keys x) x y)
       (list::subsetp (keys x) (keys y))))

;; Can we avoid saying anything about the keys?

(defun keyquiv (x y)
  (declare (type t x y))
  (and (list::setequiv (keys x) (keys y))
       (assoc-equiv (keys x) x y)
       (assoc-equiv (keys y) y x)))

(defequiv keyquiv)

(defthm assoc-non-memberp
  (implies
   (not (memberp a (keys alist)))
   (equal (assoc a alist) nil)))

(defthm car-assoc-memberp
  (implies
   (memberp a (keys alist))
   (equal (car (assoc a alist))
	  a)))

(defcong keyquiv cons-equiv (assoc a x) 2
  :hints (("Goal" :cases ((memberp a (keys x))))))

(defcong keyquiv keyquiv (cons a x) 2)
(defcong cons-equiv keyquiv (cons a x) 1)

(defcong keyquiv keyquiv (append a x) 2
  :hints (("Goal" :in-theory (disable LIST::SETEQUIV-REMOVE-DEFINITION))))

(defcong keyquiv keyquiv (append a x) 1
  :hints (("Goal" :in-theory (disable LIST::SETEQUIV-REMOVE-DEFINITION))))

(defcong keyquiv list::setequiv (keys x) 1)

;; this proof tells us that "keys" is order independent
;; w/to the alist.  However, I'm not sure if this
;; is a useful result (?)

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm member-not-member-remove-implies-equal-car
       (implies
	(and
	 (not (memberp a (keys (remove c x))))
	 (memberp a (keys x)))
	(equal (car c) a))
       :rule-classes (:forward-chaining))

     (defthm memberp-implies-memberp-car-keys
       (implies
	(and
	 (memberp c y)
	 (equal (car c) a))
	(memberp a (keys y)))
       :rule-classes (:forward-chaining))

     (defthm memberp-keys-remove-implies-memberp-keys
       (implies
	(memberp a (keys (remove c x)))
	(memberp a (keys x)))
       :rule-classes (:forward-chaining))

     (encapsulate
	 ()

       (local (include-book "../lists/remove-induction"))

       (defthm keys-remove
	 (implies
	  (and
	   (list::setequiv x y)
	   (memberp a (keys x)))
	  (memberp a (keys y)))
	 :hints (("Goal" :induct (list::remove-induction-2 x y))))

       )))


  (defcong list::setequiv list::setequiv (keys x) 1)

  )

(defthm keyquiv-cons-commute
  (implies
   (not (equal (car a) (car b)))
   (keyquiv (cons a (cons b x))
	    (cons b (cons a x)))))

(defthm keyquiv-cons-crush
  (implies
   (equal (car a) (car b))
   (keyquiv (cons a (cons b x))
	    (cons a x))))

(in-theory (disable keyquiv))

(defthm keyquiv-assoc-substitution
  (implies
   (and
    (alist::keyquiv x y)
    (syntaxp (acl2::good-rewrite-order x y)))
   (cons-equiv (assoc a x)
	       (assoc a y))))

(defcong keyquiv equal (assoc-equiv list x y) 2)
(defcong keyquiv equal (assoc-equiv list x y) 3)

(defthmd assoc-equiv-append
  (equal (alist::assoc-equiv (append x y) a b)
	 (and (alist::assoc-equiv x a b)
	      (alist::assoc-equiv y a b)))
  :hints (("Goal" :in-theory (enable list::memberp-of-append))))

(encapsulate
 ()

 (encapsulate
  (((setequiv-hyps) => *)
   ((setequiv-lhs) => *)
   ((setequiv-rhs) => *)
   )

  (local (defun setequiv-hyps () nil))
  (local (defun setequiv-lhs () nil))
  (local (defun setequiv-rhs () nil))

  (defthm setequiv-multiplicity-constraint
    (implies
     (setequiv-hyps)
     (equal (memberp arbitrary-element (setequiv-lhs))
	    (memberp arbitrary-element (setequiv-rhs))))
    :rule-classes nil)
  )

 )

(encapsulate
 ()

 (encapsulate
  (((keyquiv-hyps) => *)
   ((keyquiv-lhs) => *)
   ((keyquiv-rhs) => *))

  (local (defun keyquiv-hyps () nil))
  (local (defun keyquiv-lhs  () nil))
  (local (defun keyquiv-rhs  () nil))

  (defthm keyquiv-subdomain-multiplicity-constraint
    (implies
     (keyquiv-hyps)
     (and (cons-equiv (assoc arbitrary-element (keyquiv-lhs))
		      (assoc arbitrary-element (keyquiv-rhs)))
	  (equal (memberp arbitrary-element (keys (keyquiv-lhs)))
		 (memberp arbitrary-element (keys (keyquiv-rhs))))))
    :rule-classes nil)
  )

 (defthm keyquiv-by-multiplicity-driver
   (implies (keyquiv-hyps)
            (keyquiv (keyquiv-lhs) (keyquiv-rhs)))
   :rule-classes nil
   :hints ((and stable-under-simplificationp
		'(:use (keyquiv-subdomain-multiplicity-constraint
			(:instance keyquiv-subdomain-multiplicity-constraint
				   (arbitrary-element list::arbitrary-element)))))
	   ("Goal" :in-theory (enable keyquiv)
	    :use ((:instance (:functional-instance assocequiv-by-multiplicity-driver
						   (assocequiv-hyps keyquiv-hyps)
						   (assocequiv-list (lambda () (keys (keyquiv-lhs))))
						   (assocequiv-lhs  keyquiv-lhs)
						   (assocequiv-rhs  keyquiv-rhs)))
		  (:instance (:functional-instance assocequiv-by-multiplicity-driver
						   (assocequiv-hyps keyquiv-hyps)
						   (assocequiv-list (lambda () (keys (keyquiv-rhs))))
						   (assocequiv-lhs  keyquiv-rhs)
						   (assocequiv-rhs  keyquiv-lhs)))
		  (:instance (:functional-instance list::setequiv-by-multiplicity-driver
						   (list::setequiv-hyps keyquiv-hyps)
						   (list::setequiv-lhs  (lambda () (keys (keyquiv-lhs))))
						   (list::setequiv-rhs  (lambda () (keys (keyquiv-rhs))))))))))
 (ADVISER::defadvice keyquiv-by-multiplicity
		     (implies (keyquiv-hyps)
			      (keyquiv (keyquiv-lhs) (keyquiv-rhs)))
		     :rule-classes (:pick-a-point :driver keyquiv-by-multiplicity-driver))

 )

(defun setv (a v alist)
  (cons (cons a v) alist))

(defun getv (a alist)
  (cdr (assoc a alist)))

(defcong keyquiv equal (getv a r) 2)
(defcong keyquiv keyquiv (setv a v r) 3)

(defthm getv-over-setv
  (equal (getv a (setv b v r))
	 (if (equal a b)
	     v
	   (getv a r))))

(defthm setv-over-setv
  (implies
   (not (equal a b))
   (keyquiv (setv a v (setv b w r))
	    (setv b w (setv a v r)))))

(defthm setv-of-setv
  (keyquiv (setv a v (setv a w r))
	   (setv a v r)))

(defthm setv-of-getv
  (implies
   (memberp a (keys r))
   (keyquiv (setv a (getv a r) r)
	    r))
  :hints (("Goal" :in-theory (enable keyquiv))))

(defthm keys-setv
  (equal (keys (setv a v r))
	 (cons a (keys r))))

(defun clr (key alist)
  (declare (type t key alist))
  (if (consp alist)
      (if (if (consp (car alist)) (equal key (caar alist)) (null key))
	  (clr key (cdr alist))
	(cons (car alist)
	      (clr key (cdr alist))))
    alist))

(defthm clr-append
  (equal (clr a (append x y))
	 (append (clr a x) (clr a y))))

(defthm clr-clr-commute
  (equal (clr a (clr b x))
	 (clr b (clr a x))))

(defthm keys-clr
  (equal (keys (clr key alist))
	 (remove key (keys alist))))

(defthm assoc-clr
  (equal (assoc a (clr key x))
	 (if (equal a key) nil
	   (assoc a x))))

(in-theory (disable LIST::SETEQUIV-REMOVE-DEFINITION))

(defcong keyquiv keyquiv (clr key r) 2)

(defthm getv-clr
  (equal (getv a (clr key alist))
	 (if (equal a key) nil
	   (getv a alist))))

(defthm clr-over-setv
  (implies
   (not (equal a b))
   (keyquiv (clr a (setv b v r))
	    (setv b v (clr a r)))))

(defthm clr-of-setv
  (keyquiv (clr a (setv a v r))
	   (clr a r)))

(defthm acl2-count-cdr-<=
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes (:linear))

(defthm acl2-count-car-<=
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes (:linear))

(defthm memberp-clr-non-increasing
  (<= (acl2-count (clr a alist)) (acl2-count alist))
  :hints (("goal" :induct (clr a alist)))
  :rule-classes (:linear))

(defthm memberp-clr-decreases
  (implies
   (memberp a (keys alist))
   (< (acl2-count (clr a alist)) (acl2-count alist)))
  :hints (("goal" :induct (clr a alist)))
  :rule-classes (:linear))

(defthm memberp-cons
  (implies
   (consp alist)
   (memberp (caar alist) (keys alist))))

(defthm acl2-count-assoc-<=
  (<= (acl2-count (assoc a list)) (acl2-count list))
  :hints (("Goal" :induct (assoc a list)))
  :rule-classes (:linear))

(defthm acl2-count-assoc-memberp-<
  (implies
   (memberp key (keys list))
   (< (acl2-count (assoc a list)) (acl2-count list)))
  :hints (("Goal" :induct (assoc a list)))
  :rule-classes (:linear))

(defthm acl2-count-getv-<=
  (<= (acl2-count (alist::getv key alist1)) (acl2-count alist1))
  :rule-classes (:linear))

(defthm acl2-count-getv-<
  (implies
   (memberp key (alist::keys alist1))
   (< (acl2-count (alist::getv key alist1)) (acl2-count alist1)))
  :rule-classes (:linear))

(in-theory (disable setv getv clr)) ;;  keys))

;; This should be true in general

(include-book "../lists/remove")

(defun def-equivp (list x y)
  (and (assoc-equiv (list::remove-list list (keys x)) x y)
       (assoc-equiv (list::remove-list list (keys y)) y x)))

(defthm keyquiv-implies-assoc-equiv
  (implies
   (keyquiv x y)
   (assoc-equiv list x y)))

(defthm keyquiv-implies-def-equivp
  (implies
   (keyquiv x y)
   (def-equivp list x y)))

(local
 (defthm assoc-equiv-remove-list-reduction
   (implies
    (assoc-equiv a x y)
    (equal (assoc-equiv (list::remove-list a b) x y)
	   (assoc-equiv b x y))))
 )

(defthm keyquiv-from-setequiv-assoc-equiv
  (implies
   (and
    (list::setequiv (keys x) (keys y))
    (assoc-equiv (keys x) x y))
   (keyquiv x y))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (keyquiv)
				  (KEYQUIV-BY-MULTIPLICITY)))))

(defthm keyquiv-reduction
  (equal (keyquiv x y)
	 (and (list::setequiv (keys x) (keys y))
	      (assoc-equiv list x y)
	      (def-equivp list x y)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t)))

(defthm def-equivp-reduction
  (equal (def-equivp keys x y)
	 (and (assoc-equiv (list::remove-list keys list) x y)
	      (def-equivp (append keys list) x y)))
  :hints (("Goal" :in-theory (disable
			      LIST::MEMBERP-DISJOINT-NON-MEMBERP
			      LIST::MEMBER-IS-MEMBERP-PROPOSITIONALLY
			      ASSOC-EQUIV-SUBSETP-2
			      LIST::MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP
			      LIST::REMOVE-LIST
			      LIST::REMOVE-LIST-SUPERSET-REDUCTION
			      LIST::MEMBERP-REMOVE-LIST
			      ))
; Matt K. mod, 1/28/2017, to accommodate fix for soundness bug in functional
; instantiation: these hints trigger further, inappropriate use of the
; "[Adviser]" computed hint -- they cause arbitrary-element to be a free
; variable that is both in the range of the functional substitution and in the
; constraints.  Our solution is to apply the appropriate :cases hints only at
; the appropriate time.

#||
	  (and stable-under-simplificationp
	       '(:cases ((list::memberp arbitrary-element (append (keys x) (keys y))))))
	  (and stable-under-simplificationp
	       '(:do-not-induct t :cases ((list::memberp arbitrary-element list))))
||#

          ("Subgoal 5.1" :cases ((list::memberp arbitrary-element (append (keys x) (keys y)))))
          ("Subgoal 2.1" :cases ((list::memberp arbitrary-element list)))
          ("Subgoal 1.1" :cases ((list::memberp arbitrary-element list)))
          )
  :rule-classes nil)
