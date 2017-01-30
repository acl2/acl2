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

(in-package "ALIST")

;;
;; A book about alists used in binding environments.
;;

(include-book "../util/mv-nth")
(include-book "../nary/nary")
(include-book "../util/good-rewrite-order")
(include-book "keyquiv")
(include-book "../bags/top")
(include-book "misc/total-order" :dir :system)

;; bindequiv is like keyquiv except that it does not provide any
;; guarantees about the domain of the alists .. only the range.
;; This is more likely to be of use in reasoning about binding
;; enviornments.  This relation probably should have come first.

(defun bindequiv (x y)
  (and (assoc-equiv (keys x) x y)
       (assoc-equiv (keys y) y x)))

(defthm assoc-from-assoc-equiv-keys
  (implies
   (and
    (assoc-equiv (keys y) y x)
    (syntaxp (acl2::good-rewrite-order y x)))
   (cons-equiv (assoc a y)
	       (if (list::memberp a (keys y))
		   (assoc a x)
		 nil))))

(defthmd assoc-from-assoc-equiv-keys-alt
  (implies
   (and
    (assoc-equiv (keys y) y x)
    (syntaxp (acl2::good-rewrite-order x y)))
   (cons-equiv (assoc a y)
	       (if (list::memberp a (keys y))
		   (assoc a x)
		 nil))))

(theory-invariant
 (incompatible
  (:rewrite assoc-from-assoc-equiv-keys-alt)
  (:rewrite assoc-from-assoc-equiv-keys)
  ))

(theory-invariant
 (incompatible
  (:rewrite assoc-from-assoc-equiv-keys-alt)
  (:rewrite ASSOC-EQUIV-MEMBERP)
  ))

(encapsulate
    ()

  (local
   (defthm bindequiv-chaining
     (implies
      (and
       (bindequiv x y)
       (bindequiv y z))
      (bindequiv x z))
     :rule-classes (:rewrite :forward-chaining)
     :hints ((and stable-under-simplificationp
		  (acl2::occur-lst 'ARBITRARY-ELEMENT clause)
		  '(:cases ((list::memberp ARBITRARY-ELEMENT (keys z)))))
	     (and stable-under-simplificationp
		  (acl2::occur-lst 'ARBITRARY-ELEMENT clause)
		  '(:in-theory (e/d (assoc-from-assoc-equiv-keys-alt)
				    (ASSOC-EQUIV-MEMBERP
				     assoc-from-assoc-equiv-keys))))
	     )))

  (local
   (defthm bindequiv-props
     (AND (BOOLEANP (BINDEQUIV X Y))
	  (BINDEQUIV X X)
	  (IMPLIES (BINDEQUIV X Y)
		   (BINDEQUIV Y X)))))

  (defequiv bindequiv
    :hints (("Goal" :in-theory (disable bindequiv))))


  )


(defrefinement keyquiv bindequiv
  :hints (("Goal" :in-theory (enable bindequiv keyquiv))))

(defcong bindequiv  cons-equiv (assoc a x) 2
  :hints ((and stable-under-simplificationp
		  `(:in-theory (e/d (assoc-from-assoc-equiv-keys-alt)
				    (ASSOC-EQUIV-MEMBERP
				     assoc-from-assoc-equiv-keys))))))

(defthm bindequiv-assoc-substitution
  (implies
   (and
    (bindequiv x y)
    (syntaxp (acl2::good-rewrite-order x y)))
   (cons-equiv (assoc a x)
	       (assoc a y)))
  :hints (("Goal" :in-theory (disable bindequiv))))

; Matt K. mod, 1/28/2017, to accommodate fix for soundness bug in functional
; instantiation: This no longer proves, and it without knowledge of this
; material, I found it wasn't trivial to hack a fix.  This lemma isn't used in
; the result of this file, so I'll take a chance by commenting it out.

#||
(defthm bindequiv-reduction
  (equal (bindequiv x y)
	 (and (assoc-equiv list x y)
	      (def-equivp list x y)))
  :hints ((and stable-under-simplificationp
	       '(:in-theory (enable LIST::MEMBERP-OF-APPEND)
			    :cases ((list::memberp arbitrary-element (append (keys x) (keys y))))))
	  (and stable-under-simplificationp
	       '(:in-theory (enable LIST::MEMBERP-OF-APPEND)
			    :cases ((list::memberp arbitrary-element list)))))
  :rule-classes nil)
||#

(encapsulate
 ()

 (encapsulate
  (((bindequiv-hyps) => *)
   ((bindequiv-lhs) => *)
   ((bindequiv-rhs) => *))

  (local (defun bindequiv-hyps () nil))
  (local (defun bindequiv-lhs  () nil))
  (local (defun bindequiv-rhs  () nil))

  (defthm bindequiv-subdomain-multiplicity-constraint
    (implies
     (bindequiv-hyps)
     (cons-equiv (assoc arbitrary-element (bindequiv-lhs))
		 (assoc arbitrary-element (bindequiv-rhs))))
    :rule-classes nil)
  )

 (defthm bindequiv-by-multiplicity-driver
   (implies (bindequiv-hyps)
            (bindequiv (bindequiv-lhs) (bindequiv-rhs)))
   :rule-classes nil
   :hints ((and stable-under-simplificationp
		'(:use (bindequiv-subdomain-multiplicity-constraint
			(:instance bindequiv-subdomain-multiplicity-constraint
				   (arbitrary-element list::arbitrary-element)))))
	   ("Goal" :in-theory (enable bindequiv)
	    :use ((:instance (:functional-instance assocequiv-by-multiplicity-driver
						   (assocequiv-hyps bindequiv-hyps)
						   (assocequiv-list (lambda () (keys (bindequiv-lhs))))
						   (assocequiv-lhs  bindequiv-lhs)
						   (assocequiv-rhs  bindequiv-rhs)))
		  (:instance (:functional-instance assocequiv-by-multiplicity-driver
						   (assocequiv-hyps bindequiv-hyps)
						   (assocequiv-list (lambda () (keys (bindequiv-rhs))))
						   (assocequiv-lhs  bindequiv-rhs)
						   (assocequiv-rhs  bindequiv-lhs)))
		  ))))

 (ADVISER::defadvice bindequiv-by-multiplicity
		     (implies (bindequiv-hyps)
			      (bindequiv (bindequiv-lhs) (bindequiv-rhs)))
		     :rule-classes (:pick-a-point :driver bindequiv-by-multiplicity-driver))

 )

(in-theory (disable bindequiv))

(defcong bindequiv  bindequiv  (cons p x) 2)

(defcong bindequiv  bindequiv  (acons k v x) 3)

(defcong cons-equiv bindequiv  (cons p x) 1)

(defcong bindequiv  bindequiv  (append x y) 2)

;; Here is a curious turn of events.  Because association lists are
;; order dependent, we do not get bindequiv congruence in the first
;; argument of append (!)  This gets us back to thinking about
;; associatins in terms of their entire domain .. which is where we
;; started.  In other words, we may be stuck with keyquiv in the long
;; run because bindequiv is just too weak.  Append may not seem like
;; such a loss .. but what will we do with other functions that update
;; alists en mass?

(defcong keyquiv bindequiv (append x y) 1)

(defthm bindequiv-cons-commute
  (implies
   (not (equal (car a) (car b)))
   (bindequiv (cons a (cons b x))
	      (cons b (cons a x)))))

(defthm bindequiv-cons-crush
  (implies
   (equal (car a) (car b))
   (bindequiv (cons a (cons b x))
	      (cons a x))))

;;

(defmacro alist::use-equivp (domain x y)
  `(alist::assoc-equiv ,domain ,x ,y))

(acl2::defequiv+ (alist::use-equivp domain x y)
  :lhs x
  :rhs y
  :equiv   alist::use-equiv
  :context alist::use-ctx
  :keywords t
  :chaining t
  )

(defthm alist::use-equivp-id
  (alist::use-equivp domain x x))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-eq-is-assoc
;   (equal (assoc-eq key list)
;          (assoc key list)))

(defthm assoc-equiv-rewrite-order
  (implies
   (syntaxp (acl2::good-rewrite-order y x))
   (equal (alist::assoc-equiv domain x y)
	  (alist::assoc-equiv domain y x))))

(in-theory (disable ALIST::ASSOC-EQUIV-COMMUTE))

(defthm assoc-equiv-substitution
  (implies
   (and
    (alist::assoc-equiv d1 x y)
    (syntaxp (acl2::good-rewrite-order x y))
    (list::subsetp d2 d1))
   (alist::use-equiv :lhs x
		     :rhs y
		     :domain d2)))

(defthm assoc-use-cong
  (implies
   (and
    (equal domain (list a))
    (acl2::bind-contextp ((b1 (equal b2 (alist::use-ctx b1 :domain domain))))))
   (alist::cons-equiv (assoc a b1)
		      (assoc a b2))))

(defthm alist::use-equivp-self-characterization
  (implies
   (acl2::bind-contextp ((x (equal a (alist::use-ctx x :domain domain)))
			 (y (equal b (alist::use-ctx y :domain domain)))))
   (equal (alist::use-equivp domain x y)
	  (alist::use-equivp domain a b))))

(defthm use-equiv-cons-not-member-reduction
  (implies
   (not (list::memberp (car a) domain))
   (alist::use-equiv :lhs (cons a list)
		     :rhs list
		     :domain domain)))

(defthm use-equiv-cons-normal-form
  (implies
   (and
    (syntaxp (acl2::<< (car b) (car a)))
    (not (equal (car a) (car b))))
   (alist::use-equiv :lhs (cons a (cons b x))
		     :rhs (cons b (cons a x)))))

(defthm use-equiv-append-normal-form
  (implies
   (and
    (syntaxp (acl2::<< y x))
    (bag::disjoint (alist::keys x) (alist::keys y)))
   (alist::use-equiv :lhs (append x y)
		     :rhs (append y x))))

;; ===========================================================================
;;
;; This was the easy property ..  dropping the first argument to
;; append will be tougher.
;;
;; ===========================================================================

(defthm use-equiv-append-reduction-2
  (implies
   (list::subsetp domain (alist::keys x))
   (alist::use-equiv :lhs (append x y)
		     :rhs x
		     :domain domain)))


;; ===========================================================================
;;
;; assoc-transparent: either the keys are disjoint or the bound values
;; are equal.
;;
;; ===========================================================================


(defun assoc-transparent (key value alist)
  (if (consp alist)
      (and (implies (equal key (caar alist)) (equal value (cdar alist)))
	   (assoc-transparent key value (cdr alist)))
    t))

(defthm assoc-transparent-append
  (equal (assoc-transparent key value (append x y))
	 (and (assoc-transparent key value x)
	      (assoc-transparent key value y))))

(defthm assoc-transparent-implies-cons-equiv-assoc
  (implies
   (assoc-transparent key value x)
   (alist::cons-equiv (assoc key x)
		      (and (list::memberp key (alist::keys x)) (cons key value))))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthmd assoc-transparent-implies-cons-equiv-assoc-2
  (implies
   (and
    (assoc-transparent key (cdr (assoc key x)) y)
    (list::memberp key (alist::keys y)))
   (alist::cons-equiv (assoc key x)
		      (and (list::memberp key (alist::keys x)) (assoc key y))))
  :hints (("Goal" :induct (assoc key y)
	   :in-theory (enable alist::keys))))

(defthm assoc-transparent-non-memberp
  (implies
   (not (list::memberp key (alist::keys x)))
   (assoc-transparent key nil x))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm use-equiv-cons-assoc-transparent-reduction
  (implies
   (and
    (assoc-transparent (car a) (cdr a) list)
    (list::memberp (car a) (alist::keys list)))
   (alist::use-equiv :lhs (cons a list)
		     :rhs list
		     :domain domain))
  :hints (("Goal" :in-theory (enable alist::keys))))

;; ===========================================================================
;;
;; unified-domain-binding: the alist is self-assoc-transparent.
;;
;; cross-domain-binding: the glue that combines two parts of a
;; unified-domain-binding.
;;
;; ===========================================================================


(defun unified-domain-binding (domain alist)
  (if (consp domain)
      (and (assoc-transparent (car domain) (cdr (assoc (car domain) alist)) alist)
	   (unified-domain-binding (cdr domain) alist))
    t))

(defun cross-domain-binding (domain x y)
  (if (consp domain)
      (let ((key (car domain)))
	(and (implies (list::memberp key (alist::keys x))
		      (assoc-transparent key (cdr (assoc key x)) y))
	     (cross-domain-binding (cdr domain) x y)))
    t))

(defthm disjoint-cross-domain-binding
  (implies
   (bag::disjoint (alist::keys x) (alist::keys y))
   (cross-domain-binding domain x y))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm cross-domain-binding-replacement
  (implies
   (and
    (cross-domain-binding domain x y)
    (list::memberp key domain)
    (list::memberp key (alist::keys y)))
   (alist::cons-equiv (assoc key x)
		      (and (list::memberp key (alist::keys x)) (assoc key y)))))


(defthmd cross-domain-binding-cons
  (implies
   (and
    (consp x)
    (unified-domain-binding domain x))
   (equal (cross-domain-binding domain x y)
	  (and (implies (list::memberp (caar x) domain)
			(assoc-transparent (caar x) (cdar x) y))
	       (cross-domain-binding domain (cdr x) y))))
  :hints (("Goal" :induct (cross-domain-binding domain x y)
	   :in-theory (enable alist::keys))))

(defthmd cross-domain-binding-not-cons
  (implies
   (not (consp x))
   (cross-domain-binding domain x y))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthmd unified-domain-binding-cons
  (implies
   (consp x)
   (equal (unified-domain-binding domain x)
	  (and (implies (list::memberp (caar x) domain)
			(assoc-transparent (caar x) (cdar x) (cdr x)))
	       (unified-domain-binding domain (cdr x)))))
  :hints (("Goal" :induct (unified-domain-binding domain x)
	   :in-theory (enable alist::keys))))

(defthmd unified-domain-binding-non-cons
  (implies
   (not (consp x))
   (unified-domain-binding domain x)))

(defthm unified-domain-binding-append
  (equal (unified-domain-binding domain (append x y))
	 (and (unified-domain-binding domain x)
	      (unified-domain-binding domain y)
	      (cross-domain-binding domain x y)))
  :hints (("Goal" :induct (append x y)
	   :in-theory (enable append
			      unified-domain-binding-cons
			      unified-domain-binding-non-cons
			      cross-domain-binding-cons
			      cross-domain-binding-not-cons
			      ))))

(defthm use-equiv-append-reduction-1
  (implies
   (and
    (cross-domain-binding d1 x y)
    (list::subsetp domain d1)
    (list::subsetp domain (alist::keys y)))
   (alist::use-equiv :lhs (append x y)
		     :rhs y
		     :domain domain))
  :hints (("Goal" :in-theory (disable ASSOC-EQUIV-SUBSTITUTION)))
  :otf-flg t)

(defthmd unified-domain-binding-append-1
  (equal (alist::unified-domain-binding (append x y) z)
	 (and (alist::unified-domain-binding x z)
	      (alist::unified-domain-binding y z))))


;; ===========================================================================
;;
;; unified-binding: the alist is self-consistent w/to unified-domain-bindings
;;
;; ===========================================================================

(defund unified-binding (alist)
  (unified-domain-binding (alist::keys alist) alist))

(defun equiv-domain-binding (domain x y)
  (and (cross-domain-binding domain x y)
       (cross-domain-binding domain y x)))

(defthm unified-domain-binding-subsetp
  (implies
   (and
    (unified-domain-binding y a)
    (list::subsetp x y))
   (unified-domain-binding x a)))
