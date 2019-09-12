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
(include-book "../lists/basic")
(include-book "../util/iff")

;; Use assox to ensure minimal guard obligations.

(defun assox (key alist)
  (declare (type t key alist))
  (if (consp alist)
      (let ((entry (car alist)))
	(if (consp entry)
	    (if (equal key (car entry)) entry
	      (assox key (cdr alist)))
	  (if (null key) entry
	    (assox key (cdr alist)))))
    nil))

(defthm assox-reduction
  (equal (assox key alist)
	 (assoc key alist)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-equal-reduction
;   (equal (assoc-equal x y)
;          (assoc x y)))

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

(defund cons-equiv (x y)
  (declare (type t x y))
  (equal (consfix x)
         (consfix y)))

(defequiv cons-equiv
  :hints(("Goal" :in-theory (enable cons-equiv))))

(defthm consfix-in-cons-equiv
  (cons-equiv (consfix x)
              x)
  :hints(("Goal" :in-theory (enable cons-equiv))))

(defcong cons-equiv equal (car x) 1
  :hints(("Goal" :in-theory (enable cons-equiv consfix))))

(defcong cons-equiv equal (cdr x) 1
  :hints(("Goal" :in-theory (enable cons-equiv consfix))))

(defcong alist::cons-equiv equal (list::cdr? x) 1
  :hints (("Goal" :in-theory (enable list::cdr? alist::cons-equiv))))

(defcong alist::cons-equiv equal (list::cdr! x) 1
  :hints (("Goal" :in-theory (enable list::cdr! alist::cons-equiv))))

(defcong cons-equiv equal (consfix x) 1
  :hints(("Goal" :in-theory (enable cons-equiv consfix))))

(defthm cons-equiv-cases-fwd
  (implies
   (and (equal (car x) (car y))
	(equal (cdr x) (cdr y)))
   (cons-equiv x y))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm not-cons-equiv-cases-fwd-1
  (implies
   (not (equal (car x) (car y)))
   (not (cons-equiv x y)))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm not-cons-equiv-cases-fwd-2
  (implies
   (not (equal (cdr x) (cdr y)))
   (not (cons-equiv x y)))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm cons-equiv-fwd
  (implies
   (cons-equiv x y)
   (and (equal (car x) (car y))
	(equal (cdr x) (cdr y))))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm cons-equiv-cons-reduction-1
  (equal (cons-equiv (cons a b) c)
	 (and (equal a (car c))
	      (equal b (cdr c))))
  :hints (("Goal" :in-theory (enable cons-equiv))))

(defthm cons-equiv-cons-reduction-2
  (equal (cons-equiv a (cons b c))
	 (and (equal (car a) b)
	      (equal (cdr a) c)))
  :hints (("Goal" :in-theory (enable cons-equiv))))

(defthm equal-consfix-to-cons-equiv
  (equal (equal (consfix x) y)
	 (and (consp y)
	      (cons-equiv x y)))
  :hints (("Goal" :in-theory (enable cons-equiv))))

(theory-invariant (incompatible (:rewrite equal-consfix-to-cons-equiv)
                                (:definition cons-equiv)))

;; Interpreting Objects as Alists (alistfix)
;;
;; An alist is a list of pairs.  Since we can now interpret any ACL2 object as
;; a pair using consfix, it is straightforward to interpet any ACL2 object as
;; an alist: any atom is interpreted as the empty alist, and any list is fixed
;; by pair-fixing each of its elements.
;;
;; An alternate definition that I considered was to simply interpret any
;; non-alistp object as the empty alist, and any alist as itself.  But, I think
;; the current approach gives us many nice rules.  In particular, our approach
;; allows alist-equiv to be a refinement of list::equiv, giving us a lot of
;; rewrite rules "for free" (e.g., the lengths are the same).  Other rules work
;; nicely (the keys are the same, the values are the same, etc.)  Finally, we
;; also get to provide very nice congruence rules, e.g., the cars of alist
;; interpretations are cons-equiv.

(defund alistfix (x)
  (declare (type t x))
  (if (consp x)
      (cons (consfix (car x))
            (alistfix (cdr x)))
    nil))

(defthm alistfix-type-consp
  (implies (consp x)
           (consp (alistfix x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm alistfix-type-non-consp
  (implies (not (consp x))
           (equal (alistfix x)
                  nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable alistfix))))


;; Note (jcd): Do not add the following rule.  It is redundant with the defcong
;; below for alist-equiv over consp.
;;
;; (defthm consp-alistfix
;;   (equal (consp (alistfix x))
;;          (consp x)))


(defthm alistfix-when-non-consp
  (implies (not (consp alist))
           (equal (alistfix alist)
                  nil)))

(defthm alistfix-when-alist
  (implies (alistp x)
           (equal (alistfix x)
                  x))
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm alistfix-does-nothing
  (equal (equal x (alistfix x))
         (alistp x))
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm alistp-of-alistfix
  (alistp (alistfix x))
  :hints(("Goal" :in-theory (enable alistfix))))



(defthm alistfix-of-cons
  (equal (alistfix (cons a x))
         (cons (consfix a) (alistfix x)))
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm car-of-alistfix
  (equal (car (alistfix a))
         (if (consp a)
             (consfix (car a))
           nil))
  :hints (("Goal" :in-theory (disable EQUAL-CONSFIX-TO-CONS-EQUIV))))

(defthm cdr-of-alistfix
  (equal (cdr (alistfix a))
         (alistfix (cdr a))))

;; Note (jcd): Do not add the following rule.  It is trivial using the
;; congruence rule of alist-equiv for len, along with alistfix-in-alist-equiv.
;;
;; (defthm len-of-alistfix
;;   (equal (len (alistfix a))
;;          (len a)))

(defthm alistfix-of-append
  (equal (alistfix (append x y))
         (append (alistfix x)
                 (alistfix y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm alistfix-of-firstn
  (equal (alistfix (list::firstn n x))
         (list::firstn n (alistfix x)))
  :hints(("Goal" :in-theory (enable list::firstn))))

(defthm alistfix-of-nthcdr
  (equal (alistfix (nthcdr n x))
         (nthcdr n (alistfix x)))
  :hints(("Goal" :in-theory (enable nthcdr))))




;; The Alist Equivalence Relation
;;
;; Given that (with alistfix) we can now think of any object as an alist, the
;; next natural step is to define an equivalence relation wherein objects are
;; considered to be equivalent when their interpretations as alists are the
;; same.
;;
;; IMPORTANT: You might think that alists should be considered to be equivalent
;; whenever "forall a, (assoc a x) = (assoc a y)."  Although equivalent alists
;; will satisfy this property, the converse is NOT true!  For example, if x and
;; y satisfy this property but x has shadowed pairs and y does not, then x and
;; y will not be considered equivalent under alist-equiv!
;;
;; Instead, you should think of alist-equiv as a "structural" relation that
;; essentially is comparing the interpretation of x and y as lists of pairs.
;; But understand that no a priori judgement is made as to how those lists of
;; pairs will be used, and we do not assume that shadowed pairs are irrelevant.

(defund alist-equiv (a b)
  (equal (alistfix a)
         (alistfix b)))

(defequiv alist-equiv
  :hints(("Goal" :in-theory (enable alist-equiv))))

(defrefinement list::equiv alist-equiv
  :hints(("Goal"
          :in-theory (enable alist-equiv)
          :induct (list::len-len-induction x y))))

(defcong alist-equiv equal (alistfix x) 1
  :hints(("Goal" :in-theory (enable alist-equiv))))

(defcong alist-equiv equal (len x) 1
  :hints(("Goal"
          :in-theory (enable alist-equiv)
          :induct (list::len-len-induction x x-equiv))))

(defcong alist-equiv equal (consp x) 1
  :hints(("Goal" :in-theory (enable alist-equiv))))


;; We already have congruence rules that say list::equiv lists have list::equiv
;; cdrs and equal cars.  We now prove that alist-equiv lists have alist-equiv
;; cdrs, which is slightly stronger because it allows us to at least say
;; something about alist-equiv objects which are't quite list::equiv.  We also
;; show that alist-equiv objects have cons-equiv cars, which allows us to say
;; at least something about alist-equiv objects which aren't quite list::equiv.

(defcong alist-equiv alist-equiv (cdr x) 1
  :hints(("Goal" :in-theory (enable alist-equiv alistfix))))

;; bzo (jcd) - There is an error in the ACL2 eliminate destructors code that
;; causes a loop here until segfault if the rule alistfix-type-consp is
;; enabled.  This should be fixed in v2-9-3, at which time we should be able
;; to use only the hint: (in-theory (enable alist-equiv)), and everything
;; should work.

(defcong alist-equiv cons-equiv (car x) 1
  :hints(("Goal"
          :in-theory (e/d (alist-equiv alistfix)
                          (alistfix-type-consp)))))

(defthm alistfix-in-alist-equiv
  (alist-equiv (alistfix a)
               a)
  :hints(("Goal" :in-theory (enable alist-equiv))))

(defthm alist-equiv-cons-cases
  (equal (alist-equiv x (cons y z))
         (and (consp x)
              (cons-equiv y (car x))
              (alist-equiv z (cdr x))))
  :hints(("Goal" :in-theory (enable alist-equiv))))

(defthm equal-of-alistfixes
  (equal (equal (alistfix x) (alistfix y))
         (alist-equiv x y))
  :hints(("Goal" :in-theory (enable alist-equiv))))

(theory-invariant (incompatible (:rewrite equal-of-alist-fixes)
                                (:definition alist-equiv)))
