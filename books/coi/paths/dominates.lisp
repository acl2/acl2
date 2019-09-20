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

;; dominates.lisp
;; Domination relations for lists

(in-package "CPATH")
(include-book "../lists/basic")
(include-book "../lists/memberp")
(include-book "../bags/basic")
(include-book "../adviser/adviser")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "../util/iff"))


;; ----------------------------------------------------------------------------
;;
;;                                   PART 1
;;
;;                          The Dominates Relations
;;
;; ----------------------------------------------------------------------------


;; Dominates
;;
;; We say that list x dominates list y if x is a prefix of y.  We can extend
;; this relation to all ACL2 objects by merely interpreting the objects as
;; lists, i.e., with list::fix.  It is easy to write the dominates function in a
;; straightforward, recursive manner, and that is what we do.

(defund dominates (x y)
  (declare (type t x y))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (dominates (cdr x) (cdr y)))
    t))

;; Another way to look at domination is as follows: x dominates y whenever x is
;; equivalent (in the list sense) to (firstn (len x) y).  This can be a nice
;; way to work with dominates, because now theorems about firstn are available
;; for simplifying terms about dominates.  By default, we keep this alternate
;; definition disabled, but you can enable dominates-redefinition if you would
;; like to use it.

(defthmd dominates-redefinition
  (equal (dominates x y)
         (list::equiv x (firstn (len x) y)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable dominates))))

(theory-invariant (incompatible (:definition dominates)
                                (:definition dominates-redefinition)))


;; Note: Most of the theorems about dominates can be proven with either
;; dominates or dominates-redefinition enabled.  When possible, I prefer to use
;; dominates-redefinition because then ACL2 is forced to use our theorems about
;; firstn.  This is just a basic check that our theorems about firstn are
;; working well.

(defcong list::equiv equal (dominates x y) 1
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defcong list::equiv equal (dominates x y) 2
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-type-1
  (implies (not (consp x))
           (equal (dominates x y) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-type-2
  (implies (and (consp x)
                (not (consp y)))
           (equal (dominates x y) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-non-consp-one
  (implies (not (consp x))
           (dominates x y))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-non-consp-two
  (implies (not (consp y))
           (equal (dominates x y)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm list-equiv-when-dominated
  (implies (dominates x y)
           (equal (list::equiv x y)
                  (equal (len x) (len y))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-reflexive
  (dominates x x)
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-transitive-one
  (implies (and (dominates x y)
                (dominates y z))
           (dominates x z))
  :rule-classes (:rewrite :forward-chaining)
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-transitive-two
  (implies (and (dominates y z)
                (dominates x y))
           (dominates x z))
  :rule-classes (:rewrite :forward-chaining)
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-weakly-asymmetric
  ;; I think this theorem is more clear when list::equiv is used as the
  ;; conclusion, but I prefer to normalize list::equiv under dominates to a
  ;; simple equality test on the lengths of the list, hence the corollary.
  ;; (See the theorem list-equiv-when-dominated, above).
  (implies (dominates x y)
           (equal (dominates y x)
                  (list::equiv x y)))
  :rule-classes ((:rewrite :corollary
                           (implies (dominates x y)
                                    (equal (dominates y x)
                                           (equal (len x) (len y))))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-cons-one
  (equal (dominates (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (dominates x (cdr y))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-cons-two
  (equal (dominates x (cons a y))
         (or (not (consp x))
             (and (equal a (car x))
                  (dominates (cdr x) y))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-append-self-one
  (equal (dominates (append x y) x)
         (not (consp y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm dominates-of-append-self-two
  (dominates x (append x y))
  :hints(("Goal" :in-theory (enable append))))

(defthm dominates-of-append-and-append
  (equal (dominates (append x z) (append x y))
         (dominates z y))
  :hints(("Goal" :in-theory (enable append))))

(defthm len-when-dominated
  (implies (dominates x y)
           (<= (len x) (len y)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm len-larger-when-dominated
  (implies (dominates x y)
           (equal (< (len y) (len x))
                  nil)))

(defthm len-smaller-when-dominated
  (implies (dominates x y)
           (equal (< (len x) (len y))
                  (not (list::equiv x y))))
  :rule-classes ((:rewrite :corollary
                           (implies (dominates x y)
                                    (equal (< (len x) (len y))
                                           (not (equal (len x) (len y)))))))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

;; jcd - can we switch this to be about (equal (len x) (len y)) ?
(defthm dominates-same-len-cheap
  (implies (equal (len x) (len y))
           (equal (dominates x y)
                  (list::equiv x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm nthcdr-len-when-dominates
  (implies (dominates x y)
           (equal (nthcdr (len y) x)
                  (if (equal (len x) (len y))
                      (finalcdr x)
                    nil))))

(defthm append-nthcdr-identity-when-dominates
  (implies (dominates x y)
           (equal (append x (nthcdr (len x) y))
                  y))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-of-nthcdr-and-nthcdr-from-dominates
  (implies (dominates x y)
           (dominates (nthcdr n x) (nthcdr n y)))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm linear-domination-hierarchy
  ;; Given two dominators of z, one of them must dominate the other.  If we
  ;; think of only "well formed" dominators (i.e., those that end with nil),
  ;; then we imagine that this rule shows how all such dominators can be put
  ;; into a hierarchy of domination, where nil is the most superior, followed
  ;; by (list (car z)), on and on until we reach z itself.  Dropping our well
  ;; formedness assumption, what we actually have is a hierarchy of domination
  ;; classes, where each class's members are list::equiv to one another.
  (implies (and (dominates x z)
                (dominates y z)
                (not (dominates x y)))
           (dominates y x))
  :hints(("Goal" :in-theory (enable dominates-redefinition))))

(defthm dominates-from-dominates-of-nthcdr-etc
  ;; bzo - This proof is ugly and relies on using "dominates" rather than
  ;; dominates-redefinition.  This is probably a weakness that should be
  ;; addressed when we have more time.
  (implies (and (dominates (nthcdr (len x) y)
                           (nthcdr (len x) z))
                (dominates x y)
                (dominates x z))
           (dominates y z))
  :hints(("Goal" :in-theory (enable dominates))))





;; Strictly Dominates
;;
;; Given lists a and b, we say that a strictly dominates b whenever a dominates
;; b but a has a smaller length than b.  In other words, whenever a dominates b
;; but a and b are not "the same" (in the sense of list::equiv) list.  In a way,
;; dominates is like <=, and strictly-dominates is like <.

(defund strictly-dominates (x y)
  (declare (type t x y))
  (and (dominates x y)
       ;; bzo - I want to change this to read
       ;; (not (equal (len x) (len y))), since after all our strategy is to
       ;; rewrite list::equiv to equal lengths when dominates is known.
       ;; But, we have to leave this as (not (list::equiv x y)) for now,
       ;; because otherwise the old theory in records/path.lisp won't work
       ;; quite right.
       ;; bzo - use me instead: (not (equal (len x) (len y)))))
       (not (list::equiv x y))))


;; Note: of course strictly-dominates is nonrecursive, so we might have just
;; left it enabled or even defined it as a macro.  Instead, we have chosen to
;; essentially reprove most of the above theorems about dominates.  In exchange
;; for proving these theorems, we are now able to use strictly-dominates as a
;; target for rewrite rules just like any other function.

(defthm strictly-dominates-forward-to-dominates
  ;; Many of the theorems about dominates also apply to strictly-dominates, so
  ;; we write a forward chaining rule that allows us to note whenever we see
  ;; (strictly-dominates x y) that (dominates x y) is also true.
  (implies (strictly-dominates x y)
           (dominates x y))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm not-dominates-forward-to-not-strictly-dominates
  ;; Many of the theorems about dominates also apply to strictly-dominates, so
  ;; we write a forward chaining rule that allows us to note whenever we see
  ;; (strictly-dominates x y) that (dominates x y) is also true.
  (implies (not (dominates x y))
           (not (strictly-dominates x y)))
  :rule-classes :forward-chaining)

(defthm strictly-dominates-implies-dominates
  ;; Even though we have already proven this as a forward chaining rule, we
  ;; also want this available as a rewrite so that theorems about "dominates"
  ;; can also be used to simplify strictly-dominates terms when backchaining.
  (implies (strictly-dominates x y)
           (dominates x y)))

;; By proving the above rules, we have already inherited a good theorem about
;; strictly-dominates through dominates.  However, there are many areas where
;; we can strengthen this theory since additional information is known.  The
;; following theorems are all similar in character to the above rules about
;; dominates, but should each add something more.

(defcong list::equiv equal (strictly-dominates x y) 1
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defcong list::equiv equal (strictly-dominates x y) 2
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-type-1
  (implies (and (not (consp x))
                (consp y))
           (equal (strictly-dominates x y) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-type-2
  (implies (and (consp x)
                (not (consp y)))
           (equal (strictly-dominates x y) nil))
  :rule-classes :type-prescription)

(defthm strictly-dominates-of-non-consp-one
  (implies (not (consp x))
           (equal (strictly-dominates x y)
                  (consp y)))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-non-consp-two
  (implies (not (consp y))
           (equal (strictly-dominates x y)
                  nil))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-irreflexive
  (not (strictly-dominates x x))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-transitive-one
  (implies (and (strictly-dominates x y)
                (strictly-dominates y z))
           (strictly-dominates x z))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-transitive-two
  (implies (and (strictly-dominates y z)
                (strictly-dominates x y))
           (strictly-dominates x z))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-asymmetric
  (implies (strictly-dominates x y)
           (equal (strictly-dominates y x)
                  nil))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-cons-one
  (equal (strictly-dominates (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (strictly-dominates x (cdr y))))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-cons-two
  (equal (strictly-dominates x (cons a y))
         (or (not (consp x))
             (and (equal a (car x))
                  (strictly-dominates (cdr x) y))))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominates-of-append-self-one
  (equal (strictly-dominates (append x y) x)
         nil)
  :hints (("Goal" :in-theory (enable append))))

(defthm strictly-dominates-of-append-self-two
  (equal (strictly-dominates x (append x y))
         (consp y))
  :hints(("Goal" :in-theory (enable append))))

(defthm strictly-dominates-of-append-and-append
  (equal (strictly-dominates (append x z) (append x y))
         (strictly-dominates z y))
  :hints(("Goal" :in-theory (enable append))))

(defthm len-when-strictly-dominated
  (implies (strictly-dominates x y)
           (< (len x) (len y)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(defthm len-equal-when-strictly-dominated
  (implies (strictly-dominates x y)
           (equal (equal (len x) (len y))
                  nil)))

(defthm len-equal-when-strictly-dominated-2
  (implies (strictly-dominates x y)
           (equal (equal (len y) (len x))
                  nil)))

(defthm len-smaller-when-strictly-dominated
  (implies (strictly-dominates x y)
           (equal (< (len x) (len y))
                  t)))

(defthm not-strictly-dominates-of-append-when-not-strictly-dominates
  (implies (not (strictly-dominates a b))
           (not (strictly-dominates (append a x) b)))
  :hints(("goal" :in-theory (enable strictly-dominates))))

(encapsulate
 ()

 (local (defthm lemma
          (implies (not (equal (len x) (len y)))
                   (equal (equal (len (nthcdr n x))
                                 (len (nthcdr n y)))
                          (and (integerp n)
                               (<= (len x) n)
                               (<= (len y) n))))))

 (defthm strictly-dominates-of-nthcdrs-when-strictly-dominates
   (implies (strictly-dominates x y)
            (equal (strictly-dominates (nthcdr n x) (nthcdr n y))
                   (or (not (integerp n))
                       (< n (len x))
                       (< n (len y)))))
   :hints(("Goal" :in-theory (enable strictly-dominates))))

)

(defthm strictly-dominates-from-strictly-dominates-of-nthcdr-etc
  (implies (and (strictly-dominates (nthcdr (len x) y)
                                    (nthcdr (len x) z))
                (dominates x y)
                (dominates x z))
           (strictly-dominates y z))
  :hints(("Goal" :in-theory (enable strictly-dominates))))

(encapsulate
 ()
 (local (defun len-len-len-induction (x y z)
          (if (and (consp x)
                   (consp y)
                   (consp z))
              (len-len-len-induction (cdr x) (cdr y) (cdr z))
            (list x y z))))

 (defthm linear-strict-domination-hierarchy
   (implies (and (dominates x z)
                 (dominates y z)
                 (not (dominates x y)))
            (strictly-dominates y x))
   :hints(("Goal"
           :in-theory (enable strictly-dominates)
           :induct (len-len-len-induction x y z))))
)





;; ----------------------------------------------------------------------------
;;
;;                                   PART 2
;;
;;                Extending the Dominates Relations over Lists
;;
;; ----------------------------------------------------------------------------

;; All Conses
;;
;; We are about to extend our notion of dominates to lists of lists, e.g., so
;; that given some list a and some list of lists x, we can talk about whether
;; or not there are any paths in x that dominate or are dominated by a.  It is
;; useful to be able to talk about the "base" cases where a is an atom, or when
;; x contains some atom, or when x contains no atoms.  (In these cases, the
;; domination relations are trivial).
;;
;; Historical Note: originally we had the function contains-a-non-consp here,
;; which returned true only if the list had an atom as a member.  This is, of
;; course, the same idea as (not (all-conses x)).  However, I prefer to use
;; all-conses, because I think it has nicer rules, particularly for car and cdr
;; and so forth.

(defund all-conses (x)
  (declare (type t x))
  (if (consp x)
      (and (consp (car x))
           (all-conses (cdr x)))
    t))

(defcong list::equiv equal (all-conses x) 1
  :hints(("Goal"
          :in-theory (enable all-conses)
          :induct (list::len-len-induction x x-equiv))))

(defthm all-conses-type-1
  (implies (not (consp x))
           (equal (all-conses x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable all-conses))))

(defthm all-conses-of-consp
  (equal (all-conses (cons a x))
         (and (consp a)
              (all-conses x)))
  :hints(("Goal" :in-theory (enable all-conses))))

(defthm all-conses-of-cdr-when-all-conses
  (implies (all-conses x)
           (all-conses (cdr x))))

(defthm consp-of-car-when-all-conses
  (implies (all-conses x)
           (equal (consp (car x))
                  (consp x))))

(defthm all-conses-from-car/cdr
  (implies (and (consp (car x))
                (all-conses (cdr x)))
           (all-conses x)))

(defthmd consp-when-member-of-all-conses
  (implies (and (all-conses x) ; x is a free variable
                (memberp a x))
           (consp a))
  :hints(("Goal" :in-theory (enable memberp))))

(local (in-theory (enable consp-when-member-of-all-conses)))

(defthmd not-all-conses-when-non-consp-member
  (implies (and (memberp a x)
                (not (consp a)))
           (not (all-conses x)))
  :hints(("Goal" :in-theory (enable memberp))))

(local (in-theory (enable not-all-conses-when-non-consp-member)))

(defthm all-conses-of-append
  (equal (all-conses (append x y))
         (and (all-conses x)
              (all-conses y)))
  :hints(("Goal" :in-theory (enable append))))

(encapsulate
 ()

 (encapsulate
  (((all-conses-hyps) => *)
   ((all-conses-term) => *))
  (local (defun all-conses-hyps () nil))
  (local (defun all-conses-term () nil))
  (defthm all-conses-by-membership-constraint
    (implies (and (all-conses-hyps)
                  (memberp all-conses-element (all-conses-term)))
             (consp all-conses-element))
    :rule-classes nil))

 (local (defund badguy (x)
          (if (endp x)
              nil
            (if (consp (car x))
                (badguy (cdr x))
              (car x)))))

 (local (defthm badguy-works
          (implies (not (all-conses x))
                   (and (memberp (badguy x) x)
                        (not (consp (badguy x)))))
          :hints(("goal" :in-theory (enable badguy)))))

 (defthm all-conses-by-membership-driver
   (implies (all-conses-hyps)
            (all-conses (all-conses-term)))
   :rule-classes nil
   :hints(("Goal"
           :use (:instance all-conses-by-membership-constraint
                           (all-conses-element (badguy (all-conses-term)))))))

 (defadvice all-conses-by-membership
   (implies (all-conses-hyps)
            (all-conses (all-conses-term)))
   :rule-classes (:pick-a-point :driver all-conses-by-membership-driver))
)





(defund no-conses (x)
  (declare (type t x))
  (if (consp x)
      (and (not (consp (car x)))
           (no-conses (cdr x)))
    t))

(defcong list::equiv equal (no-conses x) 1
  :hints(("Goal"
          :in-theory (enable no-conses)
          :induct (list::len-len-induction x x-equiv))))

(defthm no-conses-type-1
  (implies (not (consp x))
           (equal (no-conses x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable no-conses))))

(defthm no-conses-of-consp
  (equal (no-conses (cons a x))
         (and (not (consp a))
              (no-conses x)))
  :hints(("Goal" :in-theory (enable no-conses))))

(defthm no-conses-of-cdr-when-no-conses
  (implies (no-conses x)
           (no-conses (cdr x))))

(defthm consp-of-car-when-no-conses
  (implies (no-conses x)
           (equal (consp (car x))
                  nil)))

(defthm no-conses-from-car/cdr
  (implies (and (not (consp (car x)))
                (no-conses (cdr x)))
           (no-conses x)))

(defthm not-consp-when-member-of-no-conses
  (implies (and (no-conses x) ; x is a free variable
                (memberp a x))
           (equal (consp a)
                  nil))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm not-no-conses-when-consp-member
  (implies (and (memberp a x)
                (consp a))
           (not (no-conses x)))
  :hints(("Goal" :in-theory (enable memberp))))

(defthm no-conses-of-append
  (equal (no-conses (append x y))
         (and (no-conses x)
              (no-conses y)))
  :hints(("Goal" :in-theory (enable append))))

(encapsulate
 ()

 (encapsulate
  (((no-conses-hyps) => *)
   ((no-conses-term) => *))
  (local (defun no-conses-hyps () nil))
  (local (defun no-conses-term () nil))
  (defthm no-conses-by-membership-constraint
    (implies (and (no-conses-hyps)
                  (memberp no-conses-element (no-conses-term)))
             (not (consp no-conses-element)))
    :rule-classes nil))

 (local (defund badguy (x)
          (if (endp x)
              nil
            (if (not (consp (car x)))
                (badguy (cdr x))
              (car x)))))

 (local (defthm badguy-works
          (implies (not (no-conses x))
                   (and (memberp (badguy x) x)
                        (consp (badguy x))))
          :hints(("goal" :in-theory (enable badguy)))))

 (defthm no-conses-by-membership-driver
   (implies (no-conses-hyps)
            (no-conses (no-conses-term)))
   :rule-classes nil
   :hints(("Goal"
           :use (:instance no-conses-by-membership-constraint
                           (no-conses-element (badguy (no-conses-term)))))))

 (defadvice no-conses-by-membership
   (implies (no-conses-hyps)
            (no-conses (no-conses-term)))
   :rule-classes (:pick-a-point :driver no-conses-by-membership-driver))
)






;; Dominates Some
;;
;; Given some list a, and some list of lists x, we say that a "dominates some"
;; list in x whenever there is some list b in x such that a dominates b.

(defund dominates-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (dominates a (car x))
          (dominates-some a (cdr x)))
    nil))

(defcong list::equiv equal (dominates-some a x) 1
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-type-1
  (implies (not (consp x))
           (equal (dominates-some a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-type-2
  (implies (and (consp x)
                (not (consp a)))
           (equal (dominates-some a x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-non-consp-two
  (implies (not (consp x))
           (not (dominates-some a x))))

(defthm dominates-some-non-consp-one
  (implies (not (consp a))
           (equal (dominates-some a x)
                  (consp x))))

(defthm dominates-some-of-cons
  (equal (dominates-some a (cons b x))
         (or (dominates a b)
             (dominates-some a x)))
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-of-append
  (equal (dominates-some a (append x y))
         (or (dominates-some a x)
             (dominates-some a y)))
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm dominates-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (dominates a b))
           (dominates-some a x))
  :hints(("Goal" :in-theory (enable dominates-some))))

(defthm not-dominates-some-forward-to-not-dominates
  (implies (and (not (dominates-some b x))
                (memberp a x)) ;; a is a free variable
           (not (dominates b a)))
  :rule-classes :forward-chaining)

(encapsulate
 ()
 (encapsulate
  (((dominates-some-hyps) => *)
   ((dominates-some-path) => *)
   ((dominates-some-term) => *))
  (local (defun dominates-some-hyps () nil))
  (local (defun dominates-some-path () nil))
  (local (defun dominates-some-term () nil))
  (defthmd not-dominates-some-constraint
    (implies (and (dominates-some-hyps)
                  (list::memberp dominates-some-member
                                 (dominates-some-term)))
             (not (dominates (dominates-some-path)
                             dominates-some-member)))))

 (local (defund which-one? (a x)
          (if (endp x)
              nil
            (if (dominates a (car x))
                (car x)
              (which-one? a (cdr x))))))

 (local (defthm lemma
          (implies (dominates-some a x)
                   (and (memberp (which-one? a x) x)
                        (dominates a (which-one? a x))))
          :hints(("Goal" :in-theory (enable which-one?)))))

 (defthm not-dominates-some-by-membership-driver
   (implies (dominates-some-hyps)
            (not (dominates-some (dominates-some-path)
                                 (dominates-some-term))))
   :hints(("Goal"
           :use (:instance not-dominates-some-constraint
                           (dominates-some-member
                            (which-one? (dominates-some-path)
                                        (dominates-some-term)))))))

 (defadvice not-dominates-some-by-membership
   (implies (dominates-some-hyps)
            (not (dominates-some (dominates-some-path)
                                 (dominates-some-term))))
   :rule-classes (:pick-a-point
                  :driver not-dominates-some-by-membership-driver))
 )



(encapsulate
 ()
 ;; bzo - it would be nice if we could write this lemma in the "more natural"
 ;; way, i.e., say that (perm x y) and (dominates-some a x) implies
 ;; (dominates-some a y).  But, our pick a point method won't fire on terms of
 ;; the form (dominates-some a y), only on (not (dominates-some a y)).  Can
 ;; anything be done to make this work out?

 (local (defthm lemma
          (implies (and (bag::perm x y)
                        (not (dominates-some a x)))
                   (not (dominates-some a y)))))

 (defcong BAG::perm equal (dominates-some a x) 2))






;; Strictly Dominates Some
;;
;; Given some list a, and some list of lists x, we say that a "strictly
;; dominates some" list in x whenever there is some list b in x such that a
;; strictly dominates b.

(defund strictly-dominates-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (strictly-dominates a (car x))
          (strictly-dominates-some a (cdr x)))
    nil))

(defcong list::equiv equal (strictly-dominates-some a x) 1
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-type-1
  (implies (not (consp x))
           (equal (strictly-dominates-some a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-non-consp-two
  (implies (not (consp x))
           (not (strictly-dominates-some a x))))

(defthm strictly-dominates-some-non-consp-one
  (implies (not (consp a))
           (equal (strictly-dominates-some a x)
                  (not (no-conses x))))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-of-cons
  (equal (strictly-dominates-some a (cons b x))
         (or (strictly-dominates a b)
             (strictly-dominates-some a x)))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-of-append
  (equal (strictly-dominates-some a (append x y))
         (or (strictly-dominates-some a x)
             (strictly-dominates-some a y)))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm strictly-dominates-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (strictly-dominates a b))
           (strictly-dominates-some a x))
  :hints(("Goal" :in-theory (enable strictly-dominates-some))))

(defthm not-strictly-dominates-some-forward-to-not-strictly-dominates
  (implies (and (not (strictly-dominates-some b x))
                (memberp a x)) ;; a is a free variable
           (not (strictly-dominates b a)))
  :rule-classes :forward-chaining)

(encapsulate
 ()
 (encapsulate
  (((strictly-dominates-some-hyps) => *)
   ((strictly-dominates-some-path) => *)
   ((strictly-dominates-some-term) => *))
  (local (defun strictly-dominates-some-hyps () nil))
  (local (defun strictly-dominates-some-path () nil))
  (local (defun strictly-dominates-some-term () nil))
  (defthmd not-strictly-dominates-some-constraint
    (implies (and (strictly-dominates-some-hyps)
                  (list::memberp strictly-dominates-some-member
                                 (strictly-dominates-some-term)))
             (not (strictly-dominates (strictly-dominates-some-path)
                             strictly-dominates-some-member)))))

 (local (defund which-one? (a x)
          (if (endp x)
              nil
            (if (strictly-dominates a (car x))
                (car x)
              (which-one? a (cdr x))))))

 (local (defthm lemma
          (implies (strictly-dominates-some a x)
                   (and (memberp (which-one? a x) x)
                        (strictly-dominates a (which-one? a x))))
          :hints(("Goal" :in-theory (enable which-one?)))))

 (defthm not-strictly-dominates-some-by-membership-driver
   (implies (strictly-dominates-some-hyps)
            (not (strictly-dominates-some (strictly-dominates-some-path)
                                 (strictly-dominates-some-term))))
   :hints(("Goal"
           :use (:instance not-strictly-dominates-some-constraint
                           (strictly-dominates-some-member
                            (which-one? (strictly-dominates-some-path)
                                        (strictly-dominates-some-term)))))))

 (defadvice not-strictly-dominates-some-by-membership
   (implies (strictly-dominates-some-hyps)
            (not (strictly-dominates-some (strictly-dominates-some-path)
                                 (strictly-dominates-some-term))))
   :rule-classes (:pick-a-point
                  :driver not-strictly-dominates-some-by-membership-driver))
 )


(encapsulate
 ()
 ;; bzo - it would be nice if we could write this lemma in the "more natural"
 ;; way, i.e., say that (perm x y) and (dominates-some a x) implies
 ;; (dominates-some a y).  But, our pick a point method won't fire on terms of
 ;; the form (dominates-some a y), only on (not (dominates-some a y)).  Can
 ;; anything be done to make this work out?

 (local (defthm lemma
          (implies (and (bag::perm x y)
                        (not (strictly-dominates-some a x)))
                   (not (strictly-dominates-some a y)))))

 (defcong BAG::perm equal (strictly-dominates-some a x) 2))








;; Dominated By Some
;;
;; Given some list a, and some list of lists x, we say a is "dominated by some"
;; list in x whenever there is some list b in x such that b dominates a.

(defund dominated-by-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (dominates (car x) a)
          (dominated-by-some a (cdr x)))
    nil))

(defcong list::equiv equal (dominated-by-some a x) 1
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-type-1
  (implies (not (consp x))
           (equal (dominated-by-some a x) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-of-non-consp-one
  (implies (not (consp a))
           (equal (dominated-by-some a x)
                  (not (all-conses x))))
  :hints (("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-of-non-consp-two
  (implies (not (consp x))
           (equal (dominated-by-some a x)
                  nil)))

(defthm dominated-by-some-of-cons
  (equal (dominated-by-some a (cons b x))
         (or (dominates b a)
             (dominated-by-some a x)))
  :hints (("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-from-car
  (implies (and (consp x)
                (dominates (car x) a))
           (dominated-by-some a x)))

(defthm dominated-by-some-from-cdr
  (implies (dominated-by-some a (cdr x))
           (dominated-by-some a x)))

(defthm not-dominated-by-some-from-car/cdr
  (implies (and (consp x)
                (not (dominated-by-some a (cdr x)))
                (not (dominates (car x) a)))
           (not (dominated-by-some a x))))

(defthm not-dominated-by-some-from-weaker
  (implies (and (not (dominated-by-some a x))
                (dominates b a))
           (not (dominated-by-some b x)))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-of-append
  (equal (dominated-by-some a (append x y))
         (or (dominated-by-some a x)
             (dominated-by-some a y)))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (dominates b a))
           (dominated-by-some a x))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm not-dominated-by-some-forward-to-not-dominates
  (implies (and (not (dominated-by-some b x))
                (memberp a x)) ;; a is a free variable
           (not (dominates a b)))
  :rule-classes :forward-chaining)

(encapsulate
 ()
 (encapsulate
  (((dominated-by-some-hyps) => *)
   ((dominated-by-some-path) => *)
   ((dominated-by-some-term) => *))
  (local (defun dominated-by-some-hyps () nil))
  (local (defun dominated-by-some-path () nil))
  (local (defun dominated-by-some-term () nil))
  (defthmd not-dominated-by-some-constraint
    (implies (and (dominated-by-some-hyps)
                  (list::memberp dominated-by-some-member
                                 (dominated-by-some-term)))
             (not (dominates dominated-by-some-member
                             (dominated-by-some-path))))))

 (local (defund which-one? (a x)
          (if (endp x)
              nil
            (if (dominates (car x) a)
                (car x)
              (which-one? a (cdr x))))))

 (local (defthm lemma
          (implies (dominated-by-some a x)
                   (and (memberp (which-one? a x) x)
                        (dominates (which-one? a x) a)))
          :hints(("Goal" :in-theory (enable which-one?)))))

 (defthm not-dominated-by-some-by-membership-driver
   (implies (dominated-by-some-hyps)
            (not (dominated-by-some (dominated-by-some-path)
                                    (dominated-by-some-term))))
   :hints(("Goal"
           :use (:instance not-dominated-by-some-constraint
                           (dominated-by-some-member
                            (which-one? (dominated-by-some-path)
                                        (dominated-by-some-term)))))))

 (defadvice not-dominated-by-some-by-membership
   (implies (dominated-by-some-hyps)
            (not (dominated-by-some (dominated-by-some-path)
                                    (dominated-by-some-term))))
   :rule-classes (:pick-a-point
                  :driver not-dominated-by-some-by-membership-driver))
 )

(encapsulate
 ()

 (local (defthm lemma
          (implies (and (bag::perm x y)
                        (not (dominated-by-some a x)))
                   (not (dominated-by-some a y)))))

 (defcong BAG::perm equal (dominated-by-some a x) 2))








;; Strictly Dominated By Some
;;
;; Given some list a, and some list of lists x, we say a is "strictly dominated
;; by some" list in x whenever there is some list b in x such that b strictly
;; dominates a.

(defund strictly-dominated-by-some (a x)
  (declare (type t a x))
  (if (consp x)
      (or (strictly-dominates (car x) a)
          (strictly-dominated-by-some a (cdr x)))
    nil))

(defthm strictly-dominated-by-some-forward-to-dominated-by-some
  (implies (strictly-dominated-by-some a x)
           (dominated-by-some a x))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm not-dominated-by-some-forward-to-not-strictly-dominated-by-some
  (implies (not (dominated-by-some a x))
           (not (strictly-dominated-by-some a x)))
  :rule-classes :forward-chaining)

(defthm strictly-dominated-by-some-implies-dominated-by-some
  (implies (strictly-dominated-by-some a x)
           (dominated-by-some a x)))

(defcong list::equiv equal (strictly-dominated-by-some a x) 1
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-type-1
  (implies (not (consp x))
           (equal (strictly-dominated-by-some a x) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-type-2
  (implies (not (consp a))
           (equal (strictly-dominated-by-some a x) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-of-non-consp-one
  (implies (not (consp a))
           (equal (strictly-dominated-by-some a x)
                  nil))
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-of-non-consp-two
  (implies (not (consp x))
           (equal (strictly-dominated-by-some a x)
                  nil)))

(defthm strictly-dominated-by-some-of-cons
  (equal (strictly-dominated-by-some a (cons b x))
         (or (strictly-dominates b a)
             (strictly-dominated-by-some a x)))
  :hints (("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-from-car
  (implies (and (consp x)
                (strictly-dominates (car x) a))
           (strictly-dominated-by-some a x)))

(defthm strictly-dominated-by-some-from-cdr
  (implies (strictly-dominated-by-some a (cdr x))
           (strictly-dominated-by-some a x)))

(defthm not-strictly-dominated-by-some-from-car/cdr
  (implies (and (consp x)
                (not (strictly-dominated-by-some a (cdr x)))
                (not (strictly-dominates (car x) a)))
           (not (strictly-dominated-by-some a x))))

(defthm not-strictly-dominated-by-some-from-weaker
  (implies (and (not (dominated-by-some a x))
                (strictly-dominates b a))
           (not (strictly-dominated-by-some b x)))
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-of-append
  (equal (strictly-dominated-by-some a (append x y))
         (or (strictly-dominated-by-some a x)
             (strictly-dominated-by-some a y)))
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm strictly-dominated-by-some-by-membership
  (implies (and (memberp b x) ;; b is a free variable
                (strictly-dominates b a))
           (strictly-dominated-by-some a x))
  :hints(("Goal" :in-theory (enable strictly-dominated-by-some))))

(defthm not-strictly-dominated-by-some-forward-to-not-strictly-dominates
  (implies (and (not (strictly-dominated-by-some b x))
                (memberp a x)) ;; a is a free variable
           (not (strictly-dominates a b)))
  :rule-classes :forward-chaining)

(encapsulate
 ()
 (encapsulate
  (((strictly-dominated-by-some-hyps) => *)
   ((strictly-dominated-by-some-path) => *)
   ((strictly-dominated-by-some-term) => *))
  (local (defun strictly-dominated-by-some-hyps () nil))
  (local (defun strictly-dominated-by-some-path () nil))
  (local (defun strictly-dominated-by-some-term () nil))
  (defthmd not-strictly-dominated-by-some-constraint
    (implies (and (strictly-dominated-by-some-hyps)
                  (list::memberp strictly-dominated-by-some-member
                                 (strictly-dominated-by-some-term)))
             (not (strictly-dominates strictly-dominated-by-some-member
                                      (strictly-dominated-by-some-path))))))

 (local (defund which-one? (a x)
          (if (endp x)
              nil
            (if (strictly-dominates (car x) a)
                (car x)
              (which-one? a (cdr x))))))

 (local (defthm lemma
          (implies (strictly-dominated-by-some a x)
                   (and (memberp (which-one? a x) x)
                        (strictly-dominates (which-one? a x) a)))
          :hints(("Goal" :in-theory (enable which-one?)))))

 (defthm not-strictly-dominated-by-some-by-membership-driver
   (implies (strictly-dominated-by-some-hyps)
            (not (strictly-dominated-by-some (strictly-dominated-by-some-path)
                                    (strictly-dominated-by-some-term))))
   :hints(("Goal"
           :use (:instance not-strictly-dominated-by-some-constraint
                           (strictly-dominated-by-some-member
                            (which-one? (strictly-dominated-by-some-path)
                                        (strictly-dominated-by-some-term)))))))

 (defadvice not-strictly-dominated-by-some-by-membership
   (implies (strictly-dominated-by-some-hyps)
            (not (strictly-dominated-by-some (strictly-dominated-by-some-path)
                                    (strictly-dominated-by-some-term))))
   :rule-classes (:pick-a-point
                  :driver not-strictly-dominated-by-some-by-membership-driver))
 )

(encapsulate
 ()

 (local (defthm lemma
          (implies (and (bag::perm x y)
                        (not (strictly-dominated-by-some a x)))
                   (not (strictly-dominated-by-some a y)))))

 (defcong BAG::perm equal (strictly-dominated-by-some a x) 2))




;; First Dominator
;;
;; Given a list a, and a list of lists x, we define (first-dominator a x) as
;; the first list in x which dominates a, or nil otherwise.
;;
;; Historical note: first-dominator used to return 'no-dominator-found if it
;; reached the end of the list.  But, I changed it so that it instead returns
;; nil.  This has a couple of advantages.  For one, it yields better type
;; prescription rules, because nil is its own type whereas 'no-dominator-found
;; is not.  Furthermore, because nil dominates everything, the theorem
;; first-dominator-dominates is now a global truth with no hyps about whether a
;; is dominated-by-some or not.

(defund first-dominator (a x)
  (declare (type t a x))
  (if (atom x)
      nil
    (if (dominates (car x) a)
        (car x)
      (first-dominator a (cdr x)))))

(defcong list::equiv equal (first-dominator a x) 1
  :hints(("Goal" :in-theory (enable first-dominator))))

(defcong list::equiv equal (first-dominator a x) 2
  :hints(("Goal"
          :in-theory (enable first-dominator)
          :induct (list::len-len-induction x x-equiv))))

(defthm first-dominator-type-1
  (implies (not (consp x))
           (equal (first-dominator a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable first-dominator))))

(defthm first-dominator-of-non-consp-two
  (implies (not (consp x))
           (equal (first-dominator a x)
                  nil)))

(defthm first-dominator-dominates
  (dominates (first-dominator a x) a)
  :hints(("Goal" :in-theory (enable first-dominator))))


(defthm first-dominator-cons
  (equal (first-dominator a (cons b x))
         (if (dominates b a)
             b
           (first-dominator a x)))
  :hints(("Goal" :in-theory (enable first-dominator))))

(defthm first-dominator-of-cdr
  (implies (and (consp x)
                (not (dominates (car x) a)))
           (equal (first-dominator a (cdr x))
                  (first-dominator a x))))

(defthm first-dominator-when-car-dominates
  (implies (and (consp x)
                (dominates (car x) a))
           (equal (first-dominator a x)
                  (car x))))

;; It is almost true that (iff (first-dominator a x) (dominated-by-some a x)).
;; unfortunately, if nil is a member of x, then the first-dominator of a might
;; be nil, even though a is dominated by some.  Nevertheless, we have some
;; fairly powerful rules about this relationship:

(defthm first-dominator-implies-dominated-by-some
  (implies (first-dominator a x)
           (dominated-by-some a x))
  :hints(("Goal" :in-theory (enable dominated-by-some))))

(defthm dominated-by-some-when-first-dominator-nil
  (implies (not (first-dominator a x))
           (equal (dominated-by-some a x)
                  (memberp nil x)))
  :hints(("Goal" :in-theory (enable dominated-by-some))))


;; Another thing you might think is true is the following, but it isn't because
;; nil might occur near the front or near the end of a list that also contains
;; other dominators.
;;
;; (defcong BAG::perm iff (first-dominator a x) 2




;; bzo whats this for?

(defthm first-dominator-when-p-dominates-it-yuck
  (implies (and (dominates a b)
                (equal (first-dominator a x) b))
           (equal (list::equiv b a)
                  t)))









;; ----------------------------------------------------------------------------
;;
;;                                 Appendix A
;;
;;                       Pile of Dead Rules (bzo Remove Me)
;;
;; ----------------------------------------------------------------------------

;; jcd - removed this, redundant with dominates-of-non-consp-two

; (defthm dominates-of-nil-two
;   (equal (dominates p1 nil)
;          (not (consp p1)))
;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removed this, redundant with dominates-of-non-consp-one

; (defthm dominates-of-nil-one
;   (equal (dominates nil p2)
;          t)
;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removed this, redundant with congruence rule

; (defthm dominates-of-list-fix-one
;   (equal (dominates (list::fix p1) p2)
;          (dominates p1 p2))
;   :hints (("Goal" :in-theory (enable dominates))))

;; jcd - removed this, redundant with congruence rule

; (defthm dominates-of-list-fix-two
;   (equal (dominates p1 (list::fix p2))
;          (dominates p1 p2))
;   :hints (("Goal" :in-theory (enable dominates))))


;; jcd - removing this rule since it is never used anywhere and was disabled
;; to begin with.  It just doesn't seem like a good rule at all.
;;
;; (defthmd dominates-of-cdr-and-cdr-one
;;   (implies (and (equal (car p1) (car p2))
;;                 (consp p1)
;;                 (consp p2))
;;            (equal (dominates (cdr p1) (cdr p2))
;;                   (dominates p1 p2))))
;;
;; (theory-invariant (incompatible (:rewrite dominates-of-cdr-and-cdr-one)
;;                                 (:definition dominates)))

;; jcd - removed this rule.  in its place, i have proven the two rules
;; dominates-of-cons-one and dominates-of-cons-two, which are each stronger.
;;
;; (defthm dominates-of-cons-and-cons
;;   (equal (dominates (cons a p1) (cons b p2))
;;          (and (equal a b)
;;               (dominates p1 p2))))

;; jcd - these rules seem bad.  i understand that we want to be able to
;; reason about singletons and domination, but where does it end?  why not
;; write similar rules for doubles and triples?  I think at some point we
;; have to let destructor elimination do its job.
;;
;; of course, I could be wrong.  Maybe it's not too much to ask to have
;; special rules for singletons.  We'll see if anythign breaks.


;; ;make a -one version
;; ;make analogue for diverge?
;; (defthm dominates-of-singleton-two
;;   (implies (not (consp (cdr p2)))
;;            (equal (dominates p1 p2)
;;                   (if (consp p2)
;;                       (or (not (consp p1))
;;                           (and (equal (car p1) (car p2))
;;                                (not (consp (cdr p1)))))
;;                     (not (consp p1))))))

;; (defthm not-dominates-by-cadr-inequality
;;   (implies (and (consp p1)
;;                 (consp p2)
;;                 (consp (cdr p1))
;;                 (consp (cdr p2))
;;                 (not (equal (cadr p1) (cadr p2))))
;;            (not (dominates p1 p2))))



;; jcd - Removed this: redundant with dominated-by-some-of-non-consp-one.
;;
;; (defthm dominated-by-some-of-nil-one
;;   (equal (dominated-by-some nil paths)
;;          (contains-a-non-consp paths)))

;; jcd - Removed this: redundant with dominated-by-some-of-non-consp-two
;; and has-atom-of-non-consp
;;
;; (defthm dominated-by-some-of-nil-two
;;   (equal (dominated-by-some paths nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

; bzo - consider instead...
;(defthm dominates-of-nthcdr-and-nthcdr-from-dominates
;  (implies (dominates p1 p2)
;           (equal (dominates (nthcdr n1 p1) (nthcdr n2 p2))
;                  (equal (nfix n1)
;                         (nfix n2)))))

;; two-dominators-hack: given two dominators of p, one of the must dominate the
;; other

;; jcd - I have tried some variations of this rule.  I first tried case
;; splitting explicitly using
;;
;; (defthm two-dominators-hack
;;   (implies (and (dominates a p)
;;                 (dominates b p))
;;            (equal (dominates a b)
;;                   (if (dominates b a)
;;                       (list::equiv a b)
;;                     t))))
;;
;; But it turned out that this caused loops.  I also tried adding a case-split
;; around (not (dominates a b)) to make things more explicit.  That seemed to
;; work well, but sometimes misdirects proofs?
;;
;; (defthm two-dominators-hack
;;   (implies (and (dominates a p)
;;                 (dominates b p)
;;                 (case-split (not (dominates a b))))
;;            (dominates b a)))

; jcd - i don't like this rule, but i had to add it for a case
; where it came up.  can we make it more general?
;(defthm not-dominates-append-by-unequal-cars
;  (implies (and (consp path)
;                (not (equal (car path) (car path2))))
;           (not (dominates (append path rest)
;                           path2)))
;  :hints(("Goal" :in-theory (enable dominates))))
