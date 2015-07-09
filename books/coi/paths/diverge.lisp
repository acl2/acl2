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

;; diverge.lisp
;; Divergence relations for lists

(in-package "CPATH")
(include-book "dominates")
(include-book "../bags/basic")
(local (include-book "../util/iff"))



;; ----------------------------------------------------------------------------
;;
;;                                   PART 1
;;
;;                           The Diverge Relation
;;
;; ----------------------------------------------------------------------------

;; Diverge
;;
;; We say that list x diverges from list y whenever both (1) x is not a prefix
;; of y, and (2) y is not a prefix of x.  In other words, x and y may agree up
;; until some point, but eventually they "diverge" and go on their separate
;; ways.
;;
;; We could define diverge recursively, but instead we simply check that
;; neither list dominates the other.
;;
;; You might ask, why not just use dominates?  After all, diverge isn't adding
;; a whole lot.  I asked Dave about this, and he brought up an interesting
;; point: it's difficult to target rules upon the idea of diverge unless you
;; have a symbol for it.  Generally, diverge should be the normal form that we
;; try to rewrite terms into.
;;
;; bzo (jcd) - We use plural "dominates" but singular "diverge".  I think that
;; diverge should be changed to diverges.  Eric disagrees: He thinks it is
;; natural to say that "a dominates b" and also to say that "a and b diverge".
;; I prefer to say, "a diverges from b".  In any event, I will stick with
;; "diverge" for now.
;;
;; bzo (jcd) - Diverge is symmetric; should we prove each rule for both of the
;; symmetric cases?  Right now I am doing this, but perhaps it is redundant and
;; therefore bad to do this.  Maybe we should have OR's of each case in our
;; hypotheses instead?

(defund diverge (x y)
  (declare (type t x y))
  (and (not (dominates x y))
       (not (dominates y x))))

(defcong list::equiv equal (diverge x y) 1
  :hints(("Goal" :in-theory (enable diverge))))

(defcong list::equiv equal (diverge x y) 2
  :hints(("Goal" :in-theory (enable diverge))))

(defthm not-diverge-forward-to-dominates-cases
  (implies (not (diverge x y))
           (or (dominates x y)
               (dominates y x)))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable diverge))))


;; bzo (jcd) - I'm not sure why we have the above rule but not other forward
;; chaining rules.  For example, perhaps we want a rule that says if they do
;; diverge, then neither dominates.  And, if one dominates, then they do not
;; diverge.  I have added the following three forward chaining rules to go
;; along with this idea.  I'm not sure if this will break anything.

(defthm diverge-forward-to-non-domination
  (implies (diverge x y)
           (and (not (dominates x y))
                (not (dominates y x))))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable diverge))))

(defthm dominates-forward-to-non-divergence
  (implies (dominates x y)
           (and (not (diverge x y))
                (not (diverge y x))))
  :rule-classes :forward-chaining)

(defthm not-dominates-forward-to-diverge-cases
  (implies (not (dominates x y))
           (or (dominates y x)
               (diverge x y)))
  :rule-classes :forward-chaining)



(defthm diverge-type-1
  (implies (not (consp x))
           (equal (diverge x y) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-type-2
  (implies (not (consp y))
           (equal (diverge x y) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-of-non-consp-one
  (implies (not (consp x))
           (equal (diverge x y)
                  nil)))

(defthm diverge-of-non-consp-two
  (implies (not (consp y))
           (equal (diverge x y)
                  nil)))

(defthm diverge-irreflexive
  (not (diverge x x))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-symmetric
  (equal (diverge x y)
         (diverge y x))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-commute-fwd
  (implies
   (diverge x y)
   (diverge y x))
  :rule-classes (:forward-chaining))

(defthm not-diverge-commute-fwd
  (implies
   (not (diverge x y))
   (not (diverge y x)))
  :rule-classes (:forward-chaining))

(defthm diverge-of-cons-one
  (equal (diverge (cons a x) y)
         (and (consp y)
              (or (not (equal a (car y)))
                  (diverge x (cdr y)))))
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-of-cons-two
  (equal (diverge x (cons a y))
         (and (consp x)
              (or (not (equal a (car x)))
                  (diverge y (cdr x))))))

(defthm diverge-of-append-self-one
  (equal (diverge (append x y) x)
         nil)
  :hints (("Goal" :in-theory (enable append))))

(defthm diverge-of-append-self-two
  (equal (diverge x (append x y))
         nil)
  :hints (("Goal" :in-theory (enable append))))



;; bzo (jcd) - Originally we had all of the following rules to allow ourselves
;; to backchain between diverge and dominates.  I have dropped all of these in
;; favor of the extra forward chaining rules above, but this may break things.

;; (defthm not-diverge-when-dominates-one
;;   (implies (dominates x y)
;;            (not (diverge x y)))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; (defthm not-diverge-when-dominates-two
;;   (implies (dominates y x)
;;            (not (diverge x y)))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; (defthm not-dominates-when-diverge-one
;;   (implies (diverge x y)
;;            (not (dominates x y))))

;; (defthm not-dominates-when-diverge-two
;;   (implies (diverge x y)
;;            (not (dominates y x))))

(defthm two-dominators-cannot-diverge
  (implies (and (dominates x z)
                (dominates y z))
           (not (diverge x y)))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-when-diverge-with-dominator-one
  (implies (and (diverge x z)
                (dominates z y))
           (diverge x y))
  :hints (("Goal" :in-theory (enable diverge))))

(defthm diverge-when-diverge-with-dominator-one-alt
  (implies (and (dominates z y)
                (diverge x z))
           (diverge x y)))

(defthm diverge-when-diverge-with-dominator-two
  (implies (and (diverge y z)
                (dominates z x))
           (diverge x y))
  :hints(("Goal" :in-theory (enable diverge))))

(defthm diverge-when-diverge-with-dominator-two-alt
  (implies (and (dominates z x)
                (diverge y z))
           (diverge x y)))


;; jcd - the following theorem was actually provided as a really bizarre fact
;; about all-diverge.  Changing it to be a property about diverge itself seems
;; to be a much better approach:

(defthm diverge-implies-unequal-extensions
  (implies (diverge x y)
           (equal (equal (append x a)
                         (append y b))
                  nil))
  :hints(("Goal" :in-theory (enable diverge
                                    dominates
                                    ))))





;; ----------------------------------------------------------------------------
;;
;;                                   PART 2
;;
;;                  Extending the Diverge Relation to Lists
;;
;; ----------------------------------------------------------------------------


;; diverges-from-all
;;
;; Given a list a, and a list of lists x, we say that a diverges-from-all x if
;; every list b in x satisfies (diverge a b).
;;
;; Note (jcd): We could have just defined diverges-from-all nonrecursively as
;; in the redefinition theorem below.  Perhaps having both definitions around
;; will be convenient?
;;
;; Note (jcd): Most of the theorems below can be proven with either definition.
;; We tend to use the nonrecursive definition, because it gives our theories
;; about dominates-some and dominated-by-some a small workout.

(defund diverges-from-all (a x)
  (declare (type t a x))
  (if (consp x)
      (and (diverge a (car x))
           (diverges-from-all a (cdr x)))
    t))

(defthmd diverges-from-all-redefinition
  (equal (diverges-from-all p paths)
         (and (not (dominated-by-some p paths))
              (not (dominates-some p paths))))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable diverges-from-all))))

(theory-invariant (incompatible (:definition diverges-from-all)
                                (:definition diverges-from-all-redefinition)))

(defcong list::equiv equal (diverges-from-all a x) 1
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defcong bag::perm equal (diverges-from-all a x) 2
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-type-1
  (implies (not (consp x))
           (equal (diverges-from-all a x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-type-2
  (implies (and (consp x)
                (not (consp a)))
           (equal (diverges-from-all a x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-of-non-consp-one
  (implies (not (consp a))
           (equal (diverges-from-all a x)
                  (not (consp x)))))

(defthm diverges-from-all-of-non-consp-two
  (implies (not (consp x))
           (diverges-from-all a x)))

(defthm diverges-from-all-of-cons
  (equal (diverges-from-all a (cons b x))
         (and (diverge a b)
              (diverges-from-all a x)))
  :hints (("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-of-cdr
  (implies (diverges-from-all a x)
           (diverges-from-all a (cdr x))))

(defthm diverges-of-cdr-by-diverges-from-all
  (implies (diverges-from-all a x)
           (equal (diverge a (car x))
                  (consp x))))

(defthm diverges-from-all-of-append
  (equal (diverges-from-all a (append x y))
         (and (diverges-from-all a x)
              (diverges-from-all a y)))
  :hints (("Goal" :in-theory (enable append))))



;; We add a pick a point method of proving divergence from all.  So, to prove
;; (diverge-from-all a x), all you have to do is prove that (diverge a b) for
;; any arbitrary b satisfying (memberp b x).  See the advisor library for
;; more information about this approach.

(encapsulate
 ()

 (encapsulate
  (((diverges-from-all-hyps) => *)
   ((diverges-from-all-path) => *)
   ((diverges-from-all-list) => *))
  (local (defun diverges-from-all-hyps () nil))
  (local (defun diverges-from-all-path () nil))
  (local (defun diverges-from-all-list () nil))
  (defthmd diverges-from-all-constraint
    (implies (and (diverges-from-all-hyps)
                  (memberp diverges-from-all-member
                                (diverges-from-all-list)))
             (diverge diverges-from-all-member
                      (diverges-from-all-path)))))

 (local (defund badguy (a x)
          (if (endp x)
              nil
            (if (diverge a (car x))
                (badguy a (cdr x))
              (car x)))))

 (local (defthm badguy-witness
          (implies (not (diverges-from-all a x))
                   (and (memberp (badguy a x) x)
                        (not (diverge a (badguy a x)))))
          :hints(("Goal" :in-theory (enable badguy)))))

 (defthm diverges-from-all-by-membership-driver
   (implies (diverges-from-all-hyps)
            (diverges-from-all (diverges-from-all-path)
                               (diverges-from-all-list)))
   :rule-classes nil
   :hints(("Goal"
           :use (:instance diverges-from-all-constraint
                           (diverges-from-all-member
                            (badguy (diverges-from-all-path)
                                    (diverges-from-all-list)))))))

 (defadvice diverges-from-all-by-membership
   (implies (diverges-from-all-hyps)
            (diverges-from-all (diverges-from-all-path)
                               (diverges-from-all-list)))
   :rule-classes (:pick-a-point
                  :driver diverges-from-all-by-membership-driver))
 )



;; To effectively reason about diverge-from-all through membership, we need to
;; know that whenever (memberp a x) and (diverges-from-all b x), then
;; (diverge a b) and also (diverge b a).  To cover the free variable matching
;; alternatives, there are actually four different versions of these theorems
;; (Note that x is a free variable in all of these rules.)

(defthm diverge-when-memberp-and-diverges-from-all-one
  (implies (and (memberp a x)
                (diverges-from-all b x))
           (diverge a b))
  :hints (("Goal" :in-theory( enable diverges-from-all-redefinition))))

(defthm diverge-when-memberp-and-diverges-from-all-two
  (implies (and (diverges-from-all b x)
                (memberp a x))
           (diverge a b)))

(defthm diverge-when-memberp-and-diverges-from-all-three
  (implies (and (memberp b x)
                (diverges-from-all a x))
           (diverge a b))
  :hints (("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverge-when-memberp-and-diverges-from-all-four
   (implies (and (diverges-from-all a x)
                 (memberp b x))
            (diverge a b)))

(defthm diverges-from-all-forward-to-diverge
  (implies (and (diverges-from-all a x)
                (memberp b x))
           (and (diverge a b)
                (diverge b a)))
  :rule-classes :forward-chaining)




;; We now use our membership strategy to prove divergence from all of subbags.
;; Again because of free variable matching, there are two versions of this rule
;; (Note that y is a free variable.)

(defthm diverges-from-all-by-subbagp-one
  (implies (and (diverges-from-all a y)
                (bag::subbagp x y))
           (diverges-from-all a x)))

(defthm diverges-from-all-by-subbagp-two
  (implies (and (bag::subbagp x y)
                (diverges-from-all a y))
           (diverges-from-all a x)))



;; There are probably other nice facts we could prove about diverges-from-all
;; especially as it relates to the list and bag functions.  For now we will
;; just prove these:

(defthm diverges-from-all-of-nthcdr
  (implies (diverges-from-all a x)
           (diverges-from-all a (nthcdr n x))))

(defthm diverges-from-all-of-firstn
  (implies (diverges-from-all a x)
           (diverges-from-all a (firstn n x))))

(defthm diverges-from-all-of-remove-1
  (implies (diverges-from-all a x)
           (diverges-from-all a (bag::remove-1 b x))))

(defthm diverges-from-all-of-remove-all
  (implies (diverges-from-all a x)
           (diverges-from-all a (bag::remove-all b x))))

(defthm diverges-from-all-when-dominated
  (implies (and (dominates a b) ; a is a free var
                (diverges-from-all a x))
           (diverges-from-all b x)))



;; Forward chaining to dominated-by-some and dominates-some

(defthm diverge-from-all-forward
  (implies (diverges-from-all a x)
           (and (not (dominated-by-some a x))
                (not (dominates-some a x))))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

(defthm diverges-from-all-when-no-domination
  (implies (and (not (dominated-by-some a x))
                (not (dominates-some a x)))
           (diverges-from-all a x))
  :hints(("Goal" :in-theory (enable diverges-from-all-redefinition))))

;; (defthm not-dominated-by-some-when-diverges-from-all
;;   (implies (diverges-from-all p paths)
;;            (not (dominated-by-some p paths)))
;;   :hints (("Goal" :in-theory (enable dominated-by-some))))

;; ;bzo drop? other rules handle this?
;; (defthm not-dominated-by-some
;;   (implies (and (diverges-from-all a x) ; a is a free variable
;;                 (dominates b a))
;;            (not (dominated-by-some b x))))

;; (defthm not-strictly-dominated-by-some-when-diverges-from-all
;;   (implies (diverges-from-all p paths)
;;            (not (strictly-dominated-by-some p paths))))

;; (defthm diverges-from-when-not-strictly-dominated-by-some-and-not-dominates-some
;;   (implies (and (not (strictly-dominated-by-some p paths))
;;                 (not (dominates-some p paths)))
;;            (diverges-from-all p paths)))

;; (defthm diverges-from-all-when-no-domination-alt
;;   (implies (and (not (strictly-dominated-by-some p paths))
;;                 (not (dominates-some p paths)))
;;            (diverges-from-all p paths)))




;; ----------------------------------------------------------------------------
;;
;;                                   PART 3
;;
;;                     The All-Diverge-From-All Relation
;;
;; ----------------------------------------------------------------------------

;; Given x and y, both list of lists, we say that (all-diverge-from-all x y)
;; whenever every path a in x and every path b in y satisfy (diverge x y).

(defund all-diverge-from-all (x y)
  (declare (type t x y))
  (if (consp x)
      (and (diverges-from-all (car x) y)
           (all-diverge-from-all (cdr x) y))
    t))


(encapsulate
 ()

 ;; Because all-diverge-from-all is a pretty complicated function, I much
 ;; prefer to view it in terms of membership rather than in its recursive form.
 ;; The pick-a-point setup for it is a little complicated: we suppose as our
 ;; constraint that for every e1 in x and every e2 in y, e1 and e2 diverge.  We
 ;; will then show that this means x and y satisfy all-diverge-from-all.

 (encapsulate
  (((all-diverge-from-all-hyps) => *)
   ((all-diverge-from-all-one) => *)
   ((all-diverge-from-all-two) => *))
  (local (defun all-diverge-from-all-hyps () nil))
  (local (defun all-diverge-from-all-one () nil))
  (local (defun all-diverge-from-all-two () nil))
  (defthm all-diverge-from-all-constraint
    (implies (and (all-diverge-from-all-hyps)
                  (memberp all-diverge-from-all-e1 (all-diverge-from-all-one))
                  (memberp all-diverge-from-all-e2 (all-diverge-from-all-two)))
             (diverge all-diverge-from-all-e1
                      all-diverge-from-all-e2))
    :rule-classes nil))

 ;; Proving that this constraint is sufficient is a little complicated.  We
 ;; actually need two badguys!  dfa-badguy is a badguy for diverges-from-all,
 ;; and returns whichever element of x a diverges from.

 (local (defund dfa-badguy (a x)
          (if (endp x)
              nil
            (if (diverge a (car x))
                (dfa-badguy a (cdr x))
              (car x)))))

 (local (defthm dfa-badguy-witness
          (implies (not (diverges-from-all a x))
                   (and (memberp (dfa-badguy a x) x)
                        (not (diverge a (dfa-badguy a x)))))
          :hints(("Goal" :in-theory (enable dfa-badguy)))))

 ;; We also have a second badguy for all-diverge-from-all, which returns
 ;; the first list in x that doesn't satisfy diverges-from-all with y.

 (local (defund adfa-badguy (x y)
          (if (endp x)
              nil
            (if (diverges-from-all (car x) y)
                (adfa-badguy (cdr x) y)
              (car x)))))

 (local (defthm adfa-badguy-witness
          (implies (not (all-diverge-from-all x y))
                   (and (memberp (adfa-badguy x y) x)
                        (not (diverges-from-all (adfa-badguy x y) y))))
          :hints(("Goal" :in-theory (enable adfa-badguy
                                            all-diverge-from-all
                                            )))))

 ;; Now to prove our theorem, we need to set up e1 to be the member of x that
 ;; doesn't satisfy diverges-from-all y.  Then, we set up e2 to be the member
 ;; of y that e1 doesn't diverge from.  Everything else falls out nicely after
 ;; appealing to our constraint.

 (defthm all-diverge-from-all-by-membership-driver
   (implies (all-diverge-from-all-hyps)
            (all-diverge-from-all (all-diverge-from-all-one)
                                  (all-diverge-from-all-two)))
   :hints(("Goal"
           :use ((:instance all-diverge-from-all-constraint
                            (all-diverge-from-all-e1
                             (adfa-badguy (all-diverge-from-all-one)
                                          (all-diverge-from-all-two)))
                            (all-diverge-from-all-e2
                             (dfa-badguy (adfa-badguy
                                          (all-diverge-from-all-one)
                                          (all-diverge-from-all-two))
                                         (all-diverge-from-all-two))))))))

 ;; And we go ahead and tell Adviser to automate this strategy.

 (defadvice all-diverge-from-all-by-membership
   (implies (all-diverge-from-all-hyps)
            (all-diverge-from-all (all-diverge-from-all-one)
                                  (all-diverge-from-all-two)))
   :rule-classes (:pick-a-point
                  :driver all-diverge-from-all-by-membership-driver))
)


;; To get any use out of the strategy, we have to be able to reason about
;; membership in all-diverge-from-all.  The following are crucial lemmas that
;; show how arbitrary members diverge when x and y satisfy
;; all-diverge-from-all.

(defthm diverge-when-members-of-all-diverge-from-all-one
  (implies (and (all-diverge-from-all x y) ;; x and y are free
                (memberp a x)
                (memberp b y))
           (diverge a b))
  :hints(("Goal" :in-theory (enable all-diverge-from-all))))

(defthm diverge-when-members-of-all-diverge-from-all-two
  (implies (and (all-diverge-from-all x y) ;; x and y are free
                (memberp a x)
                (memberp b y))
           (diverge b a)))



;; Here are some mundane theorems about all-diverge-from-all.  We could prove
;; these with the definition of all-diverge-from-all, but we prefer to try out
;; our membership strategy some more.

(defthm all-diverge-from-all-type-1
  (implies (not (consp x))
           (equal (all-diverge-from-all x y) t))
  :rule-classes :type-prescription)

(defthm all-diverge-from-all-type-2
  (implies (not (consp y))
           (equal (all-diverge-from-all x y) t))
  :rule-classes :type-prescription)

(defthm all-diverge-from-all-of-non-consp-one
  (implies (not (consp x))
           (all-diverge-from-all x y)))

(defthm all-diverge-from-all-of-non-consp-two
  (implies (not (consp y))
           (all-diverge-from-all x y)))



;; We'll now show that all-diverge-from-all is commutative.  This is a pretty
;; straightforward membership argument now.  I've left the original proofs in
;; comments below so that you can see the improvement:
;;
;; ;bzo generalize the car to any memberp?
;; (defthm not-all-diverge-from-all-when-not-diverges-from-all-of-car
;;   (implies (not (diverges-from-all (car paths1) paths2))
;;            (equal (all-diverge-from-all paths1 paths2)
;;                   (not (consp paths1))))
;;   :hints (("Goal" :in-theory (enable all-diverge-from-all))))
;;
;; (defthm all-diverge-from-all-alternate-definition
;;   (implies (consp paths2) ;this hyp helps prevent this rule from looping
;;            (equal (all-diverge-from-all paths1 paths2)
;;                   (and (all-diverge-from-all paths1 (cdr paths2))
;;                        (diverges-from-all (car paths2) paths1))))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand ( (ALL-DIVERGE-FROM-ALL PATHS2 PATHS1))
;;            :in-theory (enable all-diverge-from-all))) )
;;
;; (defthm all-diverge-from-all-commutative
;;   (equal (all-diverge-from-all paths1 paths2)
;;          (all-diverge-from-all paths2 paths1))
;;   :otf-flg t
;;   :hints (("Goal" :expand ( (ALL-DIVERGE-FROM-ALL PATHS2 PATHS1))
;;            :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable all-diverge-from-all))) )

(encapsulate
 ()

 (local (defthm lemma
          (implies (all-diverge-from-all x y)
                   (all-diverge-from-all y x))))

 (defthm all-diverge-from-all-symmetric
   (equal (all-diverge-from-all x y)
          (all-diverge-from-all y x)))

)


;; I noticed that the original proof of symmetry had a nice lemma about car,
;; and a note that it could be generalized.  I've generalized it here to any
;; arbitrary member, and proven the symmetric version as well.

(defthm all-diverge-from-all-when-bad-member-one
  (implies (and (not (diverges-from-all a y))
                (memberp a x))
           (equal (all-diverge-from-all x y)
                  (not (consp y))))
   :hints (("Goal" :in-theory (enable all-diverge-from-all))))

(defthm all-diverge-from-all-when-bad-member-two
  (implies (and (not (diverges-from-all a x))
                (memberp a y))
           (equal (all-diverge-from-all x y)
                  (not (consp x))))
  :hints(("Goal"
          :in-theory (disable all-diverge-from-all-symmetric)
          :use (:instance all-diverge-from-all-symmetric
                          (x y) (y x)))))


;; We can prove some nice rewrites about how all-diverge-from-all distributes
;; over cons.  We'll do both symmetric cases below.  These are easier to prove
;; from the definition and symmetry than by membership.

(defthm all-diverge-from-all-of-cons-one
  (equal (all-diverge-from-all (cons a x) y)
         (and (diverges-from-all a y)
              (all-diverge-from-all x y)))
  :hints(("Goal"
          :use (:instance all-diverge-from-all
                          (x (cons a x))
                          (y y)))))

(defthm all-diverge-from-all-of-cons-two
  (equal (all-diverge-from-all x (cons a y))
         (and (diverges-from-all a x)
              (all-diverge-from-all x y)))
  :hints(("Goal"
          :in-theory (disable all-diverge-from-all-symmetric)
          :use ((:instance all-diverge-from-all-symmetric
                           (x (cons a y)) (y x))
                (:instance all-diverge-from-all-symmetric
                           (x y) (y x))))))



;; Here are several easy membership-based proofs of some basic properties of
;; all-diverge-from-all.

(defthm all-diverge-from-all-of-cdr-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (cdr x) y)))

(defthm all-diverge-from-all-of-cdr-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (cdr y))))

(defthm all-diverge-from-all-of-firstn-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (firstn n x) y)))

(defthm all-diverge-from-all-of-firstn-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (firstn n y))))

(defthm all-diverge-from-all-of-nthcdr-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (nthcdr n x) y)))

(defthm all-diverge-from-all-of-nthcdr-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (nthcdr n y))))

(defthm all-diverge-from-all-of-remove-1-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (bag::remove-1 a x) y)))

(defthm all-diverge-from-all-of-remove-1-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (bag::remove-1 a y))))

(defthm all-diverge-from-all-of-remove-all-one
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all (bag::remove-all a x) y)))

(defthm all-diverge-from-all-of-remove-all-two
  (implies (all-diverge-from-all x y)
           (all-diverge-from-all x (bag::remove-all a y))))

(defthm all-diverge-from-all-when-subbag-one
  (implies (and (all-diverge-from-all y z) ;; y is a free variable
                (bag::subbagp x y))
           (all-diverge-from-all x z)))

(defthm all-diverge-from-all-when-subbag-two
  (implies (and (all-diverge-from-all y z) ;; z is a free variable
                (bag::subbagp x z))
           (all-diverge-from-all y x)))

(defcong bag::perm equal (all-diverge-from-all x y) 1)
(defcong bag::perm equal (all-diverge-from-all x y) 2)


;; ----------------------------------------------------------------------------
;;
;;                                   PART 3
;;
;;                           The All-Diverge Relation
;;
;; ----------------------------------------------------------------------------

;; Given x, a list of lists, we say that (all-diverge x) if and only if every
;; member of x diverges from every other member in x.

(defund all-diverge (x)
  (declare (type t x))
  (if (consp x)
      (and (diverges-from-all (car x) (cdr x))
           (all-diverge (cdr x)))
    t))

(defthm all-diverge-type-1
  (implies (not (consp x))
           (equal (all-diverge x) t))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable all-diverge))))

(defthm all-diverge-of-non-consp
  (implies (not (consp x))
           (equal (all-diverge x) t)))

(defthm all-diverge-of-cons
  (equal (all-diverge (cons a x))
         (and (diverges-from-all a x)
              (all-diverge x)))
  :hints(("Goal" :in-theory (enable all-diverge))))



;; An early observation we can make is that, if there are any duplicate
;; elements in the list, then clearly it will not satisfy all-diverge (since,
;; after all, diverge is irreflexive).  This isn't entirely straightforward to
;; prove, but it's not that hard:

(encapsulate
 ()

 (local (defun which? (x)
          (if (endp x)
              nil
            (if (memberp (car x) (cdr x))
                (car x)
              (which? (cdr x))))))

 (local (defthm lemma
          (implies (not (bag::unique x))
                   (and (memberp (which? x) x)
                        (memberp (which? x) (bag::remove-1 (which? x) x))))))

 (local (defthmd lemma2
          (implies (and (memberp a x)
                        (memberp b (bag::remove-1 a x))
                        (not (diverge a b)))
                   (not (all-diverge x)))
          :hints(("Goal" :in-theory (enable all-diverge)))))

 (defthm unique-when-all-diverge
   (implies (all-diverge x)
            (bag::unique x))
   :hints(("Goal"
           :in-theory (disable bag::memberp-of-remove-1-same)
           :use (:instance lemma2
                           (a (which? x))
                           (b (which? x))
                           (x x)))))
)



;; We will now create a membership approach to reasoning about all-diverge.
;; This is not as straightforward as for other functions, becuase of the need
;; to pick two "different" members of x.  Essentially, we would like to say
;; that (all-diverge x) is true exactly when:
;;
;;   1.  (bag::unique x), and
;;   2.  Forall a,b in x with a != b, (diverge a b)
;;
;; Fortunately, we can capture these constraints with a properly crafted
;; encapsulate, and by doing so, we can apply our pick a point reduction to
;; (all-diverge x).

(encapsulate
 ()

 (encapsulate
  (((all-diverge-hyps) => *)
   ((all-diverge-term) => *))
  (local (defun all-diverge-hyps () nil))
  (local (defun all-diverge-term () nil))
  (defthm all-diverge-constraint-unique
    (implies (all-diverge-hyps)
             (bag::unique (all-diverge-term)))
    :rule-classes nil)
  (defthm all-diverge-constraint-membership
    (implies (and (all-diverge-hyps)
                  (memberp all-diverge-member-a (all-diverge-term))
                  (memberp all-diverge-member-b (all-diverge-term))
                  (not (equal all-diverge-member-a all-diverge-member-b)))
             (diverge all-diverge-member-a all-diverge-member-b))
    :rule-classes nil))

 (local (defund dfa-badguy (a x)
          (if (endp x)
              nil
            (if (diverge a (car x))
                (dfa-badguy a (cdr x))
              (car x)))))

 (local (defthmd dfa-badguy-works
          (implies (not (diverges-from-all a x))
                   (and (memberp (dfa-badguy a x) x)
                        (not (diverge a (dfa-badguy a x)))))
          :hints(("Goal" :in-theory (enable dfa-badguy)))))

 (local (defund adfa-badguy (x)
          (if (endp x)
              nil
            (if (diverges-from-all (car x) (cdr x))
                (adfa-badguy (cdr x))
              (car x)))))

 (local (defthmd adfa-badguy-works
          (implies (not (all-diverge x))
                   (and (memberp (adfa-badguy x) x)
                        (not (diverges-from-all
                              (adfa-badguy x)
                              (bag::remove-1 (adfa-badguy x) x)))))
          :hints(("Goal" :in-theory (enable adfa-badguy)))))

 ;; These hints look a little extreme.  Basically the proof is the following:
 ;; By our constraints, we can assume that (all-diverge-term) satisfies both
 ;; bag::unique and our property that any two members which are not equal must
 ;; diverge.  Suppose towards contradiction that this list does not satisfy
 ;; (all-diverge (all-diverge-term)).
 ;;
 ;; Let (all-diverge-term) be "x".  Since x does not satisfy all-diverge, by
 ;; the theorem adfa-badguy-works, we know that (adfa-badguy x) is a member of
 ;; x.  Call this member "a".  By the same theorem, we also know that the
 ;; following is true: (not (diverges-from-all a (bag::remove-1 a x))).
 ;;
 ;; Since (not (diverges-from-all a (bag::remove-1 a x))), we know by the
 ;; theorem dfa-badguy-works that (dfa-badguy a (bag::remove-1 a x)) is a
 ;; member of (bag::remove-1 a x).  Call this member "b".  From the same
 ;; theorem, we also know that the following is true: (not (diverge a b)).
 ;;
 ;; Finally, note that since we have assumed (bag::unique x) and we know that
 ;; (memberp b (bag::remove-1 a x)), it must be the case that a != b and also
 ;; we know that b is a member of x.
 ;;
 ;; Well now, we are set up to show our contradiction.  We know that a and
 ;; b are both members of x, they are not equal, and they do not diverge.  But
 ;; this is a direct violation of our second constraint!  QED.

 (defthm all-diverge-by-membership-driver
   (implies (all-diverge-hyps)
            (all-diverge (all-diverge-term)))
   :rule-classes nil
   :hints(("Goal"
           :use ((:instance all-diverge-constraint-unique)
                 (:instance all-diverge-constraint-membership
                            (all-diverge-member-a
                             (adfa-badguy (all-diverge-term)))
                            (all-diverge-member-b
                             (dfa-badguy
                              (adfa-badguy (all-diverge-term))
                              (bag::remove-1
                               (adfa-badguy (all-diverge-term))
                               (all-diverge-term)))))
                 (:instance adfa-badguy-works
                            (x (all-diverge-term)))
                 (:instance dfa-badguy-works
                            (a (adfa-badguy (all-diverge-term)))
                            (x (bag::remove-1 (adfa-badguy (all-diverge-term))
                                              (all-diverge-term))))))))

 (defadvice all-diverge-by-membership
   (implies (all-diverge-hyps)
            (all-diverge (all-diverge-term)))
   :rule-classes (:pick-a-point :driver all-diverge-by-membership-driver))
 )


;; To effectively use the all-diverge-by-membership approach, we need to be
;; able to know that arbitrary members of a list which satisfies all-diverge
;; must themselves diverge.  I was quite surprised that this wasn't already a
;; theorem -- it seems like "the main fact" about all-diverge.

(defthm diverge-when-members-of-all-diverge
  (implies (and (all-diverge x) ;; x is a free variable
                (memberp a x)
                (memberp b x))
           (equal (diverge a b)
                  (not (equal a b))))
  :hints(("Goal" :in-theory (enable all-diverge))))


;; Given our membership strategy, we can now painlessly prove a number of nice
;; rewrite rules about all-diverge.

(defthm all-diverge-of-cdr
  (implies (all-diverge x)
           (all-diverge (cdr x))))

(defthm all-diverge-of-remove-1
  (implies (all-diverge x)
           (all-diverge (bag::remove-1 a x))))

(defthm all-diverge-of-remove-all
  (implies (all-diverge x)
           (all-diverge (bag::remove-all a x))))

(defthm all-diverge-of-nthcdr
  (implies (all-diverge x)
           (all-diverge (nthcdr n x))))

(defthm all-diverge-of-firstn
  (implies (all-diverge x)
           (all-diverge (firstn n x))))

(defthm all-diverge-when-subbag
  (implies (and (all-diverge y)
                (bag::subbagp x y))
           (all-diverge x)))

(defcong bag::perm equal (all-diverge x) 1)





;; jcd - Removing.  This is redundant with diverges-from-all-of-non-consp-one.
;;
;; (defthm diverges-from-all-of-nil
;;   (equal (diverges-from-all nil x)
;;          (not (consp x)))
;;   :hints (("Goal" :in-theory (enable diverges-from-all))))

;; jcd - We replaced this rule with diverge-of-cons-one and
;; diverge-of-cons-two, each of which is stronger.
;;
;; (defthm diverge-of-cons-and-cons
;;   (equal (diverge (cons a p1) (cons b p2))
;;          (or (not (equal a b))
;;              (diverge p1 p2)))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - removed this, is it legitimate to do so?  is it needed anywhere?
;;
;; (defthm diverges-from-all-when-diverges-from-all-of-cdr
;;   (implies (diverges-from-all p (cdr paths))
;;            (equal (diverges-from-all p paths)
;;                   (if (consp paths)
;;                       (diverge p (car paths))
;;                     t))))

;; jcd - Removing this -- I think this is now handled by adding the rule
;; diverge-when-diverge-with-dominator-two and its alt form.
;;
;; (defthm diverge-when-dominate-divergent
;;   (implies (and (dominates q p)   ;q is a free var
;;                 (dominates q2 p2) ;q2 is a free var
;;                 (diverge q q2))
;;            (diverge p p2))
;;   :hints (("Goal" :in-theory (enable diverge))))

;; jcd - This is a really bizarre theorem, and I am getting rid of it.  I have
;; proven a similar rule above but for "diverge" itself, an this is a pretty
;; easy consequence of it.
;;
;; (defthm all-diverge-implies-unequal-extensions
;;   (implies (all-diverge (list x y))
;;            (not (equal (append x a)
;;                        (append y b)))))
