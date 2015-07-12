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

(in-package "CPATH")
(local (include-book "../util/iff"))

;;
;; The new direction for path reasoning.
;;
;; We define a very strong notion of sets of paths that allows us to fix a set
;; to the most dominant members.  It also has the nice set properties of
;; ignoring duplicates and sorting elements.
;;
;; I think this notion will play well with such operations as (cp-set set st1
;; st2) in which dominating paths take precidence.  Hopefully it will work
;; well with dtrees/gwv as well.

(include-book "path")
(local (in-theory (enable DOMINATED-BY-SOME)))

;; dominated-by-some     <-> memberp
;; all-dominated-by-some <-> subsetp

(defthm dominated-by-some-from-dominated-by-some-all-dominated-by-some
  (implies
   (and
    (all-dominated-by-some x y)
    (dominated-by-some path x))
   (dominated-by-some path y))
  :rule-classes (:rewrite :forward-chaining))

(defthm all-dominated-by-some-chaining-1
  (implies
   (and
    (all-dominated-by-some x y)
    (all-dominated-by-some y z))
   (all-dominated-by-some x z))
  :rule-classes (:rewrite :forward-chaining))

(defthm all-dominated-by-some-chaining-2
  (implies
   (and
    (all-dominated-by-some y z)
    (all-dominated-by-some x y))
   (all-dominated-by-some x z))
  :rule-classes (:rewrite :forward-chaining))

(local (in-theory (enable strictly-dominated-by-some)))

(defthm strictly-dominates-from-dominates-strictly-dominates-1
  (implies
   (and
    (strictly-dominates x path)
    (dominates a x))
   (strictly-dominates a path))
  :hints (("Goal" :in-theory (enable strictly-dominates)))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominates-from-dominates-strictly-dominates-2
  (implies
   (and
    (dominates a x)
    (strictly-dominates x path))
   (strictly-dominates a path))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominates-from-strictly-dominates-dominates-1
  (implies
   (and
    (dominates x path)
    (strictly-dominates a x))
   (strictly-dominates a path))
  :hints (("Goal" :in-theory (enable strictly-dominates)))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominates-from-strictly-dominates-dominates-2
  (implies
   (and
    (strictly-dominates a x)
    (dominates x path))
   (strictly-dominates a path))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominated-by-some-from-strictly-dominated-dominated-by-some-1
  (implies
   (and
    (strictly-dominates x path)
    (dominated-by-some x list))
   (strictly-dominated-by-some path list))
  :rule-classes (:forward-chaining :rewrite)
  :hints (("Goal" :in-theory (enable strictly-dominates))))

(defthm strictly-dominated-by-some-from-strictly-dominated-dominated-by-some-2
  (implies
   (and
    (dominated-by-some x list)
    (strictly-dominates x path))
   (strictly-dominated-by-some path list))
  :rule-classes (:forward-chaining :rewrite))

(defthm strictly-dominated-by-some-from-striclty-dominated-by-some-all-dominated-by-some-1
  (implies
   (and
    (all-dominated-by-some x y)
    (strictly-dominated-by-some path x))
   (strictly-dominated-by-some path y))
  :rule-classes (:rewrite :forward-chaining))

(defthm strictly-dominated-by-some-from-striclty-dominated-by-some-all-dominated-by-some-2
  (implies
   (and
    (strictly-dominated-by-some path x)
    (all-dominated-by-some x y))
   (strictly-dominated-by-some path y))
  :rule-classes (:rewrite :forward-chaining))

(defthm non-divergence-from-common-domination
  (implies
   (and
    (dominates x a)
    (dominates y a))
   (not (diverge x y)))
  :rule-classes (:forward-chaining))

(defthm strictly-dominates-from-not-diverge-and-not-dominates-1
  (implies
   (and
    (not (diverge x y))
    (not (dominates x y)))
   (strictly-dominates y x))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable diverge strictly-dominates))))

(defthm strictly-dominates-from-not-diverge-and-not-dominates-2
  (implies
   (and
    (not (dominates x y))
    (not (diverge x y)))
   (strictly-dominates y x))
  :rule-classes (:forward-chaining))

(encapsulate
 ()

 (encapsulate
  (((dom-subhyps) => *)
   ((dom-subset) => *)
   ((dom-superset) => *))

  (local (defun dom-subhyps () nil))
  (local (defun dom-subset () nil))
  (local (defun dom-superset () nil))

  (defthm multiplicity-constraint
    (implies
     (and
      (dom-subhyps)
      (dominated-by-some arbitrary-element (dom-subset)))
     (dominated-by-some arbitrary-element (dom-superset)))
    :rule-classes nil)
  )

 (local (defun badguy (x y)
          (cond ((atom x)
                 nil)
                ((not (dominated-by-some (car x) y))
                 (car x))
                (t (badguy (cdr x) y)))))

 (local (in-theory (disable NOT-DOMINATED-BY-SOME-BY-MEMBERSHIP)))

 (local (defthm badguy-witness
          (implies
           (not (all-dominated-by-some x y))
           (and (dominated-by-some (badguy x y) x)
                (not (dominated-by-some (badguy x y) y))))
          :otf-flg t
          :rule-classes (:rewrite :forward-chaining)))

 (defthm dom-subset-by-multiplicity-driver
   (implies (dom-subhyps)
            (all-dominated-by-some (dom-subset) (dom-superset)))
   :rule-classes nil
   :hints(("Goal"
           :use ((:instance
                  multiplicity-constraint
                  (arbitrary-element (badguy (dom-subset) (dom-superset))))))))

 (ADVISER::defadvice dom-subset-by-multiplicity
   (implies (dom-subhyps)
            (all-dominated-by-some (dom-subset) (dom-superset)))
   :rule-classes (:pick-a-point :driver dom-subset-by-multiplicity-driver))

 )

(defthm all-dominated-by-some-id
  (all-dominated-by-some x x))

(defun setequiv (x y)
  (and (all-dominated-by-some x y)
       (all-dominated-by-some y x)))

(defequiv setequiv)

(defthm setequiv-cons-reduction
  (implies
   (dominated-by-some path x)
   (setequiv (cons path x) x)))

(defthm setequiv-append-reduction
  (implies
   (all-dominated-by-some x y)
   (setequiv (append x y) y)))

(defcong list::equiv setequiv (cons a x) 1)
(defcong setequiv setequiv (cons a x) 2)
(defcong setequiv setequiv (append x y) 1)
(defcong setequiv setequiv (append x y) 2)

(defcong setequiv equal (all-dominated-by-some x y) 1)
(defcong setequiv equal (all-dominated-by-some x y) 2)
(defcong setequiv equal (dominated-by-some a x) 2)
(defcong setequiv equal (strictly-dominated-by-some a x) 2)

;;
;; I think we should get these rules from refinement of list::setequiv
;;

(defthm setequiv-cons-commute
  (setequiv (cons a (cons b x))
            (cons b (cons a x))))

(defthm setequiv-cons-duplicate
  (setequiv (cons a (cons a x))
            (cons a x)))

(defthm setequiv-append-commute
  (setequiv (append x (append y z))
            (append y (append x z))))

(defthm setequiv-append-duplicate
  (setequiv (append x (append x y))
            (append x y)))

(in-theory (disable setequiv))

;;
;; pick-a-point for setequiv
;;
(encapsulate
 ()

 (encapsulate
  (((setequiv-subhyps) => *)
   ((setequiv-lhs) => *)
   ((setequiv-rhs) => *))

  (local (defun setequiv-subhyps () nil))
  (local (defun setequiv-lhs () nil))
  (local (defun setequiv-rhs () nil))

  (defthm setequiv-multiplicity-constraint
    (implies
     (setequiv-subhyps)
     (and
      (implies
       (dominated-by-some arbitrary-element (setequiv-lhs))
       (dominated-by-some arbitrary-element (setequiv-rhs)))
      (implies
       (dominated-by-some arbitrary-element (setequiv-rhs))
       (dominated-by-some arbitrary-element (setequiv-lhs)))))
    :rule-classes nil)
  )

 (local (defun badguy (x y)
          (cond ((atom x)
                 nil)
                ((not (dominated-by-some (car x) y))
                 (car x))
                (t (badguy (cdr x) y)))))

 (local (in-theory (disable NOT-DOMINATED-BY-SOME-BY-MEMBERSHIP)))
 (local (in-theory (disable DOM-SUBSET-BY-MULTIPLICITY)))

 (local (defthm badguy-witness-1
          (implies
           (not (all-dominated-by-some lhs rhs))
           (and (dominated-by-some (badguy lhs rhs) lhs)
                (not (dominated-by-some (badguy lhs rhs) rhs))))
          :otf-flg t
          :rule-classes (:rewrite :forward-chaining)))

 (defthm setequiv-by-multiplicity-driver
   (implies (setequiv-subhyps)
            (setequiv (setequiv-lhs) (setequiv-rhs)))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (enable setequiv)
           :use ((:instance
                  setequiv-multiplicity-constraint
                  (arbitrary-element (badguy (setequiv-lhs) (setequiv-rhs))))
                 (:instance
                  setequiv-multiplicity-constraint
                  (arbitrary-element (badguy (setequiv-rhs) (setequiv-lhs))))))))

 (ADVISER::defadvice setequiv-by-multiplicity
   (implies (setequiv-subhyps)
            (setequiv (setequiv-lhs) (setequiv-rhs)))
   :rule-classes (:pick-a-point :driver setequiv-by-multiplicity-driver))

 )

;;
;; path-remove <-> remove
;;
(defun path-remove (path set)
  (if (consp set)
      (if (dominates path (car set))
          (path-remove path (cdr set))
        (cons (car set) (path-remove path (cdr set))))
    set))

;; member of remove
(defthm dominated-by-some-remove
  (equal (dominated-by-some a (path-remove path list))
         (if (dominates path a)
             (strictly-dominated-by-some path list)
           (dominated-by-some a list)))
  :hints (("Goal" :induct (path-remove path list)
           :in-theory (disable NOT-STRICTLY-DOMINATED-BY-SOME-BY-MEMBERSHIP))))

;; strict-member of remove
(defthm strictly-dominated-by-some-remove
  (equal (strictly-dominated-by-some a (path-remove path list))
         (if (dominates path a)
             (strictly-dominated-by-some path list)
           (strictly-dominated-by-some a list)))
  :hints (("Goal" :induct (path-remove path list)
           :in-theory (disable strictly-dominates-implies-dominates
                               NOT-STRICTLY-DOMINATED-BY-SOME-WHEN-DIVERGES-FROM-ALL
                               DIVERGES-FROM-WHEN-NOT-STRICTLY-DOMINATED-BY-SOME-AND-NOT-DOMINATES-SOME
                               DIVERGES-OF-CDR-BY-DIVERGES-FROM-ALL
                               FIRST-DOMINATOR-OF-CDR
                               DIVERGES-FROM-ALL-WHEN-NO-DOMINATION-ALT
                               NOT-DOMINATES-FROM-<-OF-LEN-AND-LEN
                               ))))

#|

Just checking setequiv reduction.

(defthm iff-reduction
  (equal (iff a b)
         (and
          (implies a b)
          (implies b a))))

(defthm dominated-by-some-remove-reduction
  (implies
   (strictly-dominated-by-some a x)
   (setequiv (path-remove a x) x))
  :hints (("Goal" :induct (path-remove a x))))

(defthm dominates-some-car-consp
  (implies
   (consp x)
   (dominates-some (car x) x)))

(defthm len-path-remove
  (implies
   (dominates-some path x)
   (< (len (path-remove path x)) (len x)))
  :hints (("Goal" :induct (path-remove path x)))
  :rule-classes (:linear))

(defun path-remove-induction-2 (x y)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (path-remove-induction-2 (path-remove (car x) x) (path-remove (car x) y))
    (list x y)))

(thm
 (implies
  (dominated-by-some a x)
  (equal (setequiv x y)
         (and (dominated-by-some a y)
              (setequiv (path-remove a x) (path-remove a y)))))
 :hints (("Goal" :induct (path-remove-induction-2 x y))))
|#


#|
;; Know how you will be using "remove".  It is probably the case
;; that you will usually want to focus on "maximally short" paths.

;; Here is the reduction you might want:

(equal (setequiv (cons a x) y)
       (and (dominated-by-some a y)
            (setequiv (path-remove a x) (path-remove a y))))

(defcong setequiv setequiv (path-remove path set) 2)
|#

#|
(defun path-member (x list)
  (if (consp list)
      (or (list::equiv x (car list))
          (path-member x (cdr list)))
    nil))

(defcong list::equiv equal (path-member x list) 1)

(defcong list::list-equiv equal (path-member x list) 2
  :hints (("goal" :induct (list::len-len-induction list list::list-equiv))))

(defun path-subset (a b)
  (if (consp a)
      (and (path-member (car a) b)
           (path-subset (cdr a) b))
    t))

(defcong list::list-equiv equal (path-subset a b) 1
  :hints (("goal" :induct (list::len-len-induction a list::a-equiv))))

(defcong list::list-equiv equal (path-subset a b) 2)

(defthm path-member-chaining
  (implies
   (and
    (path-subset a b)
    (path-member x a))
   (path-member x b))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-member-chaining-free
  (implies
   (and
    (path-member x a)
    (path-subset a b))
   (path-member x b)))

(defthm path-subset-chaining-1
  (implies
   (and
    (path-subset b c)
    (path-subset a b))
   (path-subset a c))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subset-chaining-free-1
  (implies
   (and
    (path-subset a b)
    (path-subset b c))
   (path-subset a c)))

(defthm path-subset-chaining-2
  (implies
   (and
    (path-subset a y)
    (path-subset y z))
   (path-subset a z))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subset-chaining-free-2
  (implies
   (and
    (path-subset y z)
    (path-subset a y))
   (path-subset a z)))

(encapsulate
    ()

  (encapsulate
      (((path-subset-hyps) => *)
       ((path-subset-sub) => *)
       ((path-subset-sup) => *))
    (local (defun path-subset-hyps () nil))
    (local (defun path-subset-sub () nil))
    (local (defun path-subset-sup () nil))

    (defthmd path-memberp-constraint
      (implies (and (path-subset-hyps)
                    (path-member path-subset-member (path-subset-sub)))
               (path-member path-subset-member (path-subset-sup))))

    )

  (local (defund badguy (x y)
           (if (endp x)
               nil
             (if (path-member (car x) y)
                 (badguy (cdr x) y)
               (car x)))))

  (local (defthm badguy-witness
           (implies (not (path-subset x y))
                    (and (path-member (badguy x y) x)
                         (not (path-member (badguy x y) y))))
           :hints(("Goal" :in-theory (enable badguy)))))

  (defthm path-subset-by-membership-driver
    (implies (path-subset-hyps)
             (path-subset (path-subset-sub) (path-subset-sup)))
    :rule-classes nil
    :hints(("Goal"
            :use (:instance path-memberp-constraint
                            (path-subset-member
                             (badguy (path-subset-sub)
                                     (path-subset-sup)))))))

  (defadvice path-subset-by-membership
    (implies (path-subset-hyps)
             (path-subset (path-subset-sub) (path-subset-sup)))
    :rule-classes (:pick-a-point
                   :driver path-subset-by-membership-driver))
  )


(defthm path-subset-self
  (path-subset a a))

(defund path-equiv (a b)
  (and (path-subset a b)
       (path-subset b a)))

(defthmd path-equiv-double-containment
  (equal (path-equiv a b)
         (and (path-subset a b)
              (path-subset b a)))
  :hints (("goal" :in-theory (enable path-equiv))))

(defequiv path-equiv
  :hints (("goal" :in-theory (enable path-equiv))))

(defcong path-equiv equal (path-member a x) 2
  :hints (("goal" :in-theory (enable path-equiv))))

(defthm path-subset-cdr
  (path-subset (cdr y) y))

(defthmd path-subset-cdr-forward
  (path-subset (cdr y) y)
  :rule-classes ((:forward-chaining :trigger-terms ((cdr y)))))

(defun path-remove (x list)
  (if (consp list)
      (if (list::equiv x (car list))
          (path-remove x (cdr list))
        (cons (car list) (path-remove x (cdr list))))
    nil))

(defthm acl2-count-path-remove
  (<= (acl2-count (path-remove x list))
      (acl2-count list))
  :rule-classes (:linear))

(defcong list::equiv equal (path-remove x list) 1)
(defcong list::list-equiv list::list-equiv (path-remove x list) 2
  :hints (("goal" :induct (list::len-len-induction list list::list-equiv))))

(defthm path-member-of-path-remove
  (equal (path-member a (path-remove b list))
         (if (list::equiv a b) nil
           (path-member a list))))

(defthmd path-subset-membership-reduction
  (implies
   (path-member a y)
   (equal (path-subset y z)
          (and (path-member a z)
               (path-subset (path-remove a y) (path-remove a z)))))
  :hints (("goal" :in-theory (disable BOOLEANP-COMPOUND-RECOGNIZER
                                      PATH-SUBSET-BY-MEMBERSHIP))))

(defthmd car-membership-forward
  (implies
   (consp x)
   (path-member (car x) x))
  :rule-classes (:forward-chaining))

(encapsulate
    ()

  (encapsulate
      (((path-equiv-hyps) => *)
       ((path-equiv-a) => *)
       ((path-equiv-b) => *))
    (local (defun path-equiv-hyps () nil))
    (local (defun path-equiv-a () nil))
    (local (defun path-equiv-b () nil))

    (defthmd path-equiv-constraint
      (implies (path-equiv-hyps)
               (equal (path-member path-equiv-member (path-equiv-a))
                      (path-member path-equiv-member (path-equiv-b)))))

    )

  (local (defun badguy (x y)
           (if (endp x)
               (if (consp y)
                   (list (car y))
                 nil)
             (if (path-member (car x) y)
                 (badguy (path-remove (car x) (cdr x)) (path-remove (car x) y))
               (list (car x))))))

  (local
   (defthmd consp-badguy-implies
     (implies
      (consp (badguy x y))
      (iff (equal (path-member (car (badguy x y)) x)
                  (path-member (car (badguy x y)) y)) nil))))

  (local
   (defthmd consp-badguy-to-path-equiv
     (equal (path-equiv x y)
            (not (consp (badguy x y))))
     :hints (("goal" :induct (badguy x y)
              :in-theory (enable car-membership-forward
                                 path-subset-membership-reduction
                                 path-subset-cdr-forward
                                 path-equiv)))))

  (local (defthm badguy-witness
           (implies (not (path-equiv x y))
                    (not (equal (path-member (car (badguy x y)) x)
                                (path-member (car (badguy x y)) y))))
           :hints(("Goal" :in-theory nil
                   :use (consp-badguy-implies
                         consp-badguy-to-path-equiv)))))

  (defthm path-equiv-by-membership-driver
    (implies (path-equiv-hyps)
             (path-equiv (path-equiv-a) (path-equiv-b)))
    :rule-classes nil
    :hints(("Goal" :in-theory '(badguy-witness)
            :use (:instance path-equiv-constraint
                            (path-equiv-member
                             (car (badguy (path-equiv-a)
                                          (path-equiv-b))))))))

  (defadvice path-equiv-by-membership
    (implies (path-equiv-hyps)
             (path-equiv (path-equiv-a) (path-equiv-b)))
    :rule-classes (:pick-a-point
                   :driver path-equiv-by-membership-driver))

  (in-theory (disable path-equiv-by-membership))

  )

(defthmd non-membership-path-remove-reduction
  (implies
   (not (path-member a x))
   (equal (path-remove a x)
          (list::fix x))))

(defrefinement list::list-equiv path-equiv
  :hints (("goal" :in-theory (enable path-equiv-by-membership))))

(defthm membership-implies-membership
  (implies
   (bag::memberp a x)
   (path-member a x)))

(defthm path-membership-from-subbagp
  (implies
   (and
    (bag::subbagp x y)
    (path-member path x))
   (path-member path y)))

(defthm path-subset-from-subbag
  (implies
   (bag::subbagp x y)
   (path-subset x y)))

(defrefinement bag::perm path-equiv
  :hints (("goal" :in-theory (enable path-equiv-by-membership))))

|#
#|

;;
;; Here is an even stronger equivalence
;;

(defthm subset-remove
  (path-subset (path-remove a x) x)
  :rule-classes ((:forward-chaining :trigger-terms ((path-remove a x)))))

(defthmd open-path-subset-on-membership
  (implies
   (path-member a x)
   (equal (path-subset x y)
          (and (path-member a y)
               (path-subset (path-remove a x) (path-remove a y))))))

(defthmd open-path-equiv-on-membership
  (implies
   (path-member a x)
   (equal (path-equiv x y)
          (and (path-member a y)
               (path-equiv (path-remove a x)
                           (path-remove a y)))))
  :hints (("goal" :in-theory (enable open-path-subset-on-membership path-equiv))))

(defthmd path-equiv-reduction
  (equal (path-equiv x y)
         (and (equal (path-member a x)
                     (path-member a y))
              (path-equiv (path-remove a x)
                          (path-remove a y))))
  :hints (("goal" :in-theory (enable non-membership-path-remove-reduction
                                     open-path-equiv-on-membership))))


;; I'm not sure this is what we want to do.  I think for
;; congruences we want to reason using double-containment.

(defun path-equiv-induction (x y)
  (if (consp x)
      (and (path-member (car x) y)
           (path-equiv-induction (path-remove (car x) (cdr x)) (path-remove (car x) y)))
    (not (consp y))))

(defthm not-consp-path-equiv
  (implies
   (not (consp x))
   (and (equal (path-equiv x y)
               (not (consp y)))
        (equal (path-equiv y x)
               (not (consp y)))))
  :hints (("goal" :in-theory (enable path-equiv))))

(defthmd open-path-equiv
  (implies
   (consp x)
   (and (equal (path-equiv x y)
               (and (path-member (car x) y)
                    (path-equiv (path-remove (car x) (cdr x))
                                (path-remove (car x) y))))
        (equal (path-equiv y x)
               (and (path-member (car x) y)
                    (path-equiv (path-remove (car x) y)
                                (path-remove (car x) (cdr x)))))))
  :hints (("goal" :use (:instance path-equiv-reduction
                                  (a (car x))))))

(defthm not-strictly-dominated-by-some-subset
  (IMPLIES (AND (PATH-SUBSET sub sup)
                (NOT (STRICTLY-DOMINATED-BY-SOME A sup)))
           (NOT (STRICTLY-DOMINATED-BY-SOME A sub)))
  :hints (("goal" :in-theory (enable STRICTLY-DOMINATED-BY-SOME))))

(defcong path-equiv equal (cpath::strictly-dominated-by-some a x) 2
  :hints (("goal" :in-theory (enable path-equiv))))

(defthm path-subset-dominates-some
  (implies
   (and
    (path-subset sub sup)
    (dominates-some x sub))
   (dominates-some x sup)))

(defcong path-equiv equal (dominates-some x list) 2
  :hints (("goal" :in-theory (enable path-equiv))))

(defthm path-subset-dominated-by-some
  (implies
   (and
    (path-subset sub sup)
    (dominated-by-some x sub))
   (dominated-by-some x sup)))

(defcong path-equiv equal (dominated-by-some x list) 2
  :hints (("goal" :in-theory (enable path-equiv))))

;; This is our dom membership function

(defun path-subdom (x y)
  (if (consp x)
      (and (or (dominated-by-some (car x) (cdr x))
               (dominates-some (car x) y))
           (path-subdom (cdr x) y))
    t))

;; (all-dominate-some x y)

(and (all-dominate-some (purge x) y)
     (all-dominate-some (purge y) x))

(defcong path-equiv equal (path-subset a b) 2)

(defthm path-subset-path-subdom
  (implies
   (and
    (path-subset sub sup)
    (path-subdom sup x))
   (path-subdom sub x)))

(defcong path-equiv equal (path-subdom a b) 1
  :hints (("goal" :in-theory (enable path-equiv))))

DAG

(in-theory (enable dominates-some))
(in-theory (enable dominated-by-some))
;;
;; and even this goes thru only with pain ..
;;

(defthm hack-lemma
  (IMPLIES (AND
            (PATH-SUBDOM LIST B)
            (NOT (DOMINATED-BY-SOME X LIST))
            (DOMINATES X A)
            (DOMINATED-BY-SOME A LIST)
            )
           (DOMINATES-SOME X B)))

(defthm dominates-some-chaining
  (implies
   (and
    (path-subdom a b)
    (not (dominated-by-some x a))
    (dominates-some x a))
   (dominates-some x b))
  :rule-classes (:rewrite :forward-chaining))

(defthm dominates-some-chaining-free
  (implies
   (and
    (dominates-some x a)
    (not (dominated-by-some x a))
    (path-subdom a b))
   (dominates-some x b)))

(thm
  (IMPLIES (AND (PATH-SUBDOM B C)
                (PATH-SUBDOM LIST B)
                (NOT (DOMINATED-BY-SOME R LIST))
                (DOMINATES-SOME R B))
           (DOMINATES-SOME R C))
  :hints (("goal" :induct (PATH-SUBDOM LIST B))))

(defthm path-subdom-chaining-1
  (implies
   (and
    (path-subdom b c)
    (path-subdom a b))
   (path-subdom a c))
  :hints (("goal" :induct (path-subdom a c)))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subdom-chaining-free-1
  (implies
   (and
    (path-subdom a b)
    (path-subdom b c))
   (path-subdom a c)))

(defthm path-subdom-chaining-2
  (implies
   (and
    (path-subdom a y)
    (path-subdom y z))
   (path-subdom a z))
  :rule-classes (:rewrite :forward-chaining))

(defthm path-subdom-chaining-free-2
  (implies
   (and
    (path-subdom y z)
    (path-subdom a y))
   (path-subdom a z)))


DAG

(defun path-domequiv (x y)
  (and (path-subdom x y)
       (path-subdom y x)))

(defcong path-equiv equal (all-dom-some x y) 2)

(defun path-domequiv (x y)
  (and (all-dominate-some x y)
       (all-dominate-some y x)))


(defun all-dominate-some

;; dominates-or-diveres-from-all

(defun path-dominates-some (x list)
  )






(defun contains-dominators (x list)
  )

(defun remove-dominators (x list)
  )

(defun dom (x)
  (if (consp x)
      (if (cpath::strictly-dominated-by-some (car x) (cdr x))
          (dom (cdr x))
        (cons (car x)
              (dom (cpath::remove-dominators (cdr x))))
    nil))

(defun path-subdom (x y)
  (if (consp x)
      (if (cpath::strictly-dominated-by-some (car x) (cdr x))
          (path-subdom (cdr x) y)
        (and (not (cpath::strictly-dominated-by-some (car x) y))
             (path-subdom (cdr x) y)))
    t))

(defcong path-equiv equal (path-subdom a b) 2)

(defthm test
  (implies
   (and
    (path-subdom sub sup)
    (not (cpath::strictly-dominated-by-some x sup))
    (dominates-some x sup))
   (and
    (not (cpath::strictly-dominated-by-some x sub))
    (dominates-some x sub))))

(defthm path-subdom-subset
  (implies
   (and
    (path-subdom sub sup)
    (path-subdom x sub))
   (path-subdom x sup)))

(defcong path-equiv equal (path-subdom a b) 1
  :hints (("goal" :in-theory (enable path-equiv))))


  :hints (("goal" :induct (list::len-len-induction a list::a-equiv))))

(defun cpath::domequiv (x y)
  (and (cpath::subdom x y)
       (cpath::subdom y x)))

(defrefinement path-equiv cpath::subdom)
|#
