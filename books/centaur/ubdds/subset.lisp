; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.


; subset.lisp -- BDD subset operation and set-based reasoning about BDDs
;
; Think of a BDD not as an object but as the set of bit-vectors it satisfies.
; In this mindset, (eval-bdd P v) can be thought of as v \in P, and qs-subset
; extends this idea so that (qs-subset P Q) means "for every v \in P, v \in Q."
; In this way of thinking, NIL is the empty set, T is the universal set, and
; many BDD-building operations have obvious interpretations, e.g., Q-AND is set
; intersection, Q-OR is union, Q-NOT is complement, etc.
;
; We can understand our BDD operations through this membership property.
; Indeed, our "correctness" theorems about eval-bdd are simple statements of
; how these operations affect membership in the satisfying set of bit vectors
; for this BDD.

(in-package "ACL2")
(include-book "extra-operations")


(local (in-theory (enable* (:ruleset canonicalize-to-q-ite))))

(defund qs-subset (x y)
  (declare (xargs :guard t
                  :verify-guards nil))
  (mbe :logic (equal t (q-implies x y))
       :exec
       (cond ((atom x)
              (if x
                  ;; [Jared]: changing this to support the
                  ;; booleanification of q-implies in
                  ;; the atom case.
                  (and (atom y)
                       (if y t nil))
                t))
             ((atom y)
              ;; [Jared]: I changed this case slightly to better-handle
              ;; non-normp objects.  With this change, we get the mbe
              ;; equivalence without normp hyps.
              (if y t nil))
             ((hons-equal x y)
              t)
             (t
              (and (qs-subset (car x) (car y))
                   (qs-subset (cdr x) (cdr y)))))))

(verify-guards qs-subset
               :hints (("Goal" :in-theory
                        (e/d (qs-subset q-implies q-not)
                             (canonicalize-q-implies canonicalize-q-not)))))

(defthm |(qs-subset nil x)|
  (qs-subset nil x)
  :hints(("Goal" :in-theory (e/d (qs-subset q-implies)
                                 (canonicalize-q-implies)))))

(defthm |(qs-subset x t)|
  (qs-subset x t)
  :hints(("Goal" :in-theory (e/d (qs-subset q-implies)
                                 (canonicalize-q-implies)))))

(defthm eval-bdd-when-qs-subset
  ;; "Subset preserves membership"
  (implies (and (qs-subset x y)
                (eval-bdd x values))
           (eval-bdd y values))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary (implies (and (eval-bdd x values)
                                                    (qs-subset x y))
                                               (eval-bdd y values)))
                 (:rewrite :corollary (implies (and (qs-subset x y)
                                                    (not (eval-bdd y values)))
                                               (equal (eval-bdd x values)
                                                      nil)))
                 (:rewrite :corollary (implies (and (not (eval-bdd y values))
                                                    (qs-subset x y))
                                               (equal (eval-bdd x values)
                                                      nil))))
  :hints(("Goal"
          :in-theory (e/d (qs-subset)
                          (eval-bdd-of-q-implies))
          :use ((:instance eval-bdd-of-q-implies
                           (x x)
                           (y y))))))

(defthm reflexivity-of-qs-subset
  (qs-subset x x)
  :hints(("Goal" :in-theory (e/d (qs-subset q-implies)
                                 (canonicalize-q-implies)))))

(encapsulate
 ()
 (local (defthm lemma
          ;; Ugly, but gets hyp-free transitivity rule
          (implies (and (equal t (q-implies x y))
                        (equal t (q-implies y z)))
                   (equal (equal t (q-implies x z)) t))
          :hints(("Goal" :in-theory (e/d (q-implies q-not)
                                         (canonicalize-q-implies
                                          canonicalize-q-not
                                          equal-by-eval-bdds))))))

 (defthm transitivity-of-qs-subset
    (implies (and (qs-subset x y)
                  (qs-subset y z))
             (equal (qs-subset x z)
                    t))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary (implies (and (qs-subset y z)
                                                      (qs-subset x y))
                                                 (equal (qs-subset x z)
                                                        t))))
    :hints(("Goal" :in-theory (e/d (qs-subset)
                                   (normp-of-q-implies canonicalize-q-implies))))))





(defsection qs-subset-by-eval-bdds

  (local (in-theory (disable canonicalize-q-implies normp-of-q-implies)))
  (local (in-theory (enable qs-subset)))

  (encapsulate
   (((qs-subset-hyps) => *)
    ((qs-subset-lhs) => *)
    ((qs-subset-rhs) => *))
   (local (defun qs-subset-hyps () nil))
   (local (defun qs-subset-lhs () nil))
   (local (defun qs-subset-rhs () nil))
   (defthmd qs-subset-by-eval-bdds-constraint
     (implies (qs-subset-hyps)
              (implies (eval-bdd (qs-subset-lhs) arbitrary-values)
                       (eval-bdd (qs-subset-rhs) arbitrary-values)))))


  (local (defund qs-subset-badguy (x y)
           (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
           (if (or (consp x)
                   (consp y))
               ;; At least one of them is a cons.  We descend both trees and try
               ;; to discover a path that will break their equality.
               (mv-let (car-successp car-path)
                       (qs-subset-badguy (qcar x) (qcar y))
                       (if car-successp
                           ;; We took the "true" branch.
                           (mv t (cons t car-path))
                         (mv-let (cdr-successp cdr-path)
                                 (qs-subset-badguy (qcdr x) (qcdr y))
                                 (if cdr-successp
                                     (mv t (cons nil cdr-path))
                                   (mv nil nil)))))
             ;; Otherwise, both are atoms.  Does x imply y?  If not, we have found
             ;; a violation.
             (mv (not (implies x y)) nil))))

  (local (defthm mv-nth-1
           (equal (mv-nth 1 x)
                  (cadr x))
           :hints(("Goal" :in-theory (enable mv-nth)))))

  (local (defthm lemma1
           (implies (car (qs-subset-badguy x y))
                    (and (eval-bdd x (cadr (qs-subset-badguy x y)))
                         (not (eval-bdd y (cadr (qs-subset-badguy x y))))))
           :hints(("Goal" :in-theory (enable qs-subset-badguy eval-bdd)
                   :induct (qs-subset-badguy x y)))))


  (local (defthm q-implies-of-t-when-atom-left
           (implies (not (consp x))
                    (equal (equal t (q-implies x y))
                           (IF X
                               (if (atom y)
                                   (if y t nil)
                                 nil)
                               T)))
           :hints(("Goal" :in-theory (enable q-implies)))))

  (local (defthm q-implies-of-t-when-atom-right
           (implies (not (consp y))
                    (equal (equal t (q-implies x y))
                           (IF (ATOM X)
                               (IF X
                                   (if (atom y) (if y t nil) nil)
                                   T)
                               (IF Y
                                   T
                                   (equal t (Q-NOT X))))))
           :hints(("Goal" :in-theory (enable q-implies)))))

  (local (defthm equal-t-of-q-implies-of-cons
           (equal (equal t (q-implies (cons a x) (cons b y)))
                  (and (equal t (q-implies a b))
                       (equal t (q-implies x y))))
           :hints(("Goal" :in-theory (enable q-implies)))))

  (local (defthm lemma2
           ;; BOZO can anything be done about these hyps?
           (implies (and (normp x)
                         (normp y))
                    (equal (car (qs-subset-badguy x y))
                           (not (equal t (qs-subset x y)))))
           :hints(("Goal"
                   :induct (qs-subset-badguy x y)
                   :in-theory (e/d (qs-subset-badguy normp q-not)
                                   (q-implies-of-nil
                                    equal-by-eval-bdds
                                    canonicalize-q-not))))))

  (defthm qs-subset-by-eval-bdds
    (implies (and (qs-subset-hyps)
                  (normp (qs-subset-lhs))
                  (normp (qs-subset-rhs)))
             (equal (qs-subset (qs-subset-lhs) (qs-subset-rhs))
                    t))
    :hints(("Goal"
            :use ((:instance qs-subset-by-eval-bdds-constraint
                             (arbitrary-values (cadr (qs-subset-badguy (qs-subset-lhs)
                                                                       (qs-subset-rhs)))))))))

  (defun qs-subset-by-eval-bdds-hint (clause pspv stable world)
    (declare (xargs :mode :program))
    (and stable
      (let* ((rcnst (access prove-spec-var pspv :rewrite-constant))
             (ens   (access rewrite-constant rcnst :current-enabled-structure)))
        (and (enabled-numep (fnume '(:rewrite qs-subset-by-eval-bdds) world) ens)
             (let ((conclusion (car (last clause))))
               (and (consp conclusion)
                    (eq (car conclusion) 'qs-subset)
                    (let* ((lhs  (second conclusion))
                           (rhs  (third conclusion))
                           (hyps (dumb-negate-lit-lst (butlast clause 1)))
                           ;; We always think they are normp's if we're asking about qs-subset, so
                           ;; we don't consult the rewriter.
                           (hint `(:use (:functional-instance qs-subset-by-eval-bdds
                                          (qs-subset-hyps (lambda () (and ,@hyps)))
                                          (qs-subset-lhs  (lambda () ,lhs))
                                          (qs-subset-rhs  (lambda () ,rhs))))))
                      (prog2$
                       ;; And tell the user what's happening.
                       (cw "~|~%We now appeal to ~s0 in an attempt to show that ~x1 is a ~
                          qs-subset of ~x2.  (You can disable ~s0 to avoid this.)  ~
                          The hint we give is: ~x3~|~%"
                           'qs-subset-by-eval-bdds
                           (untranslate lhs nil world)
                           (untranslate rhs nil world)
                           hint)
                       hint))))))))

  (add-default-hints!
   '((qs-subset-by-eval-bdds-hint clause pspv stable-under-simplificationp world))))





(defsection double-containment

  ;; A radical idea.  Lets use double-containment as our normal form for
  ;; equalities between BDDs.  The wonderful benefit if this is that all of the
  ;; subset relationships will be exposed in the hypotheses we have.  And then
  ;; our rules about subset can work on simplifying them, and our membership
  ;; relationships will become more apparent.

  (local (defthm lemma
           (implies (and (normp x)
                         (normp y)
                         (qs-subset x y)
                         (qs-subset y x))
                    (equal (equal x y)
                           t))))

  (defthm bdd-equality-is-double-containment
    (implies (and (normp x)
                  (normp y))
             (equal (equal x y)
                    (and (qs-subset x y)
                         (qs-subset y x)))))

  ;; This new subset-based strategy, along with the subset by membership computed
  ;; hint, effectively replaces equal-by-bdds.  (Or should, once we make the hint
  ;; a little more powerful.)

  (in-theory (disable equal-by-eval-bdds))


  ;; An bit of a catch is that booleans are normp's too, so we will now be
  ;; rewriting equalities between booleans as qs-subset's.  To fix this, replace
  ;; subsets between booleans with implies, and the net effect is no different
  ;; than equal-of-booleans-rewrite, though more roundabout.

  (defthm qs-subset-when-booleans
    (implies (and (booleanp x)
                  (booleanp y))
             (equal (qs-subset x y)
                    (implies (double-rewrite x)
                             (double-rewrite y))))
    :hints(("Goal" :in-theory (enable qs-subset q-implies)))))



(def-ruleset qs-subset-mode-rules '(bdd-equality-is-double-containment))


;; Do not add these rules.
;; They break the normal form of q-subset.

(defthmd |(qs-subset x nil)|
  (implies (normp x)
           (equal (qs-subset x nil)
                  (not (double-rewrite x))))
  :hints(("Goal" :in-theory (enable equal-by-eval-bdds))))

(defthmd |(qs-subset t x)|
  (implies (force (normp x))
           (equal (qs-subset t x)
                  (equal x t))))



(defsection qs-subset-mode-iff-rules

  ;; It is hard to canonicalize all the equalities.  In particular (equal x
  ;; nil) gets rewritten to (not x).  And (not (equal x nil)) gets rewritten to
  ;; x, alone.  We don't yet have a good strategy for this because it's very
  ;; difficult to target these things with rewrite rules.  But if they look
  ;; like BDDs, we can do it.

  (defthm qs-subset-canonicalization-of-iff
    ;; X != NIL --> ~(subset X NIL) v ~(subset NIL Y)
    ;;          --> ~(subset X NIL) v ~(T)
    ;;          --> ~(subset X NIL)
    (implies (normp x)
             (iff x
                  (not (qs-subset x nil))))
    :rule-classes nil
    :hints(("Goal"
            :in-theory (disable bdd-equality-is-double-containment)
            :use ((:instance bdd-equality-is-double-containment
                             (x x)
                             (y nil))))))

  ;; The above rule is what we really want.  But we can't have it, because we can't
  ;; target a variable with a rewrite rule.  So we just add it for each function that
  ;; we know makes a BDD.  It's lousy but maybe it's good enough?

  (defthm q-ite-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y))
                  (force (normp z)))
             (iff (q-ite x y z)
                  (not (qs-subset (q-ite x y z) nil))))
    :hints(("Goal" :use ((:instance qs-subset-canonicalization-of-iff
                                    (x (q-ite x y z)))))))

  (defthm q-not-iff-for-qs-subset-mode
    (implies (normp x)
             (iff (q-not x)
                  (not (qs-subset (q-not x) nil)))))

  (defthm q-and-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-and x y)
                  (not (qs-subset (q-and x y) nil)))))

  (defthm q-or-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-or x y)
                  (not (qs-subset (q-or x y) nil)))))

  (defthm q-implies-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-implies x y)
                  (not (qs-subset (q-implies x y) nil)))))

  (defthm q-or-c2-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-or-c2 x y)
                  (not (qs-subset (q-or-c2 x y) nil)))))

  (defthm q-and-c1-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-and-c1 x y)
                  (not (qs-subset (q-and-c1 x y) nil)))))

  (defthm q-and-c2-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-and-c2 x y)
                  (not (qs-subset (q-and-c2 x y) nil)))))

  (defthm q-iff-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-iff x y)
                  (not (qs-subset (q-iff x y) nil)))))

  (defthm q-xor-iff-for-qs-subset-mode
    (implies (and (force (normp x))
                  (force (normp y)))
             (iff (q-xor x y)
                  (not (qs-subset (q-xor x y) nil)))))


  (add-to-ruleset qs-subset-mode-rules
                  '(q-ite-iff-for-qs-subset-mode
                    q-not-iff-for-qs-subset-mode
                    q-and-iff-for-qs-subset-mode
                    q-or-iff-for-qs-subset-mode
                    q-implies-iff-for-qs-subset-mode
                    q-or-c2-iff-for-qs-subset-mode
                    q-and-c1-iff-for-qs-subset-mode
                    q-and-c2-iff-for-qs-subset-mode
                    q-iff-iff-for-qs-subset-mode
                    q-xor-iff-for-qs-subset-mode)))






;; QS-SUBSET of Q-ITE

(defsection qs-subset-of-q-ite-left

  ;; (Q-ITE X Y Z) is a subset of W exactly when:
  ;;   1. (INTERSECT X Y), and
  ;;   2. (INTERSECT (NOT X) Z),
  ;; are both subsets of W.

 (local (defthmd lemma
          (implies (and (force (normp x))
                        (force (normp y))
                        (force (normp z))
                        (force (normp w))
                        (qs-subset (q-ite x y nil) w)
                        (qs-subset (q-ite x nil z) w))
                   (qs-subset (q-ite x y z) w))))

 (local (defthmd lemma2
          (implies (and (qs-subset (q-ite x y z) w)
                        (force (normp x))
                        (force (normp y))
                        (force (normp z))
                        (force (normp w)))
                   (qs-subset (q-ite x y nil) w))))

 (local (defthmd lemma3
          (implies (and (qs-subset (q-ite x y z) w)
                        (force (normp x))
                        (force (normp y))
                        (force (normp z))
                        (force (normp w)))
                   (qs-subset (q-ite x nil z) w))))

 (defthm qs-subset-of-q-ite-left
   (implies (and (syntaxp (not (equal y ''nil)))
                 (syntaxp (not (equal z ''nil)))
                 (force (normp x))
                 (force (normp y))
                 (force (normp z))
                 (force (normp w)))
            (equal (qs-subset (q-ite x y z) w)
                   (and (qs-subset (q-ite x y nil) w)
                        (qs-subset (q-ite x nil z) w))))
   :hints(("Goal" :use ((:instance lemma)
                        (:instance lemma2)
                        (:instance lemma3))))))



(defsection qs-subset-of-q-ite-right

  ;; W is a subset of (Q-ITE X Y Z) exactly when:
  ;;  1. (INTERSECT X W) is a subset of Y, and
  ;;  2. (INTERSECT (NOT X) W) is a subset of Z.

 (local (defthmd lemma
          (implies (and (force (normp x))
                        (force (normp y))
                        (force (normp z))
                        (force (normp w))
                        (qs-subset (q-ite w x nil) y)
                        (qs-subset (q-ite x nil w) z))
                   (qs-subset w (q-ite x y z)))))

 (local (defthmd lemma2
          (implies (and (qs-subset w (q-ite x y z))
                        (force (normp x))
                        (force (normp y))
                        (force (normp z))
                        (force (normp w)))
                   (qs-subset (q-ite w x nil) y))))

 (local (defthmd lemma3
          (implies (and (qs-subset w (q-ite x y z))
                        (force (normp x))
                        (force (normp y))
                        (force (normp z))
                        (force (normp w)))
                   (qs-subset (q-ite x nil w) z))))

 (defthm qs-subset-of-q-ite-right
   ;; I don't think we need syntax rules here because we're always moving stuff to the left.
   (implies (and (force (normp x))
                 (force (normp y))
                 (force (normp z))
                 (force (normp w)))
            (equal (qs-subset w (q-ite x y z))
                   (and (qs-subset (q-ite w x nil) y)
                        (qs-subset (q-ite x nil w) z))))
   :hints(("Goal" :use ((:instance lemma)
                        (:instance lemma2)
                        (:instance lemma3))))))



(defsection |(qs-subset (q-ite x nil y) x)|

  ;; (SUBSET (INTERSECT (NOT X) Y) X) = (SUBSET Y X)

  (local (defthmd gross
           (implies (and (force (normp x))
                         (force (normp y))
                         (qs-subset (q-ite x nil y) x)
                         (eval-bdd y values))
                    (eval-bdd x values))
           :hints(("Goal" :use ((:instance eval-bdd-of-q-ite (y nil) (z y)))))))

  (local (defthmd lemma
           (implies (and (force (normp x))
                         (force (normp y))
                         (qs-subset (q-ite x nil y) x))
                    (qs-subset y x))
           :hints(("Goal" :in-theory (enable gross)))))

  (local (defthmd lemma2
           (implies (and (force (normp x))
                         (force (normp y))
                         (qs-subset y x))
                    (qs-subset (q-ite x nil y) x))))

  (defthm |(qs-subset (q-ite x nil y) x)|
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (qs-subset (q-ite x nil y) x)
                    (qs-subset y x)))
    :hints(("Goal" :use ((:instance lemma)
                         (:instance lemma2))))))



(defsection |(qs-subset (q-ite x nil y) nil)|

  ;; (SUBSET (INTERSECT (NOT X) Y) NIL) = (SUBSET Y X)

  (local (defthmd gross
           (implies (and (normp x)
                         (normp y)
                         (qs-subset (q-ite x nil y) nil)
                         (eval-bdd y values))
                    (eval-bdd x values))
           :hints(("goal" :use ((:instance eval-bdd-of-q-ite (y nil) (z y)))))))

  (local (defthmd lemma
           (implies (and (normp x)
                         (normp y)
                         (qs-subset (q-ite x nil y) nil))
                    (qs-subset y x))
           :hints(("Goal" :in-theory (enable gross)))))

  (local (defthmd lemma2
           (implies (and (normp x)
                         (normp y)
                         (qs-subset y x))
                    (qs-subset (q-ite x nil y) nil))))

  (defthm |(qs-subset (q-ite x nil y) nil)|
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (qs-subset (q-ite x nil y) nil)
                    (qs-subset y x)))
    :hints(("Goal" :use ((:instance lemma)
                         (:instance lemma2))))))





;; QS-SUBSET of Q-AND

(defthm |(qs-subset (q-ite x y nil) x)|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset (q-ite x y nil) x)))

(defthm |(qs-subset (q-ite x y nil) y)|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset (q-ite x y nil) y)))

(defthm |(qs-subset (q-and x y) x)|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset (q-and x y) x)))

(defthm |(qs-subset (q-and x y) y)|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset (q-and x y) y)))



;; BOZO it would probably get this automatically if we fix the computed hint
;; like Sol did, so that it doesn't only look at the conclusion but instead
;; looks for any literal (qs-subset x y).
(encapsulate
 ()
 (local (defthmd lemma
          (implies (and (force (normp x))
                        (force (normp y))
                        (qs-subset x y))
                   (equal (qs-subset x (q-and x y))
                          t))))

 (local (defthmd lemma2
          (implies (and (force (normp x))
                        (force (normp y))
                        (qs-subset x (q-and x y)))
                   (equal (qs-subset x y)
                          t))))

 (defthm |(qs-subset x (q-and x y))|
   (implies (and (force (normp x))
                 (force (normp y)))
            (equal (qs-subset x (q-and x y))
                   (qs-subset x y)))
   :hints(("Goal" :use ((:instance lemma)
                        (:instance lemma2))))))

(defthm |(qs-subset x (q-ite x y nil))|
  (implies (and (force (normp x))
                (force (normp y)))
           (equal (qs-subset x (q-ite x y nil))
                  (qs-subset x y)))
  :hints(("Goal" :use ((:instance |(qs-subset x (q-and x y))|)))))

(defthm |(qs-subset y (q-and x y))|
   (implies (and (force (normp x))
                 (force (normp y)))
            (equal (qs-subset y (q-and x y))
                   (qs-subset y x)))
   :hints(("Goal"
           :in-theory (disable canonicalize-q-and
                               qs-subset-of-q-ite-right
                               |(qs-subset x (q-ite x y nil))|)
           :use ((:instance |(qs-subset x (q-ite x y nil))|
                            (x y)
                            (y x))))))

(defthm |(qs-subset y (q-ite x y nil))|
   (implies (and (force (normp x))
                 (force (normp y)))
            (equal (qs-subset y (q-ite x y nil))
                   (qs-subset y x)))
   :hints(("Goal" :use ((:instance |(qs-subset y (q-and x y))|)))))





;; QS-SUBSET of Q-OR

(defthm |(qs-subset x (q-ite x t y))|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset x (q-ite x t y))))

(defthm |(qs-subset y (q-ite x t y))|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset y (q-ite x t y))))

(defthm |(qs-subset x (q-or x y))|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset x (q-or x y))))

(defthm |(qs-subset y (q-or x y))|
  (implies (and (force (normp x))
                (force (normp y)))
           (qs-subset y (q-or x y))))



(encapsulate
 ()
 (local (defthmd lemma
          (implies (and (force (normp x))
                        (force (normp y))
                        (qs-subset (q-or x y) x))
                   (qs-subset y x))))

 (local (defthmd lemma2
          (implies (and (force (normp x))
                        (force (normp y))
                        (qs-subset y x))
                   (qs-subset (q-or x y) x))))

 (defthm |(qs-subset (q-or x y) x)|
   (implies (and (force (normp x))
                 (force (normp y)))
            (equal (qs-subset (q-or x y) x)
                   (qs-subset y x)))
   :hints(("Goal" :use ((:instance lemma)
                        (:instance lemma2))))))

(defthm |(qs-subset (q-ite x t y) x)|
  (implies (and (force (normp x))
                (force (normp y)))
           (equal (qs-subset (q-ite x t y) x)
                  (qs-subset y x)))
  :hints(("Goal" :use ((:instance |(qs-subset (q-or x y) x)|)))))

(defthm |(qs-subset (q-or x y) y)|
  (implies (and (force (normp x))
                (force (normp y)))
           (equal (qs-subset (q-or x y) y)
                  (qs-subset x y)))
  :hints(("Goal"
          :in-theory (disable canonicalize-q-or |(qs-subset (q-or x y) x)|)
          :use ((:instance |(qs-subset (q-or x y) x)|
                           (x y) (y x))))))

(defthm |(qs-subset (q-ite x t y) y)|
  (implies (and (force (normp x))
                (force (normp y)))
           (equal (qs-subset (q-ite x t y) y)
                  (qs-subset x y)))
  :hints(("Goal" :use ((:instance |(qs-subset (q-or x y) y)|)))))




;; Example that works in qs-subset-mode but not otherwise

#||

(thm
  (IMPLIES (AND (NORMP C)
                (Q-ITE C HYP NIL)
                (NOT (EQUAL (Q-ITE C HYP NIL) HYP))
                (NORMP HYP)
                (not (qs-subset hyp nil))
                (NOT (EQUAL C T))
                (NOT (Q-ITE C NIL HYP))
                (NOT (EVAL-BDD C ARBITRARY-VALUES)))
           (NOT (EVAL-BDD HYP ARBITRARY-VALUES))))

||#

