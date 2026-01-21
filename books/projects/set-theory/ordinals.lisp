; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "set-algebra")

(in-theory (disable in-is-linear))

(defthmz transitive-preserves-in-1
  (implies (and (in y x)
                (in z y)
                (transitive x))
           (in z x))
  :rule-classes (:forward-chaining :rewrite))

(defthmz transitive-preserves-in-2
  (implies (and (in z y)
                (in y x)
                (transitive x))
           (in z x))
  :rule-classes (:forward-chaining :rewrite))

(defthmz ordinals-closure-1
  (implies (and (in-is-linear x)
                (transitive x)
                (in y x))
           (in-is-linear y))
  :hints (("Goal"
           :expand ((in-is-linear y))
           :in-theory (disable in-is-linear-necc)
           :use ((:instance in-is-linear-necc
                            (x (car (in-is-linear-witness y)))
                            (y (mv-nth 1 (in-is-linear-witness y)))
                            (s x))))))

; Start proof of in-has-no-3-cycle.

(defun triple (x y z)
  (declare (xargs :guard t))
  (insert x (pair y z)))

(in-theory (disable (:e union2)))

(encapsulate
  ()

  (local (defthmz equal-union2-0-lemma
           (implies (equal (union2 x y) 0)
                    (equal x 0))
           :instructions (:bash
                          (:casesplit (in (min-in x) (union2 x y)))
                          :prove
                          (:drop 1)
                          :prove)
           :rule-classes nil))

  (defthmz equal-union2-0 ; needed for triple-is-non-empty
    (equal (equal (union2 x y) 0)
           (and (equal x 0)
                (equal y 0)))
    :hints (("Goal"
             :use (equal-union2-0-lemma
                   (:instance equal-union2-0-lemma
                              (x y)
                              (y x)))))))

(defthmz triple-is-non-empty ; needed for m4 below
  (not (equal (triple x y z)
              0)))

(local (defun m (x y z)
         (min-in (triple x y z))))

(local (defthmz m1
         (implies (in x y)
                  (not (equal (m x y z) y)))
         :rule-classes nil))

(local (defthmz m2
         (implies (in y z)
                  (not (equal (m x y z) z)))
         :rule-classes nil))

(local (defthmz m3
         (implies (in z x)
                  (not (equal (m x y z) x)))
         :rule-classes nil))

(local (defthmz m4
         (or (equal (m x y z) x)
             (equal (m x y z) y)
             (equal (m x y z) z))
         :hints (("Goal"
                  :use ((:instance min-in-1
                                   (z (triple x y z))))
                  :in-theory (disable min-in-1)))
         :rule-classes nil))

(defthmdz in-has-no-3-cycle ; needed for ordinals-closure-2

; Proof: Let i = (triple x y z) and consider m = (min-in i).  By min-in-2, m
; has no member that is in i.  But by min-in-1, m is x, y, or z, which
; respectively have as a member z, x, or y; yet these are all members of i, a
; contradiction.

  (implies (and (in x y)
                (in y z))
           (not (in z x)))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :use (m1 m2 m3 m4))))

(defthmz ordinals-closure-2-lemma-lemma

  (implies (and (in a b)
                (in b y))
           (not (in y a)))
  :hints (("Goal"
           :in-theory (enable in-has-no-3-cycle)))
  :rule-classes nil)

(defthmz ordinals-closure-2-lemma

; See the hand proof in ordinals-closure-2.

  (implies (and (in-is-linear x)
                (transitive x)
                (in y x)
                (in a b)
                (in b y))
           (in a y))
  :hints (("Goal"
           :use (ordinals-closure-2-lemma-lemma
                 (:instance in-is-linear-necc
                            (x a) (y y) (s x))))))

(defthmz ordinals-closure-2

; Proof.  Let a \in b \in y; we show a \in y.  Now b \in x by transitivity of
; x.  So a \in b \in x.  So a \in x by transitivity of x.  By linearity of x,
; since a, y \in x, then a \in y or y \in a.

; Suppose for a contradiction that y \in a.  Then y \in a \in b \in y.
; Consider z = (insert y (pair a b)) and m = (min-in z).  Then m is y, a, or b,
; and in each case we have a contradiction of min-in-2 since m then contains an
; element of z -- namely b, y, or a, respectively.

  (implies (and (in-is-linear x)
                (transitive x)
                (in y x))
           (transitive y))
  :hints (("Goal"
           :expand ((transitive y)
                    (subset (transitive-witness y) y)))))

(defthmz ordinals-closure
  (implies (and (ordinal-p x)
                (in y x))
           (ordinal-p y)))

(defthm ordinal-p-properties
  (implies (ordinal-p x)
           (and (in-is-linear x) (transitive x))))

(defthmz transitive-int2
  (implies (and (transitive x)
                (transitive y))
           (transitive (int2 x y)))
  :props (zfc diff$prop)
  :hints (("Goal" :expand ((transitive (int2 x y))
                           (subset (transitive-witness (int2 x y))
                                   (int2 x y))))))

(defthm in-is-linear-necc-rewrite
  (implies (and (in-is-linear s)
                (in x s)
                (in y s)
                (not (in x y))
                (not (in y x)))
           (equal (equal x y)
                  t))
  :hints (("Goal"
           :use in-is-linear-necc
           :in-theory (disable in-is-linear-necc))))

(in-theory (disable in-is-linear-necc))

(defthmz in-is-linear-int2
  (implies (and (in-is-linear x)
                (in-is-linear y))
           (in-is-linear (int2 x y)))
  :props (zfc diff$prop)
  :hints (("Goal" :expand ((in-is-linear (int2 x y))
                           (subset (in-is-linear-witness (int2 x y))
                                   (int2 x y))))))

(defthmz ordinal-p-int2
  (implies (and (ordinal-p x)
                (ordinal-p y))
           (ordinal-p (int2 x y)))
  :props (zfc diff$prop))

(in-theory (disable ordinal-p))

; https://proofwiki.org/wiki/Transitive_Set_is_Proper_Subset_of_Ordinal_iff_Element_of_Ordinal

; Start proof of ordinal-trichotomy.

(encapsulate
  ()

  (local (defthmz min-in-diff-is-member

; See the proof in the event, ordinal-proper-subset-is-element.  This is useful
; for ordinal-proper-subset-is-element and maybe others.

           (implies (and (subset b a)
                         (not (equal b a))
                         (equal c (min-in (diff a b))))
                    (in c a))
           :hints (("Goal" :use ((:instance equal-diff-0-is-subset
                                            (x a)
                                            (y b))
                                 (:instance min-in-1
                                            (z (diff a b))))))
           :props (zfc diff$prop)))

  (local (defthmz min-in-diff-is-not-member

; See the proof in the event, ordinal-proper-subset-is-element.  This is useful
; for ordinal-proper-subset-is-element and maybe others.

           (implies (and (subset b a)
                         (not (equal a b)))
                    (not (in (min-in (diff a b)) b)))
           :hints (("Goal"
                    :in-theory (enable equal-diff-0-is-subset)
                    :use ((:instance min-in-1
                                     (z (diff a b))))))
           :props (zfc diff$prop)))

  (local (defthmz ordinal-proper-subset-is-element-1-1-1
           (implies (and (ordinal-p b)
                         (subset b a)
                         (not (equal b a))
                         (in x b))
                    (not (in (min-in (diff a b)) x)))
           :props (zfc diff$prop)
           :otf-flg t
           :hints (("Goal"
                    :use min-in-diff-is-not-member
                    :in-theory (disable min-in-diff-is-not-member)))))

  (local (defthmz ordinal-proper-subset-is-element-1-1

; See the proof in the event, ordinal-proper-subset-is-element.  The argument
; for this lemma is as follows.  Assume (in x b).  Also (in x a) since (subset
; b a), and also (in (min-in (diff a b)) a) since (in (min-in (diff a b)) (diff
; a b)).  Since x and (min-in (diff a b)) are both in a and a is an ordinal,
; then we can apply trichotomy.  Since x is in b and (min-in (diff a b)) is in
; (diff a b), hence not in b, then (min-in (diff a b)) can't be in b; so
; (min-in (diff a b)) is not in or equal to x (since b is transitive).  So by
; trichotomy, (in x (min-in (diff a b))).

           (implies (and (ordinal-p a)
                         (ordinal-p b)
                         (subset b a)
                         (not (equal b a))
                         (in x b))
                    (in x (min-in (diff a b))))
           :props (zfc diff$prop)
           :otf-flg t
           :hints (("Goal"
                    :use ((:instance in-is-linear-necc
                                     (s a)
                                     (x x)
                                     (y (min-in (diff a b)))))
                    :in-theory (disable in-is-linear-necc
                                        in-is-linear-necc-rewrite))))
         )

  (local (defthmz ordinal-proper-subset-is-element-1
            (implies (and (ordinal-p a)
                          (ordinal-p b)
                          (subset b a)
                          (not (equal b a)))
                     (subset b (min-in (diff a b))))
            :hints (("Goal" :expand ((subset b (min-in (diff a b))))))
            :props (zfc diff$prop))
          )

  (local (defthmz ordinal-proper-subset-is-element-2-1

; See the proof in the event, ordinal-proper-subset-is-element.

           (implies (and (ordinal-p a)
                         (ordinal-p b)
                         (subset b a)
                         (not (equal b a))
                         (in z (min-in (diff a b))))
                    (in z b))
           :hints (("Goal"
                    :use ((:instance min-in-2
                                     (a z)
                                     (z (diff a b))))
                    :in-theory (disable min-in-2)))
           :props (zfc diff$prop)))

  (local (defthmz ordinal-proper-subset-is-element-2

; See the proof in the event, ordinal-proper-subset-is-element.

           (implies (and (ordinal-p a)
                         (ordinal-p b)
                         (subset b a)
                         (not (equal b a)))
                    (subset (min-in (diff a b)) b))
           :hints (("Goal" :expand ((subset (min-in (diff a b)) b))))
           :props (zfc diff$prop)))

  (local (defthmz ordinal-proper-subset-is-element-3

; See the proof in the event, ordinal-proper-subset-is-element.

           (implies (and (ordinal-p a)
                         (ordinal-p b)
                         (subset b a)
                         (not (equal b a)))
                    (equal (min-in (diff a b)) b))
           :props (zfc diff$prop)
           :hints (("Goal" :in-theory (enable extensionality-rewrite)))
           :rule-classes nil))

  (defthmz ordinal-proper-subset-is-element

; Proof: Let x be minimal \in a such that x \notin b.  It suffices to show that
; b = x, since then (in b a) since (in x a).  Clearly (subset x b) since if (in
; z x) then (in z a) so by minimality of x, (in z b).

; To show (subset b x), let z \in b.  Since by hypothesis, (subset b a), so z
; \in a.  Since both z \in a and x \in a, then by linearity of a, either (in z
; x), (in x z), or (equal x z).  By transitivity of b, (in x z) contradicts x
; \notin b.  And of course (equal x z) contradicts x \notin b since z \in b.
; So by linearity of a, (in z x).

    (implies (and (ordinal-p a)
                  (ordinal-p b)
                  (subset b a)
                  (not (equal b a)))
             (in b a))
    :hints (("Goal" :use ordinal-proper-subset-is-element-3))
    :props (zfc diff$prop)))

(defthmz ordinal-trichotomy-lemma-1

; See the proof of ordinal-trichotomy in that event.

  (implies (and (ordinal-p a)
                (ordinal-p b)
                (not (in a b))
                (not (in b a))
                (not (subset a b))
                (not (subset b a))
                (not (equal a b)))
           (in (int2 a b) a))
  :props (zfc diff$prop)
  :hints (("Goal"
           :use ((:instance ordinal-proper-subset-is-element
                            (b (int2 a b))
                            (a a)))
           :in-theory (disable ordinal-proper-subset-is-element)))
  :rule-classes nil
  :otf-flg t)

(defthmz ordinal-trichotomy-lemma-2
  (implies (in (int2 a b) a)
           (not (in (int2 a b) b)))
  :props (zfc diff$prop)
  :hints (("Goal"
           :use ((:instance in-irreflexive (x (int2 a b))))
           :in-theory (disable in-irreflexive))))

(defthmz ordinal-trichotomy

; Proof.  First suppose (subset b a) or (subset a b); wlog, say it's the
; former.  If (equal a b) then we are done.  Otherwise by
; ordinal-proper-subset-is-element, (in a b) and we are done.

; So suppose neither (subset b a) nor (subset a b).  Let c = (int2 a b).  Then
; c is an ordinal by ordinal-p-int2, and c is a proper subset of both a and b.
; Therefore (in c a) and (in c b).  Hence (in c c), contradicting
; in-irreflexive.

  (implies (and (ordinal-p a)
                (ordinal-p b)
                (not (in a b))
                (not (in b a)))
           (equal (equal a b)
                  t))
  :otf-flg t
  :props (zfc diff$prop)
  :hints (("Goal"
           :in-theory (enable int2-commutative)
           :cases ((subset a b) (subset b a))
           :use (ordinal-trichotomy-lemma-1
                 (:instance ordinal-trichotomy-lemma-1
                            (a b)
                            (b a))))))
