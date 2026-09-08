; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
;   with contributions as noted below from Claude Code Opus 4.8, max effort.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "projects/set-theory/topology/subspace" :dir :system)
(include-book "projects/set-theory/topology/compact" :dir :system)

;;;<<The supporting events below, and the :props on the final theorem, were
;;;  added by Claude Code (Opus 4.8, max effort) to make this book certify.
;;;
;;;  Theorem: a closed subspace of a compact space is compact.
;;;
;;;  Proof outline.  Let c be an open cover of (subspace s tp).  Each open set
;;;  of the subspace is the trace (int2 w s) of an open set w of tp, so we
;;;  "lift" c to a family (csc-lift) of open sets of tp, and add the complement
;;;  (diff (union tp) s) of s -- which is open because s is closed -- to get an
;;;  open cover (csc-cover) of tp.  Compactness of tp yields a finite subcover
;;;  (csc-fsc); removing the complement gives csc-fsc1, and mapping its members
;;;  back through (inverse subspace-fn) gives a finite subfamily (csc-sub) of c
;;;  whose union is s = (union (subspace s tp)).  Hence (subspace s tp) is
;;;  compact.>>

; ----------------------------------------------------------------------------
; (union (subspace s tp)) = s, since s = (int2 (union tp) s) is the largest
; open set of the subspace.  (The two inclusions: (union (subspace s tp)) is a
; subset of s by tpp-union-subspace-1-1, and s itself is an open set of the
; subspace by in-subspace-suff.)
; ----------------------------------------------------------------------------

(defthmz union-subspace
  (implies (and (tpp tp) (subset s (union tp)))
           (equal (union (subspace s tp)) s))
  :hints (("Goal"
           :in-theory (enable extensionality subspace int2-when-subset-commuted)
           :use ((:instance tpp-union-subspace-1-1 (wit (domain (subspace-fn s tp))))
                 (:instance in-subspace-suff (s2 s) (w (union tp)))
                 (:instance in-implies-subset-union (x s) (s (subspace s tp))))))
  :props (zfc subspace-fn$prop domain$prop prod2$prop diff$prop))

; ----------------------------------------------------------------------------
; The lift of the subspace cover c, and the resulting open cover of tp.
; ----------------------------------------------------------------------------

; The open sets of tp that "lift" the subspace cover c, via the subspace-fn
; relation (which pairs each subspace set (int2 w s) with such a w).
(defund csc-lift (c s tp)
  (image (restrict (subspace-fn s tp) c)))

; An open cover of tp: the lifts together with the complement of s.
(defund csc-cover (c s tp)
  (union2 (csc-lift c s tp)
          (singleton (diff (union tp) s))))

; Forward: a lifted open w is in tp, and (int2 w s) is one of the cover sets in c.
(defthmz in-csc-lift-implies
  (implies (in w (csc-lift c s tp))
           (and (in w tp)
                (in (int2 w s) c)))
  :hints (("Goal"
           :in-theory (e/d (csc-lift restrict$comprehension subspace-fn$comprehension in-prod2)
                           (in-image-necc))
           :use ((:instance in-image-necc
                            (x w)
                            (f (restrict (subspace-fn s tp) c))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop))

; Reverse: if c0 in c is (int2 w s) for an open w of tp, then w is a lift.
(defthmz in-csc-lift-suff
  (implies (and (in c0 c)
                (in w tp)
                (equal (int2 w s) c0))
           (in w (csc-lift c s tp)))
  :hints (("Goal"
           :in-theory (e/d (csc-lift restrict$comprehension subspace-fn$comprehension
                                     in-prod2 in-powerset)
                           (in-image-suff))
           :use ((:instance in-image-suff
                            (p (cons c0 w))
                            (y w)
                            (r (restrict (subspace-fn s tp) c))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz subset-csc-lift-tp
  (subset (csc-lift c s tp) tp)
  :hints (("Goal" :in-theory (enable subset)
           :use ((:instance in-csc-lift-implies
                            (w (subset-witness (csc-lift c s tp) tp))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop))

; Each set c0 of the subspace cover is covered by its lift: c0 = (int2 w s) for
; the open w = (subspace-wit c0 s tp) of tp, and c0 is a subset of w in csc-lift.
(defthmz csc-lift-covers-c0
  (implies (and (tpp tp)
                (open-cover c (subspace s tp))
                (in c0 c))
           (subset c0 (union (csc-lift c s tp))))
  :hints (("Goal"
           :in-theory (enable open-cover subset in-int2)
           :use ((:instance in-subspace-necc (s2 c0))
                 (:instance in-subspace-wit-tp (w1 c0))
                 (:instance in-csc-lift-suff (w (subspace-wit c0 s tp)))
                 (:instance in-implies-subset-union
                            (x (subspace-wit c0 s tp))
                            (s (csc-lift c s tp))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; Hence s = (union c) is covered by the union of the lifts.
(defthmz subset-s-union-csc-lift
  (implies (and (tpp tp) (subset s (union tp)) (open-cover c (subspace s tp)))
           (subset s (union (csc-lift c s tp))))
  :hints (("Goal"
           :in-theory (e/d (subset open-cover) (in-union))
           :expand ((in-in (subset-witness s (union (csc-lift c s tp))) c))
           :use (union-subspace
                 (:instance in-union
                            (a (subset-witness s (union (csc-lift c s tp)))) (x c))
                 (:instance csc-lift-covers-c0
                            (c0 (in-in-witness (subset-witness s (union (csc-lift c s tp))) c)))
                 (:instance subset-preserves-in-1
                            (a (subset-witness s (union (csc-lift c s tp))))
                            (x (in-in-witness (subset-witness s (union (csc-lift c s tp))) c))
                            (y (union (csc-lift c s tp)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz subset-csc-cover-tp
  (implies (closed s tp)
           (subset (csc-cover c s tp) tp))
  :hints (("Goal" :in-theory (enable csc-cover closed subset-union2 subset-pair singleton)
           :use subset-csc-lift-tp))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop))

(defthmz subset-csc-lift-csc-cover
  (subset (csc-lift c s tp) (csc-cover c s tp))
  :hints (("Goal" :in-theory (enable csc-cover)))
  :props (zfc))

(defthmz in-comp-csc-cover
  (in (diff (union tp) s) (csc-cover c s tp))
  :hints (("Goal" :in-theory (enable csc-cover in-union2 in-pair singleton)))
  :props (zfc))

(defthmz subset-s-union-csc-cover
  (implies (and (tpp tp) (subset s (union tp)) (open-cover c (subspace s tp)))
           (subset s (union (csc-cover c s tp))))
  :hints (("Goal"
           :use (subset-s-union-csc-lift subset-csc-lift-csc-cover
                 (:instance union-monotone (s1 (csc-lift c s tp)) (s2 (csc-cover c s tp)))
                 (:instance subset-transitivity
                            (x s) (y (union (csc-lift c s tp))) (z (union (csc-cover c s tp)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz subset-comp-union-csc-cover
  (subset (diff (union tp) s) (union (csc-cover c s tp)))
  :hints (("Goal" :use (in-comp-csc-cover
                        (:instance in-implies-subset-union
                                   (x (diff (union tp) s)) (s (csc-cover c s tp))))))
  :props (zfc))

(defthmz subset-union-csc-cover-tp
  (implies (closed s tp)
           (subset (union (csc-cover c s tp)) (union tp)))
  :hints (("Goal" :use (subset-csc-cover-tp
                        (:instance union-monotone (s1 (csc-cover c s tp)) (s2 tp)))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop))

; Every point of tp is either in s (covered by the lifts) or in the complement
; of s; so the cover covers tp.
(defthmz subset-union-tp-csc-cover
  (implies (and (tpp tp) (closed s tp) (open-cover c (subspace s tp)))
           (subset (union tp) (union (csc-cover c s tp))))
  :hints (("Goal"
           :in-theory (enable subset closed in-diff)
           :use (subset-s-union-csc-cover subset-comp-union-csc-cover
                 (:instance subset-preserves-in-1
                            (a (subset-witness (union tp) (union (csc-cover c s tp))))
                            (x s) (y (union (csc-cover c s tp))))
                 (:instance subset-preserves-in-1
                            (a (subset-witness (union tp) (union (csc-cover c s tp))))
                            (x (diff (union tp) s)) (y (union (csc-cover c s tp)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz union-csc-cover
  (implies (and (tpp tp) (closed s tp) (open-cover c (subspace s tp)))
           (equal (union (csc-cover c s tp)) (union tp)))
  :hints (("Goal" :in-theory (enable extensionality)
           :use (subset-union-csc-cover-tp subset-union-tp-csc-cover)))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz open-cover-csc-cover
  (implies (and (tpp tp) (closed s tp) (open-cover c (subspace s tp)))
           (open-cover (csc-cover c s tp) tp))
  :hints (("Goal" :in-theory (enable open-cover)
           :use (subset-csc-cover-tp union-csc-cover)))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; ----------------------------------------------------------------------------
; A finite subcover of tp (from compactness), and its image back in the subspace.
; ----------------------------------------------------------------------------

; A finite subcover of tp, from compactness of tp.
(defund csc-fsc (c s tp)
  (exists-finite-subcover-witness (csc-cover c s tp) tp))

(defthmdz finite-subcover-csc-fsc
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (and (equal (union (csc-fsc c s tp)) (union tp))
                (subset (csc-fsc c s tp) (csc-cover c s tp))
                (finite (csc-fsc c s tp))))
  :hints (("Goal"
           :in-theory (e/d (csc-fsc exists-finite-subcover) (compact-necc))
           :use (open-cover-csc-cover
                 (:instance compact-necc (c (csc-cover c s tp)) (tp tp)))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; Remove the complement of s from the finite subcover of tp.
(defund csc-fsc1 (c s tp)
  (diff (csc-fsc c s tp)
        (singleton (diff (union tp) s))))

; Map the trimmed subcover back to open sets of the subspace, via inverse
; subspace-fn (each open w of tp maps to its trace (int2 w s), one of the c-sets).
(defund csc-sub (c s tp)
  (image (restrict (inverse (subspace-fn s tp))
                   (csc-fsc1 c s tp))))

; The trimmed subcover consists of lifts (its members are open sets of tp whose
; traces lie in c).
(defthmz subset-csc-fsc1-csc-lift
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (subset (csc-fsc1 c s tp) (csc-lift c s tp)))
  :hints (("Goal"
           :in-theory (enable csc-fsc1 csc-cover subset in-diff in-union2 in-pair singleton)
           :use (finite-subcover-csc-fsc
                 (:instance subset-preserves-in-1
                            (a (subset-witness (csc-fsc1 c s tp) (csc-lift c s tp)))
                            (x (csc-fsc c s tp))
                            (y (csc-cover c s tp))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; Reverse: each trimmed open w (in tp) contributes its trace (int2 w s) to csc-sub.
(defthmz in-csc-sub-suff
  (implies (and (in w (csc-fsc1 c s tp))
                (in w tp))
           (in (int2 w s) (csc-sub c s tp)))
  :hints (("Goal"
           :in-theory (e/d (csc-sub restrict$comprehension in-inverse
                                    subspace-fn$comprehension in-prod2 in-powerset)
                           (in-image-suff))
           :use ((:instance in-image-suff
                            (p (cons w (int2 w s)))
                            (y (int2 w s))
                            (r (restrict (inverse (subspace-fn s tp)) (csc-fsc1 c s tp)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; csc-sub is a subfamily of the original cover c.
(defthmz subset-csc-sub-c
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (subset (csc-sub c s tp) c))
  :hints (("Goal"
           :in-theory (e/d (csc-sub subset restrict$comprehension in-inverse
                                    subspace-fn$comprehension in-prod2)
                           (in-image-necc in-csc-lift-implies))
           :use (subset-csc-fsc1-csc-lift
                 (:instance in-image-necc
                            (x (subset-witness (csc-sub c s tp) c))
                            (f (restrict (inverse (subspace-fn s tp)) (csc-fsc1 c s tp))))
                 (:instance subset-preserves-in-1
                            (a (apply (inverse (restrict (inverse (subspace-fn s tp)) (csc-fsc1 c s tp)))
                                      (subset-witness (csc-sub c s tp) c)))
                            (x (csc-fsc1 c s tp))
                            (y (csc-lift c s tp)))
                 (:instance in-csc-lift-implies
                            (w (apply (inverse (restrict (inverse (subspace-fn s tp)) (csc-fsc1 c s tp)))
                                      (subset-witness (csc-sub c s tp) c)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; (inverse subspace-fn) is a function: each open w of tp determines its trace
; (int2 w s) uniquely.  Needed for finiteness of csc-sub.
(defthmz funp-inverse-subspace-fn
  (funp (inverse (subspace-fn s tp)))
  :hints (("Goal"
           :expand ((funp (inverse (subspace-fn s tp))))
           :in-theory (enable in-inverse subspace-fn$comprehension in-prod2)))
  :props (zfc subspace-fn$prop prod2$prop domain$prop inverse$prop))

(defthmz finite-csc-sub
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (finite (csc-sub c s tp)))
  :hints (("Goal"
           :in-theory (enable csc-sub csc-fsc1)
           :use finite-subcover-csc-fsc))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop rcompose$prop))

; ----------------------------------------------------------------------------
; (union csc-sub) = s = (union (subspace s tp)).
; ----------------------------------------------------------------------------

(defthmz subset-union-csc-sub-s
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (subset (union (csc-sub c s tp)) s))
  :hints (("Goal"
           :in-theory (enable open-cover closed)
           :use (subset-csc-sub-c union-subspace
                 (:instance union-monotone (s1 (csc-sub c s tp)) (s2 c))
                 (:instance subset-transitivity
                            (x (union (csc-sub c s tp))) (y (union c)) (z s)))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; Each point of s lies in some trimmed open w (covering tp) other than the
; complement of s, hence in (int2 w s) in csc-sub.
(defthmz csc-sub-covers-s-point
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp))
                (in x s))
           (in x (union (csc-sub c s tp))))
  :hints (("Goal"
           :in-theory (enable closed in-int2 in-diff csc-fsc1 singleton in-pair)
           :expand ((in-in x (csc-fsc c s tp)))
           :use (finite-subcover-csc-fsc
                 (:instance in-union (a x) (x (csc-fsc c s tp)))
                 (:instance subset-preserves-in-1 (a x) (x s) (y (union tp)))
                 subset-csc-fsc1-csc-lift
                 subset-csc-lift-tp
                 (:instance subset-preserves-in-1
                            (a (in-in-witness x (csc-fsc c s tp)))
                            (x (csc-fsc1 c s tp)) (y (csc-lift c s tp)))
                 (:instance subset-preserves-in-1
                            (a (in-in-witness x (csc-fsc c s tp)))
                            (x (csc-lift c s tp)) (y tp))
                 (:instance in-csc-sub-suff (w (in-in-witness x (csc-fsc c s tp))))
                 (:instance in-implies-subset-union
                            (x (int2 (in-in-witness x (csc-fsc c s tp)) s))
                            (s (csc-sub c s tp)))
                 (:instance subset-preserves-in-1
                            (a x)
                            (x (int2 (in-in-witness x (csc-fsc c s tp)) s))
                            (y (union (csc-sub c s tp)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz subset-s-union-csc-sub
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (subset s (union (csc-sub c s tp))))
  :hints (("Goal" :in-theory (enable subset)
           :use ((:instance csc-sub-covers-s-point
                            (x (subset-witness s (union (csc-sub c s tp))))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

(defthmz union-csc-sub
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (equal (union (csc-sub c s tp)) s))
  :hints (("Goal" :in-theory (enable extensionality)
           :use (subset-union-csc-sub-s subset-s-union-csc-sub)))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop))

; ----------------------------------------------------------------------------
; csc-sub is a finite subcover of (subspace s tp); hence the subspace is compact.
; ----------------------------------------------------------------------------

(defthmz exists-finite-subcover-csc
  (implies (and (tpp tp) (compact tp) (closed s tp) (open-cover c (subspace s tp)))
           (exists-finite-subcover c (subspace s tp)))
  :hints (("Goal"
           :in-theory (enable closed)
           :use ((:instance exists-finite-subcover-suff
                            (c2 (csc-sub c s tp)) (tp (subspace s tp)))
                 union-csc-sub union-subspace subset-csc-sub-c finite-csc-sub)))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop rcompose$prop))

(defthmz closed-subspace-is-compact
  (implies (and (tpp tp)
                (compact tp)
                (closed s tp))
           (compact (subspace s tp)))
  :hints (("Goal"
           :in-theory (enable compact)
           :use ((:instance exists-finite-subcover-csc
                            (c (compact-witness (subspace s tp)))))))
  :props (zfc prod2$prop subspace-fn$prop domain$prop inverse$prop restrict$prop diff$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop rcompose$prop))
