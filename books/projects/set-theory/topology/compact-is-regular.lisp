; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "compact")
(include-book "normal")

; Start proof of compact-hausdorff-is-regular.

; Realize point-point-separation in a relation that associates each
; neighborhood of x with all open sets disjoint from that neighborhood.
(zsub pps (x tp) ; name, args
      p                                 ; x
      (prod2 tp tp)                     ; s
      (let ((s1 (car p))                ; u
            (s2 (cdr p)))
        (and (in x s1)
             (equal (int2 s1 s2) 0))))

(defund pps-cover (x c tp)

; Return an open cover of tp consisting of all open sets separable from x
; together with the complement of c.  It is a cover if tp is Hausdorff, because
; every point other than x is in an open set separable from x, and x is in the
; complement of c.

  (union2 (image (pps x tp))
          (singleton (diff (union tp) c))))

(defthmz open-cover-pps-cover-1
  (implies (closed c tp)
           (subset (pps-cover x c tp) tp))
  :hints (("Goal"
           :in-theory (enable pps-cover)
           :restrict ((subset-image ((a tp))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop))

(defthmz open-cover-pps-cover-2-1
  (implies (and (tpp tp)
                (closed c tp))
           (subset (union (pps-cover x c tp))
                   (union tp)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

(encapsulate
  ()

  (local (defthmz in-in-union2-1
           (implies (in-in x (union2 s1 s2))
                    (or (in-in x s1)
                        (in-in x s2)))
           :hints (("Goal" :expand ((in-in x (union2 s1 s2)))))
           :rule-classes nil))

  (local (defthmz in-in-union2-2
           (implies (or (in-in x s1)
                        (in-in x s2))
                    (in-in x (union2 s1 s2)))
           :hints (("Goal" :expand ((in-in x s1) (in-in x s2))))
           :rule-classes nil))

  (defthmz in-in-union2
    (equal (in-in x (union2 s1 s2))
           (or (in-in x s1)
               (in-in x s2)))
    :hints (("Goal" :use (in-in-union2-1 in-in-union2-2)))))

(defund hausdorff-pair (x y tp)
  (mv-let (s1 s2) ; x \in s1, y \in s2, s1 and s2 disjoint open sets of tp
    (point-point-separable-witness x y tp)
    (cons s1 s2)))

(defthmdz in-in-image-suff
  (implies (and (in p r)
                (consp p)
                (in x (cdr p)))
           (in-in x (image r)))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz hausdorff-1-1
  (implies (and (tpp tp)
                (point-point-separable x y tp)
                (in x (union tp))
                (in y (union tp))
                (force (not (equal x y))))
           (in (hausdorff-pair x y tp)
               (pps x tp)))
  :hints (("Goal" :in-theory (enable point-point-separable hausdorff-pair)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

(defthmz hausdorff-1
  (implies (and (tpp tp)
                (hausdorff tp)
                (in x (union tp))
                (in y (union tp))
                (force (not (equal x y))))
           (in (hausdorff-pair x y tp)
               (pps x tp)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

(encapsulate
  ()

  (local (defthmz hausdorff-2-1
           (implies (and (tpp tp)
                         (point-point-separable x y tp)
                         (in x (union tp))
                         (in y (union tp))
                         (force (not (equal x y))))
                    (in y
                        (cdr (hausdorff-pair x y tp))))
           :hints (("Goal" :in-theory (enable point-point-separable hausdorff-pair)))
           :props (zfc prod2$prop pps$prop domain$prop inverse$prop
                       diff$prop)))

  (defthmz hausdorff-2
    (implies (and (tpp tp)
                  (hausdorff tp)
                  (in x (union tp))
                  (in y (union tp))
                  (force (not (equal x y))))
             (in y
                 (cdr (hausdorff-pair x y tp))))
    :props (zfc prod2$prop pps$prop domain$prop inverse$prop
                diff$prop)))

(defthmdz in-in-e-pair-1
  (implies (in-in e (pair x y))
           (or (in e x)
               (in e y)))
  :hints (("Goal" :in-theory (enable in-in))))

(defthmdz in-in-e-pair-2
  (implies (or (in e x)
               (in e y))
           (in-in e (pair x y)))
  :hints (("Goal"
           :use ((:instance in-in-suff
                            (a e)
                            (y (if (in e x) x y))
                            (x (pair x y))))
           :in-theory (disable in-in-suff))))

(defthmz in-in-e-pair
; The slighly odd name here is chosen becuase there is already in-in-pair in
; zfns.lisp, which is quite different.
  (equal (in-in e (pair x y))
         (or (in e x)
             (in e y)))
  :hints (("Goal" :use (in-in-e-pair-1 in-in-e-pair-2))))

(defthmz open-cover-pps-cover-2-2
  (implies (and (tpp tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (subset (union tp)
                   (union (pps-cover x c tp))))
  :instructions
  ((:in-theory (enable pps-cover))
   (:bash ("Goal" :expand ((:free (x) (subset (union tp) x)))))
   (:contrapose 14)
   (:rewrite in-in-image-suff
             ((p (hausdorff-pair
                  x
                  (subset-witness (union tp)
                                  (union (union2 (image (pps x tp))
                                                 (pair (diff (union tp) c)
                                                       (diff (union tp) c)))))
                  tp))))
   :prove :prove)
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

(defthmz open-cover-pps-cover-2
  (implies (and (tpp tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (equal (union (pps-cover x c tp))
                  (union tp)))
  :hints (("Goal" :in-theory (enable extensionality)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

(defthmdz open-cover-pps-cover
  (implies (and (tpp tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (open-cover (pps-cover x c tp) tp))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

; Start proof of compact-hausdorff-is-regular-1.  Below, "fsc" stands for
; "finite subcover".

(include-book "finite-intersection-closure")

(defund fsc0 (x c tp)

; For a point x and closed set c of tp, pick a finite subcover of the pps-cover
; consisting of the complement of c together with all open sets separatable
; from x extended by the complement of c.

  (let ((cover (pps-cover x c tp)))
    (exists-finite-subcover-witness cover tp)))

(defthmdz finite-subcover-fsc0
  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (and (equal (union (fsc0 x c tp)) (union tp))
                (subset (fsc0 x c tp) (pps-cover x c tp))
                (finite (fsc0 x c tp))))
  :hints (("Goal"
           :in-theory (e/d (fsc0 exists-finite-subcover)
                           (compact-necc))
           :use (open-cover-pps-cover
                 (:instance compact-necc
                            (c (pps-cover x c tp))
                            (tp tp)))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

(defund fsc1 (x c tp)

; Return the result of removing the complement of c from our finite subcover
; fsc0, which produces a finite open cover of c.  The intersection of fsc1 is
; thus an open set that includes c.  Then we will map fsc1 back, via the
; relation pps, to a corresponding family ssx of open sets containing x, whose
; union is disjoint from the aforementioned intersection.

  (diff (fsc0 x c tp)
        (singleton (diff (union tp) c))))

(defthmz finite-fsc1
  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (finite (fsc1 x c tp)))
  :hints (("Goal"
           :in-theory (enable fsc1)
           :use finite-subcover-fsc0))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))

(defund ssx (x c tp)

; This is the open cover of x that is described in the comment on fsc1.

  (image (restrict (skolem (inverse (pps x tp)))
                   (fsc1 x c tp))))

(include-book "../finite/finite-image")

(defthmz finite-ssx
  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (finite (ssx x c tp)))
  :hints (("Goal"
           :in-theory (enable ssx)
           :use finite-subcover-fsc0))
  :props (zfc pps$prop diff$prop skolem$prop zfns-prop phoenix$prop
              identity-fun$prop compose$prop swap$prop restrict$prop
;;;<<Note that rcompose-prop was added by Claude, Opus 6.8 max effort.>>
              rcompose$prop))

(defund sx (x c tp)
  (intersection (ssx x c tp)))

#|

I gave the skip-proofs event below to claude code max effort, Opus
4.8, with the following instructions:

  Please remove the skip-proofs in
  ~/claude-code/acl2-mcp/work/set-theory/claude.lsp by adding
  appropriate lemmas, :hints, and :props.

The result is below.  After this comment is a version that I very
easily produced by hand after cleaning up that perfectly acceptable
result from claude.

(skip-proofs
(defthmz subset-ssx-tp

; Suppose under the hypotheses that s \in (ssx x c tp).  So for some sy,
; <sy,s> \in (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp)). So
; <sy,s> \in (skolem (inverse (pps x tp))).  So
; <sy,s> \in (inverse (pps x tp)).  So
; <s,sy> \in (pps x tp).
; So s \in tp.

  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (subset (ssx x c tp) tp))
  :hints (("Goal"
           :in-theory (enable fsc1 ssx)
           :use finite-subcover-fsc0))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop skolem$prop))
)

; Claude's result:

; (restrict f s) is a subset of f.
(defthmz subset-restrict
  (subset (restrict f s) f)
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc restrict$prop))

; The inverse of (pps x tp) consists of pairs <s2,s1> where <s1,s2> is in
; (pps x tp), hence in (prod2 tp tp); so both s1 and s2 are in tp, and thus
; <s2,s1> is in (prod2 tp tp).
(defthmz subset-inverse-pps
  (subset (inverse (pps x tp)) (prod2 tp tp))
  :hints (("Goal" :in-theory (enable subset in-inverse in-prod2)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop))

(defthmz subset-ssx-tp

; Suppose under the hypotheses that s \in (ssx x c tp).  So for some sy,
; <sy,s> \in (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp)). So
; <sy,s> \in (skolem (inverse (pps x tp))).  So
; <sy,s> \in (inverse (pps x tp)).  So
; <s,sy> \in (pps x tp).
; So s \in tp.

; Dually (at the level of sets), (ssx x c tp) is the image of a relation that,
; by subset-restrict, subset-skolem, and subset-inverse-pps, is a subset of
; (prod2 tp tp); so by subset-image its image is a subset of tp.

  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (subset (ssx x c tp) tp))
  :hints (("Goal"
           :in-theory (e/d (ssx)
                           (subset-image subset-restrict subset-skolem
                            subset-inverse-pps subset-transitivity))
           :use ((:instance subset-image
                            (r (restrict (skolem (inverse (pps x tp)))
                                         (fsc1 x c tp)))
                            (a tp) (b tp))
                 (:instance subset-restrict
                            (f (skolem (inverse (pps x tp))))
                            (s (fsc1 x c tp)))
                 (:instance subset-skolem
                            (r (inverse (pps x tp))))
                 subset-inverse-pps
                 (:instance subset-transitivity
                            (x (restrict (skolem (inverse (pps x tp)))
                                         (fsc1 x c tp)))
                            (y (skolem (inverse (pps x tp))))
                            (z (inverse (pps x tp))))
                 (:instance subset-transitivity
                            (x (restrict (skolem (inverse (pps x tp)))
                                         (fsc1 x c tp)))
                            (y (inverse (pps x tp)))
                            (z (prod2 tp tp))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop skolem$prop restrict$prop))
|#

(defthmz subset-ssx-tp

; Suppose under the hypotheses that s \in (ssx x c tp).  So for some sy,
; <sy,s> \in (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp)). So
; <sy,s> \in (skolem (inverse (pps x tp))).  So
; <sy,s> \in (inverse (pps x tp)).  So
; <s,sy> \in (pps x tp).
; So s \in tp.

; Dually (at the level of sets), (ssx x c tp) is the image of a relation that,
; by subset-restrict, subset-skolem, and subset-inverse-pps, is a subset of
; (prod2 tp tp); so by subset-image its image is a subset of tp.

  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (subset (ssx x c tp) tp))
  :hints (("Goal"
           :in-theory (e/d (ssx) (subset-image))
           :use ((:instance subset-image
                            (r (restrict (skolem (inverse (pps x tp)))
                                         (fsc1 x c tp)))
                            (a tp) (b tp)))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop skolem$prop restrict$prop))

(defthmdz in-sx-tp
  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (closed c tp)
                (not (in x c))
                (in x (union tp)))
           (in (sx x c tp) tp))
  :hints (("Goal"
           :in-theory (enable sx)))
  :props (pps$prop diff$prop skolem$prop intersection$prop zfns-prop
                   phoenix$prop identity-fun$prop compose$prop swap$prop
                   restrict$prop
;;;<<Note that rcompose-prop was added by Claude, Opus 6.8 max effort.>>
                   rcompose$prop))

;;;<<Begin proof by Claude, Opus 6.8 max effort, of in-x-sx
;;;  (including comments just below).  Extra :props added
;;;  by Claude for in-x-sx are (skolem$prop intersection$prop restrict$prop).>>

; ----------------------------------------------------------------------------
; Proof of in-x-sx: x is in (sx x c tp) = (intersection (ssx x c tp)).
;
; This requires (a) x is in every member of (ssx x c tp) and (b) (ssx x c tp) is
; non-empty.  Part (b), and hence in-x-sx, requires the hypothesis (not (equal c
; 0)): when c is empty, the finite subcover fsc0 can consist solely of the
; complement of c, so fsc1 -- and hence ssx -- is empty, (sx x c tp) is
; (intersection 0) = 0, and x is not in it.  The c=0 case is handled separately
; in compact-hausdorff-is-regular-1 below.
; ----------------------------------------------------------------------------

(defthmz union-pair-same
  (equal (union (pair x x)) x)
  :hints (("Goal"
           :in-theory (enable subset in-union in-in-e-pair)
           :use ((:instance extensionality (x (union (pair x x))) (y x)))))
  :props (zfc))

; (a) x is in every member of (ssx x c tp).  For s in (ssx x c tp), some sy maps
; to s under (skolem (inverse (pps x tp))), so <s,sy> is in (pps x tp), whence x
; is in s (the first pps coordinate).
(defthmz in-x-ssx-member
  (implies (in s (ssx x c tp))
           (in x s))
  :hints (("Goal"
           :in-theory (e/d (ssx restrict$comprehension pps$comprehension in-inverse)
                           (in-image-necc))
           :use ((:instance in-image-necc
                            (x s)
                            (f (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp))))
                 (:instance subset-skolem (r (inverse (pps x tp)))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop restrict$prop))

; (b), step 1: fsc1 is non-empty when c is non-empty.  If (fsc1 x c tp) = 0 then
; fsc0 is a subset of {(diff (union tp) c)}, so (union tp) = (union fsc0) is a
; subset of (diff (union tp) c), forcing c = 0.
(defthmz fsc1-not-empty
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)) (not (equal c 0)))
           (not (equal (fsc1 x c tp) 0)))
  :hints (("Goal"
           :in-theory (enable fsc1 closed union-pair-same in-diff)
           :use (finite-subcover-fsc0
                 (:instance diff-is-0-implies-subset
                            (x (fsc0 x c tp))
                            (y (pair (diff (union tp) c) (diff (union tp) c))))
                 (:instance union-monotone
                            (s1 (fsc0 x c tp))
                            (s2 (pair (diff (union tp) c) (diff (union tp) c))))
                 (:instance min-in-1 (z c))
                 (:instance subset-preserves-in-1
                            (a (min-in c)) (x c) (y (union tp)))
                 (:instance subset-preserves-in-1
                            (a (min-in c)) (x (union tp)) (y (diff (union tp) c))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

; (b), step 2: every member of fsc1 lies in (image (pps x tp)), the domain of
; (skolem (inverse (pps x tp))).
(defthmz subset-fsc1-image-pps
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)))
           (subset (fsc1 x c tp) (image (pps x tp))))
  :hints (("Goal"
           :in-theory (enable fsc1 pps-cover subset in-diff in-union2 in-pair)
           :use (finite-subcover-fsc0
                 (:instance subset-preserves-in-1
                            (a (subset-witness (fsc1 x c tp) (image (pps x tp))))
                            (x (fsc0 x c tp))
                            (y (pps-cover x c tp))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

; (b): ssx is non-empty when c is non-empty.
(defthmz ssx-not-empty
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)) (not (equal c 0)))
           (not (equal (ssx x c tp) 0)))
  :hints (("Goal"
           :in-theory (enable ssx domain-skolem domain-inverse)
           :use (fsc1-not-empty
                 subset-fsc1-image-pps
                 (:instance min-in-1 (z (fsc1 x c tp)))
                 (:instance subset-preserves-in-1
                            (a (min-in (fsc1 x c tp))) (x (fsc1 x c tp)) (y (image (pps x tp))))
                 (:instance domain-restrict-3
                            (x (min-in (fsc1 x c tp)))
                            (f (skolem (inverse (pps x tp))))
                            (s (fsc1 x c tp)))
                 (:instance in-apply-image
                            (r (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp)))
                            (x (min-in (fsc1 x c tp)))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop restrict$prop))

(defthmz in-x-sx

; (The following are my original comments, before Claude removed the skip-proofs.)

; Suppose the hypotheses.  It suffices to show that x \in s for arbitrary s \in
; (ssx x c tp).  The proof is now very similar to the proof of subset-ssx-tp;
; it proceeds as follows.

; Assume the hypotheses and that s \in (ssx x c tp).  So for some sy,
; <sy,s> \in (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp)). So
; <sy,s> \in (skolem (inverse (pps x tp))).  So
; <sy,s> \in (inverse (pps x tp)).  So
; <s,sy> \in (pps x tp).
; So x \in s.

  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp))
;;;<<The following hypothesis was added by Claude, Opus 6.8 max effort.>>
                (not (equal c 0)))
           (in x (sx x c tp)))
  :hints (("Goal"
           :in-theory (enable sx intersection$comprehension-improved)
           :expand ((in-all x (ssx x c tp)))
           :use ((:instance in-x-ssx-member (s (in-all-witness x (ssx x c tp))))
                 ssx-not-empty)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop
              skolem$prop intersection$prop restrict$prop))

;;;<<End proof by Claude, Opus 6.8 max effort, of in-x-sx.>>

;;;<<Begin proof by Claude, Opus 6.8 max effort, of compact-hausdorff-is-regular-1.
;;;  Note that the original :props only included:
;;;  (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop).>>

; ----------------------------------------------------------------------------
; Proof of compact-hausdorff-is-regular-1.  We separate x from c using s1 = (sx
; x c tp) and s2 = (union (fsc1 x c tp)).  We need: (sx x c tp) and (union (fsc1
; x c tp)) are open (in-sx-tp above, and union-fsc1-in-tp below); x is in (sx x
; c tp) (in-x-sx); c is a subset of (union (fsc1 x c tp)) (subset-c-union-fsc1);
; and they are disjoint (int2-sx-union-fsc1).  The disjointness is the heart:
; for sy in fsc1, the chosen s = (apply (skolem (inverse (pps x tp))) sy) is in
; ssx and satisfies (int2 s sy) = 0, while (sx x c tp), being the intersection
; of ssx, is a subset of s; so no point lies in both (sx x c tp) and sy.
; ----------------------------------------------------------------------------

; For sy in fsc1, <sy, (apply (skolem (inverse (pps x tp))) sy)> is in (inverse
; (pps x tp)) (the skolem choice property).
(defthmz inverse-pair-from-fsc1
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)) (in sy (fsc1 x c tp)))
           (in (cons sy (apply (skolem (inverse (pps x tp))) sy))
               (inverse (pps x tp))))
  :hints (("Goal"
           :in-theory (enable domain-inverse)
           :use (subset-fsc1-image-pps
                 (:instance subset-preserves-in-1
                            (a sy) (x (fsc1 x c tp)) (y (image (pps x tp))))
                 (:instance skolem-skolemizes (x sy) (r (inverse (pps x tp)))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop restrict$prop))

; Hence <(apply (skolem (inverse (pps x tp))) sy), sy> is in (pps x tp).
(defthmz pps-pair-from-fsc1
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)) (in sy (fsc1 x c tp)))
           (in (cons (apply (skolem (inverse (pps x tp))) sy) sy)
               (pps x tp)))
  :hints (("Goal"
           :use (inverse-pair-from-fsc1
                 (:instance in-inverse
                            (x (cons sy (apply (skolem (inverse (pps x tp))) sy)))
                            (r (pps x tp))))
           :in-theory (disable in-inverse pps$comprehension)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop restrict$prop)
  :rule-classes nil)

; That chosen open set is a member of ssx.
(defthmz apply-g-in-ssx
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)) (in sy (fsc1 x c tp)))
           (in (apply (skolem (inverse (pps x tp))) sy) (ssx x c tp)))
  :hints (("Goal"
           :in-theory (enable ssx domain-skolem domain-inverse)
           :use (subset-fsc1-image-pps
                 (:instance subset-preserves-in-1
                            (a sy) (x (fsc1 x c tp)) (y (image (pps x tp))))
                 (:instance domain-restrict-3
                            (x sy) (f (skolem (inverse (pps x tp)))) (s (fsc1 x c tp)))
                 (:instance apply-restrict
                            (f (skolem (inverse (pps x tp)))) (x (fsc1 x c tp)) (a sy))
                 (:instance in-apply-image
                            (r (restrict (skolem (inverse (pps x tp))) (fsc1 x c tp))) (x sy)))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop restrict$prop))

; The disjointness, pointwise: no p is in both (sx x c tp) and (union (fsc1 x c tp)).
(defthmz not-in-sx-and-union-fsc1
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp))
                (in p (sx x c tp)))
           (not (in p (union (fsc1 x c tp)))))
  :hints (("Goal"
           :in-theory (enable sx intersection$comprehension-improved in-union)
           :expand ((in-in p (fsc1 x c tp)))
           :use ((:instance apply-g-in-ssx (sy (in-in-witness p (fsc1 x c tp))))
                 (:instance pps-pair-from-fsc1 (sy (in-in-witness p (fsc1 x c tp))))
                 (:instance in-all-necc
                            (x p) (s (ssx x c tp))
                            (y (apply (skolem (inverse (pps x tp)))
                                      (in-in-witness p (fsc1 x c tp)))))
                 (:instance int2-non-empty
                            (a p)
                            (x (apply (skolem (inverse (pps x tp)))
                                      (in-in-witness p (fsc1 x c tp))))
                            (y (in-in-witness p (fsc1 x c tp)))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop
              restrict$prop intersection$prop))

(defthmz int2-sx-union-fsc1
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)))
           (equal (int2 (sx x c tp) (union (fsc1 x c tp))) 0))
  :hints (("Goal"
           :in-theory (enable in-int2)
           :use ((:instance min-in-1 (z (int2 (sx x c tp) (union (fsc1 x c tp)))))
                 (:instance not-in-sx-and-union-fsc1
                            (p (min-in (int2 (sx x c tp) (union (fsc1 x c tp)))))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop skolem$prop
              restrict$prop intersection$prop))

; (union (fsc1 x c tp)) is open: fsc1 is a finite family of open sets.
(defthmz in-fsc1-iff
  (equal (in e (fsc1 x c tp))
         (and (in e (fsc0 x c tp))
              (not (equal e (diff (union tp) c)))))
  :hints (("Goal" :in-theory (enable fsc1 in-diff in-pair)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

(defthmz subset-fsc1-tp
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)))
           (subset (fsc1 x c tp) tp))
  :hints (("Goal"
           :in-theory (enable fsc1 subset in-diff)
           :use (finite-subcover-fsc0
                 open-cover-pps-cover-1
                 (:instance subset-preserves-in-1
                            (a (subset-witness (fsc1 x c tp) tp))
                            (x (fsc0 x c tp)) (y (pps-cover x c tp)))
                 (:instance subset-preserves-in-1
                            (a (subset-witness (fsc1 x c tp) tp))
                            (x (pps-cover x c tp)) (y tp)))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

(defthmz union-fsc1-in-tp
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)))
           (in (union (fsc1 x c tp)) tp))
  :hints (("Goal"
           :in-theory (enable tpp)
           :use (subset-fsc1-tp
                 (:instance tpp-union-necc (tp2 (fsc1 x c tp))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

; c is covered by (union (fsc1 x c tp)): every point of c lies in some member of
; fsc0 other than the complement of c, hence in some member of fsc1.
(defthmz subset-c-union-fsc0
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)))
           (subset c (union (fsc0 x c tp))))
  :hints (("Goal"
           :in-theory (enable closed)
           :use (finite-subcover-fsc0)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

(defthmz subset-c-union-fsc1
  (implies (and (tpp tp) (compact tp) (hausdorff tp) (closed c tp)
                (not (in x c)) (in x (union tp)))
           (subset c (union (fsc1 x c tp))))
  :hints (("Goal"
           :in-theory (e/d (closed subset in-union in-diff in-fsc1-iff) (fsc1))
           :expand ((in-in (subset-witness c (union (fsc1 x c tp))) (fsc0 x c tp)))
           :use (subset-c-union-fsc0
                 (:instance subset-preserves-in-1
                            (a (subset-witness c (union (fsc1 x c tp))))
                            (x c) (y (union (fsc0 x c tp))))
                 (:instance in-in-suff
                            (a (subset-witness c (union (fsc1 x c tp))))
                            (x (fsc1 x c tp))
                            (y (in-in-witness (subset-witness c (union (fsc1 x c tp)))
                                              (fsc0 x c tp)))))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop))

(defthmz compact-hausdorff-is-regular-1

; (The following are my original comments, before Claude removed the
; skip-proofs, except that Claude added the last sentence.)

; Informal proof.  Assume the hypotheses.  Then (pps-cover x c tp) is an open
; cover of tp, so it has a finite subcover ("fsc"), fsc0.  Let fsc1 be the
; result of removing (diff (union tp) c) from fsc0.  Let fc = (skolem (inverse
; (pps x tp))), i.e., fc picks for each y \in (image (pps x tp)) some x such
; that <x,y> \in (pps x tp).  Let ssx = (image (restrict fc fsc1)); thus ssx is
; finite and contained in tp.  Let sx = (intersection ssx).  Then x \in sx \in
; tp, sx is disjoint from (union fsc1) \in tp, and c \subset (union fsc1) \in
; tp.  When c is empty, the open sets (union tp) and 0 separate x from c.

  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp)
                (in x (union tp))
                (not (in x c))
                (subset c (union tp))
                (closed c tp))
           (point-set-separable x c tp))
  :hints (("Goal"
           :in-theory (enable tpp)
           :cases ((equal c 0))
           :use ((:instance point-set-separable-suff
                            (s1 (sx x c tp)) (s2 (union (fsc1 x c tp))))
                 (:instance point-set-separable-suff
                            (s1 (union tp)) (s2 0))
                 in-x-sx in-sx-tp union-fsc1-in-tp subset-c-union-fsc1 int2-sx-union-fsc1
                 (:instance tpp-union-necc (tp2 0))
                 (:instance tpp-union-necc (tp2 tp)))))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop
              skolem$prop intersection$prop restrict$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              rcompose$prop))

;;;<<End proof by Claude, Opus 6.8 max effort, of compact-hausdorff-is-regular-1.

(defthmz compact-hausdorff-is-regular
  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp))
           (regular tp))
  :hints (("Goal" :in-theory (enable regular)))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop
;;;<<The following :props where added by Claude:>>
              skolem$prop intersection$prop restrict$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              rcompose$prop))
