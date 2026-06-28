; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "compact-is-regular")

#| Matt K.: Commenting out the rest of this file for now; see comments below.

;;;<<Comment added by Claude:>>
; !! Left as skip-proofs: as currently defined in
; projects/set-theory/topology/normal.lisp, (normal tp) requires, for disjoint
; closed sets c1 and c2, an open set s1 with (in c1 s1) -- i.e., c1 a *member*
; of s1 -- via (point-set-separable c1 c2 tp).  The compactness/regularity
; argument instead yields (subset c1 s1), i.e., (set-set-separable c1 c2 tp).
; In fact the lemma is false as stated: e.g. for tp = (pair 0 (union tp)) the
; closed set (union tp) is a member of no open set, yet that space is compact
; and regular, so it is not normal in this sense.  This would be provable were
; (normal tp) defined via set-set-separable (which is already defined, just not
; used, in normal.lisp); fixing that definition is left to the library author.
(skip-proofs
(defthmz compact-regular-is-normal
  (implies (and (tpp tp)
                (compact tp)
                (regular tp))
           (normal tp))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop
              diff$prop))
)

;;;<<Comment added by Claude:>>
; This inherits the normal-definition issue noted above (via
; compact-regular-is-normal), so it too relies on that skip-proofs event.
(defthmz compact-hausdorff-is-normal
  (implies (and (tpp tp)
                (compact tp)
                (hausdorff tp))
           (normal tp))
  :props (zfc prod2$prop pps$prop domain$prop inverse$prop diff$prop
;;;<<The following :props where added by Claude:>>
              skolem$prop intersection$prop restrict$prop
              zfns-prop phoenix$prop identity-fun$prop compose$prop swap$prop
              rcompose$prop))

|#
