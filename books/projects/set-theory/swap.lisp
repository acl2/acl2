; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")

; For a relation r, (swap r) is the function mapping each <x,y> \in r to <y,x>.
; Note that for <x,y> \in r, {{x},{x,y}} \in r, so {x,y} \in (union r), so y
; \in (union (union r)), so {y} \in (powerset (union (union r))).  Similarly x
; \in (union (union r)), so {y,x} \in (powerset (union (union r))).  So
; {{y},{y,x}} \in (powerset (powerset (union (union r)))).

(zsub swap (r)
      p ; <<x,y>,<y,x>>
      (prod2 r
             (powerset (powerset (union (union r))))) ; see above
      (and (consp p)
           (in (car p) r)
           (equal (cdr p)
                  (cons (cdr (car p))
                        (car (car p)))))
      )

(defthmz swap$comprehension-better-1
  (implies (and (in (cons x y) r)
                (in wit (cons y x)))
           (subset wit (union (union r))))
; !! Possible AI challenge -- I found the hint manually pretty quickly, though
; at first I tried to give a :use hint for the two necessary instances of
; cons-as-ordered-pair and that didn't work.
  :hints (("Goal" :in-theory (enable cons-as-ordered-pair)))
  :props (zfc swap$prop prod2$prop))

(defthmz swap$comprehension-better
  (implies (case-split (relation-p r))
           (equal (in p (swap r))
                  (and (consp p)
                       (in (car p) r)
                       (equal (cdr p)
                              (cons (cdr (car p))
                                    (car (car p)))))))
  :hints (("Goal" :expand ((SUBSET (cdr P) (POWERSET (UNION (UNION R)))))))
  :props (zfc swap$prop prod2$prop))

(defthmz relation-p-swap
  (implies (case-split (relation-p r))
           (relation-p (swap r)))
  :hints (("Goal" :in-theory (enable relation-p)))
  :props (zfc swap$prop prod2$prop))

(defthmz funp-swap-1
; !! It would be nice to generate this automatically from funp-swap with an
; enhanced version of defthme (which I should then rename, perhaps to
; defthmz*).
  (implies (and (relation-p r)
                (in p1 (swap r))
                (in p2 (swap r))
                (not (equal p1 p2)))
           (not (equal (car p1) (car p2))))
  :props (zfc swap$prop prod2$prop))

(defthmz funp-swap
  (implies (case-split (relation-p r))
           (funp (swap r)))
  :hints (("Goal" :in-theory (enable funp)))
  :props (zfc swap$prop prod2$prop))

(defthmz domain-swap
  (implies (case-split (relation-p r))
           (equal (domain (swap r))
                  r))
;;;<<Begin hints added by Claude, Opus 6.8 max effort, to avoid skip-proofs.>>
  :hints (("Goal"
           :in-theory (e/d (extensionality-rewrite subset
                            swap$comprehension-better in-domain-rewrite)
                           (in-cons-apply))
           :restrict ((in-car-domain-alt
                       ((p (cons (subset-witness r (domain (swap r)))
                                 (cons (cdr (subset-witness r (domain (swap r))))
                                       (car (subset-witness r (domain (swap r))))))))))))
;;;<<End hints added by Claude, Opus 6.8 max effort, to avoid skip-proofs.>>
  :props (zfc swap$prop prod2$prop domain$prop))

(include-book "bijection")

(include-book "utilities/defthme")

(defthme inverse-swap
  (implies (case-split (relation-p r))
           (equal (swap (inverse r))
                  (inverse (swap r))))
  :props (zfc swap$prop prod2$prop inverse$prop))

;;;<<Begin proof by Claude, Opus 6.8 max effort, of bijection-swap.
;;;  Note that Claude moved it to after inverse-swap and added
;;;  the comment below.>>

; (bijection (swap r)) holds because (swap r) is a function (funp-swap) and so
; is its inverse: by inverse-swap, (inverse (swap r)) = (swap (inverse r)),
; which is a function by funp-swap applied to (inverse r).
(defthmz bijection-swap
  (implies (force (relation-p r))
           (bijection (swap r)))
  :hints (("Goal"
           :in-theory (e/d (bijection) (funp-swap))
           :use (funp-swap
                 (:instance funp-swap (r (inverse r))))))
  :props (zfc swap$prop prod2$prop inverse$prop))

;;;<<End proof by Claude, Opus 6.8 max effort, of bijection-swap.>>

(encapsulate
  ()

  (local (include-book "inverse"))

  (defthmz image-swap
    (implies (case-split (relation-p r))
             (equal (image (swap r))
                    (inverse r)))
    :props (zfc swap$prop prod2$prop inverse$prop domain$prop)
    :hints (("Goal"
             :in-theory (e/d (image)
                             (domain-swap domain-inverse))
             :use ((:instance domain-swap
                              (r (inverse r))))))))

